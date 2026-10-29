/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.FinitePanelGeometry.StablePolytope
public import Mathlib.Analysis.Convex.Intrinsic

/-! # Relative-interior exact matching -/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace Rhone.Algebra.FinitePanelGeometry

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem relativeInterior_eventually_mem_convexHull (p : α → E)
    (q : ℕ → α → E) {m : E}
    (hm : m ∈ intrinsicInterior ℝ (convexHull ℝ (range p)))
    (hqspan : ∀ n x, q n x ∈ affineSpan ℝ (range p))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, m ∈ convexHull ℝ (range (q n)) := by
  classical
  obtain ⟨mH, hmint, hmH⟩ := mem_intrinsicInterior.mp hm
  let H := affineSpan ℝ (convexHull ℝ (range p))
  let : Nonempty H := ⟨mH⟩
  let e := AffineIsometryEquiv.vaddConst ℝ mH
  let φ : H.direction →ᵃⁱ[ℝ] E := H.subtypeₐᵢ.comp e.toAffineIsometry
  let pH (x : α) : H := ⟨p x, subset_affineSpan ℝ _
    (subset_convexHull ℝ (range p) (mem_range_self x))⟩
  let qH (n : ℕ) (x : α) : H := ⟨q n x, by simpa only [H, affineSpan_convexHull] using hqspan n x⟩
  let v (x : α) : H.direction := e.symm (pH x)
  let a (n : ℕ) (x : α) : H.direction := e.symm (qH n x)
  have hφv : ∀ x, φ (v x) = p x := by
    intro x
    change ((e (e.symm (pH x)) : H) : E) = p x
    simp only [e.apply_symm_apply]
    rfl
  have hφa : ∀ n x, φ (a n x) = q n x := by
    intro n x
    change ((e (e.symm (qH n x)) : H) : E) = q n x
    simp only [e.apply_symm_apply]
    rfl
  have himage : φ '' convexHull ℝ (range v) = convexHull ℝ (range p) := by
    rw [← φ.coe_toAffineMap, φ.toAffineMap.image_convexHull]
    congr 1
    rw [← range_comp]
    exact congrArg range (funext hφv)
  have hpre : e ⁻¹' (((↑) : H → E) ⁻¹' convexHull ℝ (range p)) =
      convexHull ℝ (range v) := by
    change φ ⁻¹' convexHull ℝ (range p) = _
    rw [← himage, preimage_image_eq _ φ.injective]
  have hvi : e.symm mH ∈ interior (convexHull ℝ (range v)) := by
    rw [← hpre]
    change e.symm mH ∈ interior (e.toHomeomorph ⁻¹' _ )
    rw [← e.toHomeomorph.preimage_interior]
    change e (e.symm mH) ∈ interior (((↑) : H → E) ⁻¹' convexHull ℝ (range p))
    simpa only [e.apply_symm_apply] using hmint
  have halim : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 (v x)) := by
    intro x
    apply e.symm.continuous.continuousAt.tendsto.comp
    exact tendsto_subtype_rng.mpr (hq x)
  filter_upwards [curve_eventually_exists_positive_exact_match v a hvi halim] with n hn
  obtain ⟨t, w, ht, _, _, hw, hsum, heq⟩ := hn
  have hmem : e.symm mH ∈ convexHull ℝ (range (a n)) := by
    apply convexHull_mono ht
    exact Finset.mem_convexHull'.mpr ⟨w, fun y hy => (hw y hy).le, hsum, heq⟩
  have himagen : φ '' convexHull ℝ (range (a n)) = convexHull ℝ (range (q n)) := by
    rw [← φ.coe_toAffineMap, φ.toAffineMap.image_convexHull]
    congr 1
    rw [← range_comp]
    exact congrArg range (funext (hφa n))
  have hmapped := mem_image_of_mem φ hmem
  rw [himagen] at hmapped
  have htarget : φ (e.symm mH) = m := by
    change ((e (e.symm mH) : H) : E) = m
    simpa only [e.apply_symm_apply] using hmH
  rwa [htarget] at hmapped

theorem relativeInterior_eventually_exists_positive_exact_match (p : α → E)
    (q : ℕ → α → E) {m : E}
    (hm : m ∈ intrinsicInterior ℝ (convexHull ℝ (range p)))
    (hqspan : ∀ n x, q n x ∈ affineSpan ℝ (range p))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = m := by
  filter_upwards [relativeInterior_eventually_mem_convexHull p q hm hqspan hq] with n hn
  exact exists_positive_small_convex_combination hn

end Rhone.Algebra.FinitePanelGeometry
