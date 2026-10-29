/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.FinitePanelGeometry.RelativeInterior
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Interior barycenters of full-support probabilities -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction

namespace Rhone.Algebra.FinitePanelGeometry

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace α] [MeasurableSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem integral_mem_interior_convexHull_of_fullSupport (p : α → E)
    (hp : Continuous p) (hpi : Integrable p μ)
    (hspan : affineSpan ℝ (range p) = ⊤) :
    (∫ x, p x ∂μ) ∈ interior (convexHull ℝ (range p)) := by
  have hint : (interior (convexHull ℝ (range p))).Nonempty := by
    apply (convex_convexHull ℝ (range p)).interior_nonempty_iff_affineSpan_eq_top.mpr
    rwa [affineSpan_convexHull]
  by_contra hout
  obtain ⟨f, hf, hsupport⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ (range p)) hout hint
  have hle : ∀ x, f (p x) ≤ f (∫ x, p x ∂μ) := fun x =>
    hsupport _ (subset_convexHull ℝ (range p) (mem_range_self x))
  have heq : (fun x => f (p x)) =ᵐ[μ] (fun _ => f (∫ x, p x ∂μ)) := by
    apply (integral_eq_iff_of_ae_le (f.integrable_comp hpi) (integrable_const _)
      (Eventually.of_forall hle)).mp
    rw [f.integral_comp_comm hpi, integral_const]
    simp
  have hevery : (fun x => f (p x)) = (fun _ => f (∫ x, p x ∂μ)) :=
    (f.continuous.comp hp).ae_eq_iff_eq μ continuous_const |>.mp heq
  have hmaps : f.toLinearMap.toAffineMap =
      AffineMap.const ℝ E (f (∫ x, p x ∂μ)) := by
    apply AffineMap.ext_on hspan
    rintro _ ⟨x, rfl⟩
    exact congrFun hevery x
  have hzero : f (∫ x, p x ∂μ) = 0 := by
    have h := congrArg (fun g : E →ᵃ[ℝ] ℝ => g 0) hmaps
    simpa using h.symm
  apply hf
  ext y
  have h := congrArg (fun g : E →ᵃ[ℝ] ℝ => g y) hmaps
  simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe,
    AffineMap.const_apply, hzero, zero_apply] using h

theorem fullSupport_eventually_exists_positive_exact_match (p : α → E)
    (hp : Continuous p) (hpi : Integrable p μ)
    (hspan : affineSpan ℝ (range p) = ⊤) (q : ℕ → α → E)
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = ∫ x, p x ∂μ :=
  curve_eventually_exists_positive_exact_match p q
    (integral_mem_interior_convexHull_of_fullSupport p hp hpi hspan) hq

theorem integral_mem_relativeInterior_convexHull_of_fullSupport
    [OpensMeasurableSpace α] (p : α → E) (hp : Continuous p) (hpi : Integrable p μ) :
    (∫ x, p x ∂μ) ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) := by
  classical
  obtain ⟨x₀, _⟩ := (Eventually.of_forall (fun _ : α => True.intro) : ∀ᵐ x ∂μ, True).exists
  let H := affineSpan ℝ (range p)
  let pH (x : α) : H := ⟨p x, subset_affineSpan ℝ (range p) (mem_range_self x)⟩
  let : Nonempty H := ⟨pH x₀⟩
  let : Nonempty (range p) := ⟨⟨p x₀, mem_range_self x₀⟩⟩
  let e := AffineIsometryEquiv.vaddConst ℝ (pH x₀)
  let φ : H.direction →ᵃⁱ[ℝ] E := H.subtypeₐᵢ.comp e.toAffineIsometry
  let v (x : α) : H.direction := e.symm (pH x)
  have hpH : Continuous pH := hp.subtype_mk _
  have hv : Continuous v := e.symm.continuous.comp hpH
  have hcoev : ∀ x, (v x : E) = p x - p x₀ := fun _ => rfl
  have hvi : Integrable v μ := by
    apply (hpi.sub (integrable_const (p x₀))).mono hv.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by change ‖(v x : E)‖ ≤ ‖p x - p x₀‖; rw [hcoev])
  have hpHrange : range pH = ((↑) : H → E) ⁻¹' range p := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_range_self x
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hvrange : range v = e ⁻¹' range pH := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change e (e.symm (pH x)) ∈ range pH
      simp only [e.apply_symm_apply, mem_range_self]
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change e.symm (pH x) = y
      rw [hx, e.symm_apply_apply]
  have hspan : affineSpan ℝ (range v) = ⊤ := by
    rw [hvrange]
    change affineSpan ℝ (e.toAffineEquiv ⁻¹' range pH) = ⊤
    rw [← AffineSubspace.comap_span, hpHrange,
      affineSpan_coe_preimage_eq_top, AffineSubspace.comap_top]
  have hφv : ∀ x, φ (v x) = p x := by
    intro x
    change ((e (e.symm (pH x)) : H) : E) = p x
    simp only [e.apply_symm_apply]
    rfl
  have himage : φ '' convexHull ℝ (range v) = convexHull ℝ (range p) := by
    rw [← φ.coe_toAffineMap, φ.toAffineMap.image_convexHull]
    congr 1
    rw [← range_comp]
    exact congrArg range (funext hφv)
  have htarget : φ (∫ x, v x ∂μ) = ∫ x, p x ∂μ := by
    change H.direction.subtypeL (∫ x, v x ∂μ) + p x₀ = ∫ x, p x ∂μ
    rw [← H.direction.subtypeL.integral_comp_comm hvi]
    change (∫ x, (v x : E) ∂μ) + p x₀ = ∫ x, p x ∂μ
    simp only [hcoev, integral_sub hpi (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_add_cancel]
  have hint := integral_mem_interior_convexHull_of_fullSupport v hv hvi hspan
  have hi := interior_subset_intrinsicInterior (𝕜 := ℝ) hint
  have him := mem_image_of_mem φ hi
  rw [← φ.intrinsicInterior_image, himage, htarget] at him
  exact him

theorem fullSupport_relative_eventually_exists_positive_exact_match
    [OpensMeasurableSpace α] (p : α → E) (hp : Continuous p) (hpi : Integrable p μ)
    (q : ℕ → α → E) (hqspan : ∀ n x, q n x ∈ affineSpan ℝ (range p))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = ∫ x, p x ∂μ :=
  relativeInterior_eventually_exists_positive_exact_match p q
    (integral_mem_relativeInterior_convexHull_of_fullSupport p hp hpi) hqspan hq

theorem boundedContinuous_fullSupport_eventually_exists_positive_exact_match
    [OpensMeasurableSpace α] (p : α →ᵇ E) (q : ℕ → α → E)
    (hqspan : ∀ n x, q n x ∈ affineSpan ℝ (range p))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = ∫ x, p x ∂μ := by
  borelize E
  exact fullSupport_relative_eventually_exists_positive_exact_match p p.continuous
    (p.integrable μ) q hqspan hq

theorem probability_integral_mem_affineSpan {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (p : β → E) (hpi : Integrable p ν) :
    (∫ x, p x ∂ν) ∈ affineSpan ℝ (range p) := by
  apply (affineSpan ℝ (range p)).convex.integral_mem
    (affineSpan ℝ (range p)).closed_of_finiteDimensional _ hpi
  exact Eventually.of_forall (fun x => subset_affineSpan ℝ (range p) (mem_range_self x))

theorem boundedContinuous_expectation_approximants_exact_match
    [OpensMeasurableSpace α] (p : α →ᵇ E) (ν : ℕ → α → Measure α)
    [∀ n x, IsProbabilityMeasure (ν n x)]
    (hν : ∀ x, Tendsto (fun n => ∫ y, p y ∂ν n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ),
      (↑t : Set E) ⊆ range (fun x => ∫ y, p y ∂ν n x) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = ∫ x, p x ∂μ := by
  borelize E
  apply boundedContinuous_fullSupport_eventually_exists_positive_exact_match p
    (fun n x => ∫ y, p y ∂ν n x) _ hν
  intro n x
  exact probability_integral_mem_affineSpan (ν n x) p (p.integrable (ν n x))

end Rhone.Algebra.FinitePanelGeometry
