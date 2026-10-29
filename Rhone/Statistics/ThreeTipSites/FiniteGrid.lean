/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeTipSites.LaplaceSpan

/-! # Finite-grid Laplace uniqueness for three-tip site transitions and masses -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.ThreeTipSites

open Identifiability.EqualRatesMutation

lemma grid_sum {ι : Type*} {c : ℝ} {a b : ℕ} (s : Finset ι)
    (f : ι → (ℝ × ℝ) → ℝ) (hf : ∀ i ∈ s, f i ∈ grid c a b) :
    (fun t => ∑ i ∈ s, f i t) ∈ grid c a b := by
  convert (grid c a b).sum_mem hf using 1
  ext t
  simp only [Finset.sum_apply]

lemma transition_grid {K : ℕ} (k : ℝ) (τ : (ℝ × ℝ) → ℝ)
    {a b : ℕ} (hτ : (fun t => Real.exp (-(k / 2) * τ t)) ∈ grid (k / 2) a b)
    (r z : Fin K) : (fun t => transition K k (τ t) r z) ∈ grid (k / 2) a b := by
  have h := (grid (k / 2) a b).add_mem
    ((grid (k / 2) a b).smul_mem ((1 : MutationMatrix K) r z) hτ)
    ((grid (k / 2) a b).smul_mem (uniform K r z)
      ((grid (k / 2) a b).sub_mem (one_mem (k / 2) a b) hτ))
  convert h using 1
  ext t
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
  ring

lemma transition_U_grid {K : ℕ} (k : ℝ) (r z : Fin K) :
    (fun t : ℝ × ℝ => transition K k t.1 r z) ∈ grid (k / 2) 1 0 := by
  apply transition_grid k Prod.fst
  convert mode_mem (k / 2) (Nat.le_refl 1) (Nat.le_refl 0) using 1
  ext t
  simp [mode]

lemma transition_V_grid {K : ℕ} (k : ℝ) (r z : Fin K) :
    (fun t : ℝ × ℝ => transition K k t.2 r z) ∈ grid (k / 2) 0 1 := by
  apply transition_grid k Prod.snd
  convert mode_mem (k / 2) (Nat.le_refl 0) (Nat.le_refl 1) using 1
  ext t
  simp [mode]

lemma transition_UV_grid {K : ℕ} (k : ℝ) (r z : Fin K) :
    (fun t : ℝ × ℝ => transition K k (t.1 + t.2) r z) ∈ grid (k / 2) 1 1 := by
  apply transition_grid k (fun t => t.1 + t.2)
  convert mode_mem (k / 2) (Nat.le_refl 1) (Nat.le_refl 1) using 1
  ext t
  simp [mode]

theorem site_grid (K : ℕ) (π : Fin K → ℝ) (k : ℝ) (x : Triple K) :
    (fun t => site K π k t x) ∈ grid (k / 2) 3 2 := by
  apply grid_sum
  intro r _
  apply grid_sum
  intro z _
  have h := grid_mul (grid_mul (grid_mul (transition_V_grid k r z)
    (transition_U_grid k z x.1)) (transition_U_grid k z x.2.1))
    (transition_UV_grid k r x.2.2)
  have hs := (grid (k / 2) 3 2).smul_mem (π r) h
  convert hs using 1
  ext t
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

lemma fixedTopology_grid {K L : ℕ} (π : Roots K L) (k : ℝ)
    (q : Fin 3) (x : Panel K L) :
    (fun t => fixedTopology π k t q x) ∈ grid (k / 2) (3 * L) (2 * L) := by
  have h := grid_prod Finset.univ
    (fun s t => site K (π.weight s) k t (orientation K q (x s)))
    (fun s _ => site_grid K (π.weight s) k (orientation K q (x s)))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  convert h using 1
  ext t
  simp only [fixedTopology, Finset.prod_apply]

theorem conditional_grid {K L : ℕ} (π : Roots K L) (k : ℝ) (x : Panel K L) :
    (fun t => conditional π k t x) ∈ grid (k / 2) (3 * L) (2 * L) := by
  exact (grid (k / 2) (3 * L) (2 * L)).smul_mem (1 / 3 : ℝ)
    (grid_sum Finset.univ (fun q t => fixedTopology π k t q x)
      (fun q _ => fixedTopology_grid π k q x))

theorem mass_eq_of_laplace_grid {K L : ℕ} (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ ν : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hm : ∀ i ≤ 3 * L, ∀ j ≤ 2 * L,
      ∫ t, mode (k / 2) i j t ∂μ = ∫ t, mode (k / 2) i j t ∂ν)
    (x : Panel K L) : mass π k μ x = mass π k ν x := by
  exact integral_eq_of_grid (by positivity) hμ hν hm (conditional_grid π k x)

theorem law_eq_of_laplace_grid {K L : ℕ} (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ ν : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hm : ∀ i ≤ 3 * L, ∀ j ≤ 2 * L,
      ∫ t, mode (k / 2) i j t ∂μ = ∫ t, mode (k / 2) i j t ∂ν) :
    law π k μ = law π k ν := by
  unfold law
  congr 1
  funext x
  rw [mass_eq_of_laplace_grid π hk hμ hν hm x]

end Rhone.Statistics.ThreeTipSites
