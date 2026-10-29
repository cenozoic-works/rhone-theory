/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkovMass

/-! # Finite-interval absolutely continuous Markov row evolutions -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι]

theorem integrable_row_solution_nonneg_endpoint (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, t ∈ uIcc a b → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b)
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hzero : ∀ i, 0 ≤ v a i) : ∀ i, 0 ≤ v b i := by
  classical
  let E : ℝ → ℝ := fun t => ∑ i, (min (v t i) 0)^2
  let Edot : ℝ → ℝ := fun t => ∑ j, 2 * min (v t j) 0 * (∑ i, v t i * Q t i j)
  let C : ℝ → ℝ := fun t => 2 * ∑ j, ∑ i, |Q t i j|
  let H : ℝ → ℝ := fun t => -(∫ s in a..t, C s)
  have hCi : LocallyIntegrable C volume := metzler_energy_coefficient_locallyIntegrable hQi
  have hEzero : E a = 0 := by simp [E, hzero]
  have hEac : AbsolutelyContinuousOnInterval E a b :=
    ac_finset_sum Finset.univ (fun j _ => ac_sq_min_zero (hv j))
  have hHac : AbsolutelyContinuousOnInterval H a b := by
    exact ((LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hCi a
      b).absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg
  have hEd : ∀ᵐ s, s ∈ uIcc a b → HasDerivAt E (Edot s) s := by
    filter_upwards [he] with s hs hmem
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [Function.comp_def] using
      (hasDerivAt_sq_min_zero (v s j)).comp s (hs hmem j)
  have hHd : ∀ᵐ s, s ∈ uIcc a b → HasDerivAt H (-C s) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hCi] with s hs _
    exact (hs a).neg
  have hb : ∀ᵐ s, s ∈ uIcc a b → Edot s ≤ -(-C s) * E s := by
    filter_upwards [hQ] with s hs hmem
    simpa only [Edot, C, E, neg_neg] using
      metzler_negative_energy_bound (Q s) (v s) (hs hmem)
  have hle := ac_comparison_upper E Edot H (fun s => -C s) a b hab hEac hHac hEd hHd hb
  rw [hEzero, zero_mul] at hle
  intro i
  have hi : (min (v b i) 0)^2 ≤ E b :=
    Finset.single_le_sum (fun j _ => sq_nonneg (min (v b j) 0)) (Finset.mem_univ i)
  have hz : min (v b i) 0 = 0 := by nlinarith [hi.trans hle]
  simpa only [hz] using min_le_left (v b i) 0

theorem integrable_row_solution_nonneg_interval (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, t ∈ uIcc a b → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b)
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hzero : ∀ i, 0 ≤ v a i) :
    ∀ t, t ∈ uIcc a b → ∀ i, 0 ≤ v t i := by
  intro t ht
  have hat : a ≤ t := (by simpa only [uIcc_of_le hab, mem_Icc] using ht : a ≤ t ∧ t ≤ b).1
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc (by simp) ht
  apply integrable_row_solution_nonneg_endpoint Q v hat hQi
  · filter_upwards [hQ] with s hs hmem
    exact hs (hsub hmem)
  · exact fun i => (hv i).mono hsub
  · filter_upwards [he] with s hs hmem
    exact hs (hsub hmem)
  · exact hzero

theorem finiteRowODE_mass_ae_hasDerivAt_interval (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ}
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) :
    ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun s => ∑ i, v s i) (∑ i, v t i * ∑ j, Q t i j) t := by
  filter_upwards [he] with t ht hmem
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht hmem j)
  rw [Finset.sum_comm] at hsum
  simpa only [Finset.mul_sum] using hsum

theorem integrable_finiteRowODE_mass_antitoneOn_interval (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ}
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b)
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, t ∈ uIcc a b → ∀ i, 0 ≤ v t i)
    (hrows : ∀ᵐ t, t ∈ uIcc a b → ∀ i, ∑ j, Q t i j ≤ 0) :
    AntitoneOn (fun t => ∑ i, v t i) (uIcc a b) := by
  apply ac_antitoneOn_of_ae_hasDerivAt_nonpos (finiteRowODE_mass_ac hv)
    (finiteRowODE_mass_ae_hasDerivAt_interval Q v he)
  filter_upwards [hrows] with t ht hmem
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hnonneg t hmem i) (ht hmem i)

theorem integrable_finiteRowODE_mass_le_endpoint (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b)
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, t ∈ uIcc a b → ∀ i, 0 ≤ v t i)
    (hrows : ∀ᵐ t, t ∈ uIcc a b → ∀ i, ∑ j, Q t i j ≤ 0) :
    (∑ i, v b i) ≤ ∑ i, v a i :=
  integrable_finiteRowODE_mass_antitoneOn_interval Q v hv he hnonneg hrows
    (by simp) (by simp) hab

theorem integrable_finiteRowODE_mass_eq_endpoint (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) {a b : ℝ}
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b)
    (he : ∀ᵐ t, t ∈ uIcc a b → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hrows : ∀ᵐ t, t ∈ uIcc a b → ∀ i, ∑ j, Q t i j = 0) :
    (∑ i, v b i) = ∑ i, v a i := by
  have hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (fun s => ∑ i, v s i) 0 t := by
    filter_upwards [finiteRowODE_mass_ae_hasDerivAt_interval Q v he, hrows]
      with t ht hrow hmem
    simpa only [hrow hmem, mul_zero, Finset.sum_const_zero] using ht hmem
  obtain ⟨C, hC⟩ := (finiteRowODE_mass_ac hv).const_of_ae_hasDerivAt_zero hd
  exact (hC b (by simp)).trans (hC a (by simp)).symm

end Rhone.Statistics.Identifiability
