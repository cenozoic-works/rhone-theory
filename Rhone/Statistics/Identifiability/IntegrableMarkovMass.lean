/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovBasic
public import Rhone.Statistics.Identifiability.ACComparisonBounds

/-! # Total mass of absolutely continuous finite row evolutions -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι]

theorem finiteRowODE_mass_ac {v : ℝ → ι → ℝ} {a b : ℝ}
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) a b) :
    AbsolutelyContinuousOnInterval (fun s => ∑ i, v s i) a b :=
  ac_finset_sum Finset.univ (fun i _ => hv i)

theorem finiteRowODE_mass_ae_hasDerivAt (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) :
    ∀ᵐ t, 0 ≤ t →
      HasDerivAt (fun s => ∑ i, v s i) (∑ i, v t i * ∑ j, Q t i j) t := by
  filter_upwards [he] with t ht ht0
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht ht0 j)
  rw [Finset.sum_comm] at hsum
  simpa only [Finset.mul_sum] using hsum

theorem integrable_finiteRowODE_mass_antitoneOn (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) :
    AntitoneOn (fun t => ∑ i, v t i) (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  have hac := finiteRowODE_mass_ac (hv b hb)
  have hanti : AntitoneOn (fun t => ∑ i, v t i) (uIcc 0 b) := by
    apply ac_antitoneOn_of_ae_hasDerivAt_nonpos hac
      (fDot := fun t => ∑ i, v t i * ∑ j, Q t i j)
    · filter_upwards [finiteRowODE_mass_ae_hasDerivAt Q v he] with t ht hmem
      exact ht ((by simpa only [uIcc_of_le hb, mem_Icc] using hmem : 0 ≤ t ∧ t ≤ b).1)
    · filter_upwards [hrows] with t ht hmem
      have ht0 : 0 ≤ t :=
        (by simpa only [uIcc_of_le hb, mem_Icc] using hmem : 0 ≤ t ∧ t ≤ b).1
      exact Finset.sum_nonpos fun i _ =>
        mul_nonpos_of_nonneg_of_nonpos (hnonneg t ht0 i) (ht ht0 i)
  apply hanti _ (by simp) hab
  simpa only [uIcc_of_le hb, mem_Icc] using (show 0 ≤ a ∧ a ≤ b from ⟨ha, hab⟩)

theorem integrable_finiteRowODE_mass_le_initial (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v t i) ≤ ∑ i, v 0 i :=
  integrable_finiteRowODE_mass_antitoneOn Q v hv he hnonneg hrows (by simp) ht ht

theorem integrable_finiteRowODE_mass_eq_initial (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v t i) = ∑ i, v 0 i := by
  have hac := finiteRowODE_mass_ac (hv t ht)
  have hd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt (fun u => ∑ i, v u i) 0 s := by
    filter_upwards [finiteRowODE_mass_ae_hasDerivAt Q v he, hrows] with s hs hrow hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    simpa only [hrow hs0, mul_zero, Finset.sum_const_zero] using hs hs0
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hd
  exact (hC t (by simp)).trans (hC 0 (by simp)).symm

theorem integrable_finiteRowODE_mass_clock_lower_bound
    (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ) (c : ℝ → ℝ)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hc : LocallyIntegrable c volume)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v 0 i) * Real.exp (-(∫ s in (0 : ℝ)..t, c s)) ≤ ∑ i, v t i := by
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, c s
  have hHac : AbsolutelyContinuousOnInterval H 0 t :=
    (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hc 0
      t).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hd : ∀ᵐ s, s ∈ uIcc 0 t →
      HasDerivAt (fun u => ∑ i, v u i) (∑ i, v s i * ∑ j, Q s i j) s := by
    filter_upwards [finiteRowODE_mass_ae_hasDerivAt Q v he] with s hs hmem
    exact hs ((by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1)
  have hHd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt H (c s) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hc] with s hs _
    exact hs 0
  have hbound : ∀ᵐ s, s ∈ uIcc 0 t →
      -c s * (∑ i, v s i) ≤ ∑ i, v s i * ∑ j, Q s i j := by
    filter_upwards [hrows] with s hs hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hs hs0 i) (hnonneg s hs0 i)
  have h := ac_comparison_lower (fun s => ∑ i, v s i)
    (fun s => ∑ i, v s i * ∑ j, Q s i j) H c 0 t ht
    (finiteRowODE_mass_ac (hv t ht)) hHac hd hHd hbound
  simpa only [H, intervalIntegral.integral_same, zero_sub] using h

theorem integrable_finiteRowODE_mass_pos
    (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ) (c : ℝ → ℝ)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hc : LocallyIntegrable c volume)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    (hzero : 0 < ∑ i, v 0 i) {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ i, v t i :=
  (mul_pos hzero (Real.exp_pos _)).trans_le
    (integrable_finiteRowODE_mass_clock_lower_bound Q v c hv he hnonneg hc hrows ht)

end Rhone.Statistics.Identifiability
