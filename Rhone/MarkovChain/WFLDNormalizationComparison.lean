/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDExpectedRSq

/-!
# Comparison of the stationary expected `r²` with the ratio of LD moments

Source: mcvean2002, eq. (2), p. 987. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset

/-- Source: mcvean2002, eq. (1), p. 987. -/
theorem count_rsq_times_heterozygosity (M : ℕ) (hM : 0 < M)
    (a : Rhone.MarkovChain.AlleleCounts M 4) :
    Dynamics.Gametes.rSq (countGametes M a).pA (countGametes M a).pB (countGametes M a).D *
      momentStatistics (countGametes M a) 0 = momentStatistics (countGametes M a) 2 := by
  let g := countGametes M a
  have hg := count_gametes_isDist M hM a
  change Dynamics.Gametes.rSq g.pA g.pB g.D * (g.pA*(1-g.pA)*g.pB*(1-g.pB)) = g.D^2
  by_cases hh : g.pA*(1-g.pA)*g.pB*(1-g.pB) = 0
  · have hp := Dynamics.Gametes.pA'_eq hg.total_eq
    have hq := Dynamics.Gametes.pB'_eq hg.total_eq
    have hz : (g.x11+g.x12)*(g.x21+g.x22)*(g.x11+g.x21)*(g.x12+g.x22) = 0 := by
      rw [← hp, ← hq] at hh
      exact hh
    have hd : g.D = 0 := by
      rcases mul_eq_zero.mp hz with hz | hz
      · rcases mul_eq_zero.mp hz with hz | hz
        · rcases mul_eq_zero.mp hz with hz | hz
          · have h11 : g.x11=0 := by linarith [hg.x11_nonneg,hg.x12_nonneg]
            have h12 : g.x12=0 := by linarith [hg.x11_nonneg,hg.x12_nonneg]
            simp [Dynamics.Gametes.D,h11,h12]
          · have h21 : g.x21=0 := by linarith [hg.x21_nonneg,hg.x22_nonneg]
            have h22 : g.x22=0 := by linarith [hg.x21_nonneg,hg.x22_nonneg]
            simp [Dynamics.Gametes.D,h21,h22]
        · have h11 : g.x11=0 := by linarith [hg.x11_nonneg,hg.x21_nonneg]
          have h21 : g.x21=0 := by linarith [hg.x11_nonneg,hg.x21_nonneg]
          simp [Dynamics.Gametes.D,h11,h21]
      · have h12 : g.x12=0 := by linarith [hg.x12_nonneg,hg.x22_nonneg]
        have h22 : g.x22=0 := by linarith [hg.x12_nonneg,hg.x22_nonneg]
        simp [Dynamics.Gametes.D,h12,h22]
    simp [Dynamics.Gametes.rSq,hh,hd]
  · exact div_mul_cancel₀ _ hh

theorem ld_expected_rsq_sigma_comparison (M : ℕ) (hM : 2 ≤ M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    |ldExpectedRSq M π - ldStationaryMoments M π 2/ldStationaryMoments M π 0| ≤
      (∑ a, π a*|momentStatistics (countGametes M a) 0-ldStationaryMoments M π 0|)/
        ldStationaryMoments M π 0 := by
  have hM0 : 0 < M := by omega
  let H := ldStationaryMoments M π 0
  let r := fun a => Dynamics.Gametes.rSq (countGametes M a).pA (countGametes M a).pB
      (countGametes M a).D
  let h := fun a => momentStatistics (countGametes M a) 0
  have hH : 0 < H := ld_stationary_heterozygosity_pos M hM c u hc0 hc1 hu0 hu1 π hπ hnorm hstat
  have hr0 (a) : 0 ≤ r a := Dynamics.Gametes.rSq_nonneg (count_gametes_isDist M hM0 a)
  have hr1 (a) : r a ≤ 1 := Dynamics.Gametes.rSq_le_one (count_gametes_isDist M hM0 a)
  have he : ldExpectedRSq M π-ldStationaryMoments M π 2/H =
      (∑ a, π a*r a*(H-h a))/H := by
    apply (eq_div_iff hH.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hH.ne']
    unfold ldExpectedRSq ldStationaryMoments
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    have hh := count_rsq_times_heterozygosity M hM0 a
    dsimp only [r,h]
    rw [← hh]
    ring
  change |ldExpectedRSq M π-ldStationaryMoments M π 2/H| ≤ (∑ a, π a*|h a-H|)/H
  rw [he, abs_div, abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  calc
    |∑ a, π a*r a*(H-h a)| ≤ ∑ a, |π a*r a*(H-h a)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, π a*|h a-H| := by
      apply sum_le_sum
      intro a _
      rw [abs_mul, abs_mul, abs_of_nonneg (hπ a), abs_of_nonneg (hr0 a), abs_sub_comm]
      have hh := mul_le_mul_of_nonneg_right (hr1 a) (abs_nonneg (h a-H))
      have hh' := mul_le_mul_of_nonneg_left hh (hπ a)
      nlinarith only [hh']

end Rhone.MarkovChain.WFAllocationLD
