/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalChain.Cleared

/-! # Cleared diagonal chain at `k = 2` and `k = 3` in closed form -/

@[expose] public section

namespace Rhone.Probability.DiagonalChain

open LinearAlgebra.Tridiag Analysis.RecombinationExpansion LinearAlgebra.RecombinationExpansion
    Analysis.DenominatorEquation
open Analysis.RareAlleleHierarchy RareAlleleHierarchy

section Small

variable {S : Type*} [CommRing S] (θ ρ : S)

theorem diagSource_three (w : ℕ → S) : diagSource w 3 = 6 * w 2 := by
  rw [diagSource]
  norm_num

theorem adjD_two_zero_two : adjD 2 θ ρ 0 2 = 16 := by
  rw [adjD, usmaniEntry_T_of_le 2 2 θ 0 ρ (by omega : (0 : ℕ) ≤ 2)]
  norm_num [LinearAlgebra.Tridiag.cont, Qc_self, Finset.prod_Ico_succ_top]

theorem adjD_two_one_two : adjD 2 θ ρ 1 2 = 24 + 4 * θ := by
  rw [adjD, usmaniEntry_T_of_le 2 2 θ 0 ρ (by omega : (1 : ℕ) ≤ 2)]
  norm_num [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef, Qc_self,
      Finset.prod_Ico_succ_top]
  ring

theorem adjD_two_two_two : adjD 2 θ ρ 2 2 = (6 + 2 * θ + ρ) * (12 + 2 * θ) - 8 * ρ := by
  rw [adjD, usmaniEntry_T_of_le 2 2 θ 0 ρ (le_refl 2)]
  norm_num [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef, LinearAlgebra.Tridiag.bcoef,
      LinearAlgebra.Tridiag.ccoef, Qc_self]
  ring

theorem clearedChain_two_eq : clearedChain θ ρ 2 = clearedStep 2 θ ρ varthetaOne := rfl

theorem clearedChain_two_one : clearedChain θ ρ 2 1 = 2 * (24 + 4 * θ) := by
  rw [clearedChain_two_eq, clearedStep_eq_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, diagSource_zero, diagSource_one,
    diagSource_two, varthetaOne_one, adjD_two_one_two]
  ring

theorem clearedChain_two_two : clearedChain θ ρ 2 2 = 2 * ((6 + 2 * θ + ρ) * (12 + 2 * θ)
    - 8 * ρ) := by
  rw [clearedChain_two_eq, clearedStep_eq_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, diagSource_zero, diagSource_one,
    diagSource_two, varthetaOne_one, adjD_two_two_two]
  ring

theorem W_two : W 2 θ ρ = 32 := by
  rw [W, clearedChain_two_eq, clearedStep_eq_range, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, diagSource_zero,
    diagSource_one, diagSource_two, varthetaOne_one, adjD_two_zero_two]
  ring

theorem Qc_three_trail :
    Qc (dcoef S 3 3 θ 0 ρ) (bcoef S 3 3) (ccoef S ρ) (min 3 3 + 1) 3 = 6 + θ * 3 + ρ * 3 := by
  rw [Qc_of_le _ _ _ (by norm_num : (3 : ℕ) ≤ min 3 3 + 1),
    show min 3 3 + 1 - 3 = 1 from by norm_num, det_tridFrom_one]
  norm_num [LinearAlgebra.Tridiag.dcoef]

theorem adjD_three_zero_two : adjD 3 θ ρ 0 2 = 144 * (6 + θ * 3 + ρ * 3) := by
  rw [adjD, usmaniEntry_T_of_le 3 3 θ 0 ρ (by omega : (0 : ℕ) ≤ 2), Qc_three_trail]
  norm_num [LinearAlgebra.Tridiag.cont, Finset.prod_Ico_succ_top]

theorem adjD_three_zero_three : adjD 3 θ ρ 0 3 = 288 := by
  rw [adjD, usmaniEntry_T_of_le 3 3 θ 0 ρ (by omega : (0 : ℕ) ≤ 3)]
  norm_num [LinearAlgebra.Tridiag.cont, Qc_self, Finset.prod_Ico_succ_top]

theorem clearedChain_three_eq :
    clearedChain θ ρ 3 = clearedStep 3 θ ρ (clearedChain θ ρ 2) := rfl

theorem W_three : W 3 θ ρ = 6912 * (2 * (θ + 4) * ρ + (3 * θ + 8) * (θ + 6)) := by
  rw [W, clearedChain_three_eq, clearedStep_eq_range, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    diagSource_zero, diagSource_one, diagSource_two, diagSource_three,
    clearedChain_two_one, clearedChain_two_two, adjD_three_zero_two, adjD_three_zero_three]
  ring

theorem W_three_at_zero : W 3 (0 : S) ρ = 55296 * (ρ + 6) := by
  rw [W_three]
  ring

theorem ED_three_at_zero (r : S) :
    ED 3 (0 : S) r = 72 * r ^ 3 + 2664 * r ^ 2 + 23184 * r + 43200 := by
  rw [ED, E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef, LinearAlgebra.Tridiag.bcoef,
      LinearAlgebra.Tridiag.ccoef]
  ring

end Small

theorem ED_three_at_minus_six : ED 3 (0 : ℤ) (-6) = -15552 := by
  rw [ED_three_at_zero]
  norm_num

end Rhone.Probability.DiagonalChain
