/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.TajimaDCovariance

/-!
# Tajima's D

Source: tajima1989, p. 588, eq. (38); watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thm
1.22. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory

/-- Source: tajima1989, p. 588, eq. (35)–(37). -/
noncomputable def tajimaVarianceEstimate (n : ℕ) (S : ℝ) : ℝ :=
  (tajimaE1 n : ℝ) * S + (tajimaE2 n : ℝ) * S * (S - 1)

/-- Source: tajima1989, p. 588, eq. (38). -/
noncomputable def tajimaD (n : ℕ) (π S : ℝ) : ℝ :=
  (π - S / (tajimaA1 n : ℝ)) / Real.sqrt (tajimaVarianceEstimate n S)

/-- Source: tajima1989, p. 588, eq. (38). -/
noncomputable def markedKingmanTajimaD (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  tajimaD n (Coalescent.markedKingmanPi n x) (markedKingmanSegregating n x)

theorem tajimaD_of_varianceEstimate_nonpos (n : ℕ) (π S : ℝ)
    (h : tajimaVarianceEstimate n S ≤ 0) : tajimaD n π S = 0 := by
  unfold tajimaD
  rw [Real.sqrt_eq_zero_of_nonpos h, div_zero]

theorem tajimaD_zero_segregating (n : ℕ) (π : ℝ) : tajimaD n π 0 = 0 := by
  apply tajimaD_of_varianceEstimate_nonpos
  simp [tajimaVarianceEstimate]

theorem tajimaD_two (π S : ℝ) : tajimaD 2 π S = 0 := by
  apply tajimaD_of_varianceEstimate_nonpos
  simp [tajimaVarianceEstimate, tajimaE1_two, tajimaE2_two]

theorem tajimaD_three (π S : ℝ) : tajimaD 3 π S = 0 := by
  apply tajimaD_of_varianceEstimate_nonpos
  simp [tajimaVarianceEstimate, tajimaE1_three, tajimaE2_three]

theorem markedKingmanTajimaVarianceEstimate_eq (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    markedKingmanTajimaVarianceEstimate n x =
      tajimaVarianceEstimate n (markedKingmanSegregating n x) := rfl

theorem markedKingmanTajimaD_eq (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    markedKingmanTajimaD n x = markedKingmanTajimaNumerator n x /
      Real.sqrt (markedKingmanTajimaVarianceEstimate n x) := rfl

theorem measurable_tajimaD (n : ℕ) : Measurable (fun p : ℝ × ℝ => tajimaD n p.1 p.2) := by
  unfold tajimaD tajimaVarianceEstimate
  fun_prop

theorem measurable_markedKingmanTajimaD (n : ℕ) : Measurable (markedKingmanTajimaD n) :=
  (measurable_tajimaD n).comp
    ((Coalescent.measurable_markedKingmanPi n).prodMk (measurable_markedKingmanSegregating n))

end Rhone.Statistics
