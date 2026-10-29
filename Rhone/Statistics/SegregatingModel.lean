/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaVarianceModel
public import Rhone.Statistics.Watterson

/-!
# Total mutation counts and estimators on the marked Kingman law

Source: watterson1975, sec. 1.2, p. 257; durrett2008, Thm 1.22; tajima1989, p. 585, eq. (1)–(5). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory Finset

noncomputable def markedKingmanSegregating (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  ∑ b : Coalescent.KingmanMutationBranch n, (x.2 b : ℝ)

noncomputable def markedKingmanWatterson (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  markedKingmanSegregating n x / (tajimaA1 n : ℝ)

noncomputable def markedKingmanTajimaNumerator (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  Coalescent.markedKingmanPi n x - markedKingmanWatterson n x

noncomputable def markedKingmanTajimaVarianceEstimate (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  (tajimaE1 n : ℝ) * markedKingmanSegregating n x +
    (tajimaE2 n : ℝ) * markedKingmanSegregating n x *
      (markedKingmanSegregating n x - 1)

theorem measurable_markedKingmanSegregating (n : ℕ) :
    Measurable (markedKingmanSegregating n) := by
  unfold markedKingmanSegregating
  apply Finset.measurable_sum
  intro b _
  fun_prop

theorem markedKingmanSegregating_nonneg (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    0 ≤ markedKingmanSegregating n x := by
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

end Rhone.Statistics
