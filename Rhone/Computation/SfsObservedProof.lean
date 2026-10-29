/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsNull
public import Rhone.Computation.SfsProof
public import Rhone.Statistics.WattersonMarkedVarianceEstimate

/-!
# Executable observed Watterson summaries equal the marked-law statistics

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thm 1.22; tajima1989, p. 585, eq.
(1)–(5). -/

@[expose] public section
namespace Rhone.Computation.SfsNull
open Coalescent Probability Statistics

/-- Source: watterson1975, p. 258, eq. (1.5a); durrett2008, Thm 1.22. -/
theorem observedWattersonVariance_eq_estimate (n : Nat) (S : Rat)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ))
    (hS : (S : ℝ) = markedKingmanSegregating n x) :
    ((observedWattersonVariance n S : Rat) : ℝ) =
      markedKingmanWattersonVarianceEstimate n x := by
  unfold markedKingmanWattersonVarianceEstimate
  rw [← hS]
  simp [observedWattersonVariance, Sfs.a1_eq, Sfs.a2_eq]

/-- Source: watterson1975, sec. 1.1, p. 257. -/
theorem cast_count_eq_markedKingmanSegregating (n : Nat)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    ((((∑ b, x.2 b : ℕ) : Rat) : Rat) : ℝ) = markedKingmanSegregating n x := by
  simp [markedKingmanSegregating]

/-- Source: watterson1975, p. 258, eq. (1.5a); durrett2008, Thm 1.22. -/
theorem observedWattersonVariance_count_eq_estimate (n : Nat)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    ((observedWattersonVariance n ((∑ b, x.2 b : ℕ) : Rat) : Rat) : ℝ) =
      markedKingmanWattersonVarianceEstimate n x :=
  observedWattersonVariance_eq_estimate n _ x (cast_count_eq_markedKingmanSegregating n x)

/-- Source: watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.22. -/
theorem watterson_count_eq_markedKingmanWatterson (n : Nat)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    ((Sfs.watterson n ((∑ b, x.2 b : ℕ) : Rat) : Rat) : ℝ) =
      markedKingmanWatterson n x := by
  simp [Sfs.watterson, Sfs.a1_eq, markedKingmanWatterson, markedKingmanSegregating]

end Rhone.Computation.SfsNull
