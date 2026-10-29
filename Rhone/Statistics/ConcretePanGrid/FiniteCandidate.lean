/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePanGrid.CandidateNumbers
public import Rhone.Statistics.ConcretePanGrid.RationalBound
public import Rhone.Statistics.ConcreteBettingFeatures.SourceBridge

/-! # Finite-alphabet obstruction for the source law against an abstract finite comparator -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcretePanGrid
open ConcreteBettingFeatures ConcretePatternMoments ThreeTipSites
open DependenceBudget DependentPairedTest FiniteObservationRate

theorem full_class_sum (f : Fin 14 → ℝ) :
    (∑ x : Panel 4 3, f (rowClass (rowOf x))) =
      ∑ c : Fin 14, (sourceClassCount c : ℝ) * f c := by
  rw [category_panel_sum (fun r => f (rowClass r))]
  simp_rw [← row_multiplicity_real]
  rw [weighted_class_sum f]
  apply Finset.sum_congr rfl
  intro c _
  have hc : (∑ r : Row with rowClass r = c, (rowMultiplicity r : ℝ)) = sourceClassCount c := by
    exact_mod_cast source_class_counts c
  rw [hc]

def candidateLaw : Law (Panel 4 3) where
  mass x := candidateClassMass (rowClass (rowOf x))
  nonneg _x := (candidate_class_positive _).le
  total := (full_class_sum candidateClassMass).trans candidate_normalization

theorem source_candidate_rational_bound :
    (∑ x : Panel 4 3, (sourceLaw.mass x - candidateLaw.mass x) ^ 2 /
      (sourceLaw.mass x + candidateLaw.mass x)) < 9 / (16 * 38318671) := by
  simp only [source_mass_class, candidateLaw]
  rw [full_class_sum (fun c => (sourceClassMass c - candidateClassMass c) ^ 2 /
    (sourceClassMass c + candidateClassMass c))]
  apply lt_of_le_of_lt _ candidate_budget
  apply Finset.sum_le_sum
  intro c _
  simpa only [mul_div_assoc] using candidate_term_bound c

theorem source_finite_candidate_obstruction {N : ℕ} (hN : N ≤ 38318671)
    (φ : (Fin N → Panel 4 3) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsize : rejection (iid candidateLaw N) φ ≤ 1 / 20) :
    rejection (iid sourceLaw N) φ < 4 / 5 := by
  apply finite_candidate_obstruction sourceLaw candidateLaw _
    source_candidate_rational_bound hN φ hφ hsize
  intro x
  exact add_pos_of_nonneg_of_pos (sourceLaw.nonneg x) (candidate_class_positive _)

end Rhone.Statistics.ConcretePanGrid
