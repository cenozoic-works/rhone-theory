/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeGenerator
public import Rhone.Statistics.Identifiability.IntervalRank

/-! # Exact third-order separation of first-merger and pair survival -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

noncomputable def threeSurvivalJet (k : Nat) (c q : ℝ) (a : Nat) (t : ℝ) : ℝ :=
  flowOutput (threeGenerator k c q) 0 (fun _ => 1) a t

theorem three_survival_jet_one (k : Nat) (c q : ℝ) : threeSurvivalJet k c q 1 0 = -3*c := by
  simp [threeSurvivalJet, threeGenerator_row_sum]

theorem three_survival_jet_two (k : Nat) (c q : ℝ) :
    threeSurvivalJet k c q 2 0 = 9*c^2 + 6*c*MarkovChain.Identifiability.totalMigration k q := by
  simp only [threeSurvivalJet, flowOutput_zero, pow_two, ← Matrix.mulVec_mulVec,
    threeGenerator_row_sum]
  simp [threeGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem three_survival_jet_three (k : Nat) (c q : ℝ) :
    threeSurvivalJet k c q 3 0 =
      -27*c^3-42*c^2*MarkovChain.Identifiability.totalMigration k
          q-12*c*(MarkovChain.Identifiability.totalMigration k
          q)^2-12*c*MarkovChain.Identifiability.totalMigration k q*q := by
  simp only [threeSurvivalJet, flowOutput_zero, pow_succ, pow_zero, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, threeGenerator_row_sum]
  simp [threeGenerator, MarkovChain.Identifiability.totalMigration, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  ring

theorem pair_survival_jet_three (k : Nat) (c q : ℝ) :
    survivalJet k c q 3 0 =
        -c*(c+2*MarkovChain.Identifiability.totalMigration k
        q)^2-4*c*MarkovChain.Identifiability.totalMigration k q*q := by
  simp only [survivalJet, flowOutput_zero, pow_succ, pow_zero, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  simp [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.pairSurvival,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem pair_survival_jet_zero_value (k : Nat) (c q : ℝ) : survivalJet k c q 0 0 = 1 := by
  simp [survivalJet]

theorem pair_survival_jet_one_value (k : Nat) (c q : ℝ) : survivalJet k c q 1 0 = -c := by
  simp [survivalJet, MarkovChain.Identifiability.pair_survival_jet_one]

theorem pair_survival_jet_two_value (k : Nat) (c q : ℝ) :
    survivalJet k c q 2 0 = c*(c+2*MarkovChain.Identifiability.totalMigration k q) := by
  simp only [survivalJet, flowOutput_zero, pow_two, ← Matrix.mulVec_mulVec]
  simp [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.pairSurvival,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

noncomputable def threeWitness (k : Nat) (c q t : ℝ) : ℝ :=
  threeSurvivalJet k c q 0 t - (survivalJet k c q 0 t)^3

noncomputable def threeWitnessD (k : Nat) (c q t : ℝ) : ℝ :=
  threeSurvivalJet k c q 1 t - 3*(survivalJet k c q 0 t)^2*survivalJet k c q 1 t

noncomputable def threeWitnessDD (k : Nat) (c q t : ℝ) : ℝ :=
  threeSurvivalJet k c q 2 t - 6*survivalJet k c q 0 t*(survivalJet k c q 1 t)^2 -
    3*(survivalJet k c q 0 t)^2*survivalJet k c q 2 t

noncomputable def threeWitnessDDD (k : Nat) (c q t : ℝ) : ℝ :=
  threeSurvivalJet k c q 3 t - 6*(survivalJet k c q 1 t)^3 -
    18*survivalJet k c q 0 t*survivalJet k c q 1 t*survivalJet k c q 2 t -
    3*(survivalJet k c q 0 t)^2*survivalJet k c q 3 t

set_option backward.isDefEq.respectTransparency false in
theorem threeWitness_hasDerivAt (k : Nat) (c q t : ℝ) :
    HasDerivAt (threeWitness k c q) (threeWitnessD k c q t) t := by
  convert! (flowOutput_hasDerivAt (threeGenerator k c q) 0 (fun _ => 1) 0 t).sub
    ((flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
        MarkovChain.Identifiability.pairSurvival 0 t).pow 3) using 1

set_option backward.isDefEq.respectTransparency false in
theorem threeWitnessD_hasDerivAt (k : Nat) (c q t : ℝ) :
    HasDerivAt (threeWitnessD k c q) (threeWitnessDD k c q t) t := by
  have h0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 0 t
  have h1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 1 t
  convert! (flowOutput_hasDerivAt (threeGenerator k c q) 0 (fun _ => 1) 1 t).sub
    (((h0.pow 2).const_mul 3).mul h1) using 1
  dsimp [threeWitnessDD, threeSurvivalJet, survivalJet]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem threeWitnessDD_hasDerivAt (k : Nat) (c q t : ℝ) :
    HasDerivAt (threeWitnessDD k c q) (threeWitnessDDD k c q t) t := by
  have h0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 0 t
  have h1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 1 t
  have h2 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 2 t
  convert! ((flowOutput_hasDerivAt (threeGenerator k c q) 0 (fun _ => 1) 2 t).sub
    ((h0.const_mul 6).mul (h1.pow 2))).sub (((h0.pow 2).const_mul 3).mul h2) using 1
  dsimp [threeWitnessDDD, threeSurvivalJet, survivalJet]
  ring

theorem threeWitnessDDD_zero (k : Nat) (c q : ℝ) :
    threeWitnessDDD k c q 0 = 6*c^2*MarkovChain.Identifiability.totalMigration k q := by
  simp only [threeWitnessDDD, three_survival_jet_three, pair_survival_jet_three,
    pair_survival_jet_zero_value, pair_survival_jet_one_value, pair_survival_jet_two_value]
  ring

theorem threeWitness_not_zero_on_unit_interval (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ¬ (∀ t ∈ Set.Icc (0 : ℝ) 1, threeWitness k c q t = 0) := by
  intro hz
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, threeWitnessD k c q t = 0 := by
    intro t ht
    exact derivative_zero_on_interval _ zero_lt_one ht (threeWitness_hasDerivAt k c q t) hz
  have h := second_derivative_zero_on_interval (threeWitnessD k c q)
    (threeWitnessDD k c q) (threeWitnessDDD k c q) zero_lt_one
    (threeWitnessD_hasDerivAt k c q) (threeWitnessDD_hasDerivAt k c q 0) hd
  rw [threeWitnessDDD_zero] at h
  have hp : 0 < 6*c^2*MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  linarith

end Rhone.Statistics.Identifiability
