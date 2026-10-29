/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.BackwardFlux
public import Rhone.Statistics.Identifiability.ForwardRank

/-! # A rank-two factorization of the island upper-triangle density -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Set
namespace Rhone.Statistics.Identifiability

theorem transferJet_zero_order (k : Nat) (c q r s : ℝ) (j : Fin 2) :
    transferJet k c q r 0 j s =
      (NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) * firstAKernel c) 0 j :=
          by
  simp only [transferJet, flowOutput, pow_zero, Matrix.one_mul]
  rfl

theorem pairEntryJet_zero_order (k : Nat) (c q s : ℝ) (i j : Fin 2) :
    pairEntryJet k c q 0 i j s = NormedSpace.exp
        (s • MarkovChain.Identifiability.pairGenerator k c q) i j := by
  simp [pairEntryJet, flowOutput]

theorem backwardFlux_matrix (k : Nat) (c q r s : ℝ) (j : Fin 2) :
    backwardFlux k c q r j s =
      (NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) * firstAKernel c *
        NormedSpace.exp ((-s) • MarkovChain.Identifiability.pairGenerator k c q)) 0 j := by
  simp only [backwardFlux, transferJet_zero_order, pairEntryJet_zero_order, Matrix.mul_apply]

theorem pair_exp_sub (k : Nat) (c q s t : ℝ) :
    NormedSpace.exp ((t-s) • MarkovChain.Identifiability.pairGenerator k c q) =
      NormedSpace.exp ((-s) • MarkovChain.Identifiability.pairGenerator k c q) *
        NormedSpace.exp (t • MarkovChain.Identifiability.pairGenerator k c q) := by
  have hcomm : Commute ((-s) • MarkovChain.Identifiability.pairGenerator k c q)
      (t • MarkovChain.Identifiability.pairGenerator k c q) :=
    ((Commute.refl _).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  congr 1
  module

theorem upperDensity_factorization (k : Nat) (c q r s t : ℝ) :
    upperDensity k c q r s t =
      backwardFlux k c q r 0 s * forwardDensity k c q 0 t +
      backwardFlux k c q r 1 s * forwardDensity k c q 1 t := by
  rw [upperDensity, pair_exp_sub, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  simp only [backwardFlux_matrix, forwardDensity, flowOutput, pow_zero, Matrix.one_mul]
  conv_lhs => rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem backward_rank_two (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ∃ s₁ ∈ Icc (0 : ℝ) (1/2), ∃ s₂ ∈ Icc (0 : ℝ) (1/2),
      backwardFlux k c q r 0 s₁ * backwardFlux k c q r 1 s₂ -
      backwardFlux k c q r 1 s₁ * backwardFlux k c q r 0 s₂ ≠ 0 := by
  apply row_rank_two_of_jets _ _ (backwardFluxD k c q r 0)
    (backwardFluxD k c q r 1) (backwardFluxDD k c q r 1) (by norm_num)
    (backwardFlux_hasDerivAt k c q r 0) (backwardFlux_hasDerivAt k c q r 1)
    (backwardFluxD_hasDerivAt k c q r 1 0)
  · rw [backwardFluxD_zero]
    simpa using ne_of_gt (show 0 < 2*r*c from by positivity)
  · simp [backwardFluxD_zero]
  · rw [backwardFluxDD_apart_zero k hc.ne']
    have hpos : 0 < 6*r*c*MarkovChain.Identifiability.totalMigration k q :=
        by unfold MarkovChain.Identifiability.totalMigration; positivity
    nlinarith

end Rhone.Statistics.Identifiability
