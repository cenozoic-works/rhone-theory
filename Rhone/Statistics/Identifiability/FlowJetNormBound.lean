/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GeneratorNormBound
public import Rhone.Statistics.Identifiability.Cemetery
public import Rhone.Statistics.Identifiability.BackwardFlux
public import Rhone.Statistics.Identifiability.ForwardRank
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Substochastic flow and observable-jet norm bounds -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset

namespace Rhone.Statistics.Identifiability

theorem subgenerator_exp_opNorm_le_one {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsMetzler Q)
    (hrow : ∀ i, (∑ j, Q i j) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • Q)‖ ≤ 1 := by
  apply linfty_opNorm_le_of_abs_row_le _ (by norm_num)
  intro i
  simp_rw [abs_of_nonneg (exp_generator_nonneg Q hQ ht i _)]
  exact subgenerator_rows_le_one Q hQ hrow ht i

theorem abs_flowOutput_le_of_subgenerator {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsMetzler Q)
    (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (i : Fin d) (v : Fin d → ℝ) (a : Nat) {t : ℝ} (ht : 0 ≤ t) :
    |flowOutput Q i v a t| ≤ ‖Q‖^a * ‖v‖ := by
  let : Nonempty (Fin d) := ⟨i⟩
  have hexp := subgenerator_exp_opNorm_le_one Q hQ hrow ht
  have hmatrix : ‖Q^a * NormedSpace.exp (t • Q)‖ ≤ ‖Q‖^a := by
    calc
      ‖Q^a * NormedSpace.exp (t • Q)‖ ≤
          ‖Q^a‖ * ‖NormedSpace.exp (t • Q)‖ := norm_mul_le _ _
      _ ≤ ‖Q‖^a * 1 :=
        mul_le_mul (norm_pow_le Q a) hexp (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  calc
    |flowOutput Q i v a t| ≤ ‖(Q^a * NormedSpace.exp (t • Q)) *ᵥ v‖ := by
      simpa only [flowOutput, Real.norm_eq_abs] using
        norm_le_pi_norm ((Q^a * NormedSpace.exp (t • Q)) *ᵥ v) i
    _ ≤ ‖Q^a * NormedSpace.exp (t • Q)‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖Q‖^a * ‖v‖ := mul_le_mul_of_nonneg_right hmatrix (norm_nonneg _)

theorem iteratedDeriv_flowOutput {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (a b : Nat) :
    iteratedDeriv b (flowOutput Q i v a) = flowOutput Q i v (a+b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    simpa only [Nat.add_assoc] using (flowOutput_hasDerivAt Q i v (a+b) t).deriv

theorem flowOutput_contDiff_nat {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (a n : Nat) :
    ContDiff ℝ n (flowOutput Q i v a) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro b _
    rw [iteratedDeriv_flowOutput]
    exact flowOutput_continuous Q i v (a+b)
  · intro b _
    rw [iteratedDeriv_flowOutput]
    exact fun t => (flowOutput_hasDerivAt Q i v (a+b) t).differentiableAt

theorem firstAKernel_column_norm_le {c : ℝ} (hc : 0 ≤ c) (j : Fin 2) :
    ‖fun i => firstAKernel c i j‖ ≤ c := by
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  fin_cases i <;> fin_cases j <;>
    simp [firstAKernel, MarkovChain.Identifiability.firstATable,
        MarkovChain.Identifiability.firstAThenBTable, Real.norm_eq_abs,
      abs_of_nonneg hc, hc]

theorem pairDensity_norm_le {c : ℝ} (hc : 0 ≤ c) : ‖MarkovChain.Identifiability.pairDensity c‖ ≤
    c := by
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  fin_cases i <;> simp
      [MarkovChain.Identifiability.pairDensity, Real.norm_eq_abs, abs_of_nonneg hc, hc]

theorem pairGenerator_rows_le_zero (k : Nat) {c q : ℝ} (hc : 0 ≤ c) :
    ∀ i, (∑ j, MarkovChain.Identifiability.pairGenerator k c q i j) ≤ 0 := by
  intro i
  fin_cases i <;> simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_succ]
  linarith

theorem abs_transferJet_le (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (a : Nat) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    |transferJet k c q r a j t| ≤ ‖MarkovChain.Identifiability.generator k c q r‖^a * c := by
  have hrow : ∀ i, (∑ j, MarkovChain.Identifiability.generator k c q r i j) ≤ 0 := by
    intro i
    rw [generator_row_sum]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Nat.cast_nonneg _)
  exact (abs_flowOutput_le_of_subgenerator (MarkovChain.Identifiability.generator k c q r)
    (generator_metzler k hc hq hr) hrow 0 (fun i => firstAKernel c i j) a ht).trans
      (mul_le_mul_of_nonneg_left (firstAKernel_column_norm_le hc j) (by positivity))

theorem abs_transferJet_le_rateBound (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (a : Nat) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    |transferJet k c q r a j t| ≤ (12*c+4*r+8*((k : ℝ)+3)*q)^a * c := by
  apply (abs_transferJet_le k hc hq hr a j ht).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (generator_opNorm_le k hc hq hr) a) hc

theorem abs_pairDensity_flowJet_le (k : Nat) {c q : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (a : Nat) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    |flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
        (MarkovChain.Identifiability.pairDensity c) a t| ≤
      ‖MarkovChain.Identifiability.pairGenerator k c q‖^a * c := by
  exact (abs_flowOutput_le_of_subgenerator (MarkovChain.Identifiability.pairGenerator k c q)
    (pairGenerator_metzler k hq) (pairGenerator_rows_le_zero k hc) i
        (MarkovChain.Identifiability.pairDensity c) a ht).trans
      (mul_le_mul_of_nonneg_left (pairDensity_norm_le hc) (by positivity))

theorem abs_iteratedDeriv_forwardDensity_le (k : Nat) {c q : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (a : Nat) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv a (forwardDensity k c q i) t| ≤ ‖MarkovChain.Identifiability.pairGenerator k c
        q‖^a * c := by
  change |iteratedDeriv a
      (flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
      (MarkovChain.Identifiability.pairDensity c) 0) t| ≤ _
  rw [iteratedDeriv_flowOutput, zero_add]
  exact abs_pairDensity_flowJet_le k hc hq a i ht

theorem abs_iteratedDeriv_forwardDensity_le_rateBound (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (a : Nat) (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv a (forwardDensity k c q i) t| ≤
      (12*c+4*r+8*((k : ℝ)+3)*q)^a * c := by
  apply (abs_iteratedDeriv_forwardDensity_le k hc hq a i ht).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (pairGenerator_opNorm_le k hc hq hr) a) hc

theorem iteratedDeriv_transferJet (k : Nat) (c q r : ℝ) (a b : Nat) (j : Fin 2) :
    iteratedDeriv b (transferJet k c q r a j) = transferJet k c q r (a+b) j :=
  iteratedDeriv_flowOutput _ _ _ _ _

theorem transferJet_contDiff_nat (k : Nat) (c q r : ℝ) (a : Nat) (j : Fin 2) (n : Nat) :
    ContDiff ℝ n (transferJet k c q r a j) :=
  flowOutput_contDiff_nat _ _ _ _ _

theorem forwardDensity_contDiff_nat (k : Nat) (c q : ℝ) (i : Fin 2) (n : Nat) :
    ContDiff ℝ n (forwardDensity k c q i) :=
  flowOutput_contDiff_nat _ _ _ _ _

end Rhone.Statistics.Identifiability
