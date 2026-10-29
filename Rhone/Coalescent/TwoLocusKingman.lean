/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.ContinuousTimeGenealogy.Second
public import Rhone.Coalescent.KingmanPartition
public import Rhone.Coalescent.KingmanPathMoments

/-! # At `ρ = 0` the two-locus tree length has the Kingman mean and variance -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy
  TypedAncestralChain BranchLengthMoments SecondMoments ContinuousTimeGenealogy
open scoped ENNReal

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Icc 1 m, f k = ∑ i ∈ range m, f (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem expLength_cast (n : ℕ) :
    ((Rhone.Coalescent.expLength n : ℚ) : ℝ) = 2 * ∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1) := by
  rw [Rhone.Coalescent.expLength_eq, harmonic]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [one_div]

theorem varLength_cast (n : ℕ) :
    ((Rhone.Coalescent.varLength n : ℚ) : ℝ) =
      4 * ∑ i ∈ range (n - 1), (1 : ℝ) / (i + 1) ^ 2 := by
  rw [Rhone.Coalescent.varLength_eq]
  push_cast
  rw [sum_Icc_one_eq_sum_range (fun k => (1 : ℝ) / (k : ℝ) ^ 2) (n - 1)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by push_cast; rfl

theorem ctLaw_treeLength_eq_kingman {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (h : Adm (0 : ℝ) 0 ρ πA πB) :
    ∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z
        ∂(ctLaw (0 : ℝ) 0 ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)) =
      ∫⁻ p, Rhone.Coalescent.partitionTreeLength p
        ∂(Rhone.Coalescent.partitionChain (Fin n)).jumpHoldLaw ⊥ := by
  rw [expected_ct_total_length h, Rhone.Coalescent.lintegral_partitionTreeLength,
    Fintype.card_fin, expLength_cast]

theorem ctLaw_treeLength_sq_eq_kingman {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (h : Adm (0 : ℝ) 0 ρ πA πB) :
    ∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z * ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z
        ∂(ctLaw (0 : ℝ) 0 ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)) =
      ∫⁻ p, (Rhone.Coalescent.treeLength n p) ^ 2
        ∂(Rhone.Coalescent.blockChain n).jumpHoldLaw (Fin.last n) := by
  rw [expected_ct_total_length_sq h, Rhone.Coalescent.lintegral_treeLength_sq,
    expLength_cast, varLength_cast]

end Rhone.Coalescent
