/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.RegularBlocks
public import Rhone.Probability.SamplingUniform.Rare

/-! # The generic hierarchy at inverse mutation zero -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Matrix Analysis.RareAlleleHierarchy RareAlleleHierarchy DiagonalChain
variable {K : Type*} [Field K] [CharZero K]

noncomputable def lambdaPhi (θ ρ : K) : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) (RatFunc K) :=
  genericPhi Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ)

noncomputable def lambdaTheta (θ ρ : K) : ℕ → ℕ → ℕ → RatFunc K :=
  Theta (alphaSeq Algebra.SamplingUniform.lambdaA) (alphaSeq (Algebra.SamplingUniform.lambdaB θ))
      (lambdaPhi θ ρ)

theorem lambdaTheta_system (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.T (RatFunc K) i j Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) *ᵥ
      (fun t : Fin (min i j + 1) => lambdaTheta θ ρ i j t) =
      fun t : Fin (min i j + 1) =>
        redSource (alphaSeq Algebra.SamplingUniform.lambdaA)
            (alphaSeq (Algebra.SamplingUniform.lambdaB θ)) (lambdaPhi θ ρ) i j t := by
  exact trid_mul_Theta
    (genericPhi_rareHyp Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
        (RatFunc.C ρ) (lambdaDfull_ne_zero θ ρ hE))
    (genericPhi_isRecursionSolution Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) (lambdaDfull_ne_zero θ ρ hE)) hi hj

omit [CharZero K] in
theorem lambdaTheta_clamp (θ ρ : K) {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (t : ℕ) :
    lambdaTheta θ ρ i j t = lambdaTheta θ ρ i j (blockLevel i j t) := by
  unfold lambdaTheta
  rw [Theta_eq_cf11 _ _ _ hi hj, Theta_eq_cf11 _ _ _ hi hj]
  change cf 1 1 (genericPhi Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
      (RatFunc.C ρ) i j t) =
    cf 1 1 (genericPhi Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
        (RatFunc.C ρ) i j (min t (min i j)))
  by_cases ht : t ≤ min i j
  · rw [min_eq_left ht]
  · rw [min_eq_right (by omega : min i j ≤ t), genericPhi_clamp _ _ _ i j t (by omega)]

theorem lambdaTheta_regular_zero (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) :
    lambdaTheta θ ρ i j t ∈ Algebra.SamplingUniform.regularAtZero K ∧
      (i ≠ j → RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ i j t) = 0) := by
  have main : ∀ n i j, i + j = n → ∀ t,
      lambdaTheta θ ρ i j t ∈ Algebra.SamplingUniform.regularAtZero K ∧
        (i ≠ j → RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ i j t) = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j hij t
      by_cases hi0 : i = 0
      · subst i
        simp [lambdaTheta, (Algebra.SamplingUniform.regularAtZero K).zero_mem]
      by_cases hj0 : j = 0
      · subst j
        simp [lambdaTheta, (Algebra.SamplingUniform.regularAtZero K).zero_mem]
      by_cases hi1 : i = 1
      · subst i
        by_cases hj1 : j = 1
        · subst j
          simp [lambdaTheta, (Algebra.SamplingUniform.regularAtZero K).one_mem]
        · have hj : 2 ≤ j := by omega
          change Theta _ _ _ 1 j t ∈ _ ∧ _
          simp only [lambdaTheta, Theta_one_right _ _ _ hj]
          constructor
          · exact alphaSeq_B_mem_regular θ j
          · intro _
            change RatFunc.eval (RingHom.id K) 0 (alphaSeq (RatFunc.C θ - RatFunc.X⁻¹) j) = 0
            rw [← coe_regularAlphaB θ j]
            exact residue_regularAlphaB θ hj
      by_cases hj1 : j = 1
      · subst j
        have hi : 2 ≤ i := by omega
        change Theta _ _ _ i 1 t ∈ _ ∧ _
        simp only [lambdaTheta, Theta_one_left _ _ _ hi]
        constructor
        · exact alphaSeq_A_mem_regular i
        · intro _
          change RatFunc.eval (RingHom.id K) 0 (alphaSeq (RatFunc.X⁻¹ : RatFunc K) i) = 0
          rw [← coe_regularAlphaA i]
          exact residue_regularAlphaA hi
      have hi : 2 ≤ i := by omega
      have hj : 2 ≤ j := by omega
      have hs (s : Fin (min i j + 1)) :
          redSource (alphaSeq Algebra.SamplingUniform.lambdaA)
              (alphaSeq (Algebra.SamplingUniform.lambdaB θ)) (lambdaPhi θ ρ) i j s
            ∈ Algebra.SamplingUniform.regularAtZero K := by
        unfold redSource
        apply (Algebra.SamplingUniform.regularAtZero K).add_mem
        · apply (Algebra.SamplingUniform.regularAtZero K).add_mem
          · exact (Algebra.SamplingUniform.regularAtZero K).mul_mem
              (natCast_mem (Algebra.SamplingUniform.regularAtZero K) _)
              (ih (i - 1 + j) (by omega) (i - 1) j rfl s).1
          · exact (Algebra.SamplingUniform.regularAtZero K).mul_mem
              (natCast_mem (Algebra.SamplingUniform.regularAtZero K) _)
              (ih (i + (j - 1)) (by omega) i (j - 1) rfl s).1
        · exact (Algebra.SamplingUniform.regularAtZero K).mul_mem
            (natCast_mem (Algebra.SamplingUniform.regularAtZero K) _)
            (ih (i - 1 + (j - 1)) (by omega) (i - 1) (j - 1) rfl (s - 1)).1
      let src : Fin (min i j + 1) → Algebra.SamplingUniform.RegularAtZero K := fun s => ⟨_, hs s⟩
      have hsys := lambdaTheta_system θ ρ hE hi hj
      rw [lambdaTheta_clamp θ ρ hi hj t]
      by_cases heq : i = j
      · subst j
        rw [Algebra.SamplingUniform.lambdaBlock_diagonal] at hsys
        constructor
        · exact Algebra.SamplingUniform.constant_matrix_solution_regular
            (LinearAlgebra.Tridiag.T K i i θ 0 ρ) (hE i hi)
            src (fun s => lambdaTheta θ ρ i i s) hsys (blockLevel i i t)
        · intro hne
          exact (hne rfl).elim
      · rw [lambdaBlock_eq_poleMatrix] at hsys
        have hz := Algebra.SamplingUniform.poleMatrix_solution_regular_zero
            (Algebra.SamplingUniform.index_difference_ne_zero heq)
          ((LinearAlgebra.Tridiag.T K i j 0 θ ρ).map Algebra.SamplingUniform.regularC) src
          (fun s => lambdaTheta θ ρ i j s) hsys (blockLevel i j t)
        exact ⟨hz.1, fun _ => hz.2⟩
  exact main (i + j) i j rfl t

end Rhone.Probability.SamplingUniform
