/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteProductExponential
public import Rhone.Statistics.Identifiability.MatrixKernelJetCertificate
public import Mathlib.Data.Matrix.Block

/-! # Block realizations allow finite certificates to compare distinct finite models -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma exp_fromBlocks_diagonal (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (t : ℝ) :
    NormedSpace.exp (t • Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (NormedSpace.exp (t • A)) 0 0 (NormedSpace.exp (t • B)) := by
  let Q := Matrix.fromBlocks A 0 0 B
  let F := fun u : ℝ =>
    Matrix.fromBlocks (NormedSpace.exp (u • A)) 0 0 (NormedSpace.exp (u • B))
  have hd : ∀ u i j, HasDerivAt (fun v => F v i j) ((F u * Q) i j) u := by
    intro u i j
    cases i <;> cases j
    · simpa [F, Q, Matrix.fromBlocks_multiply] using exp_entry_hasDerivAt A _ _ u
    · simpa [F, Q, Matrix.fromBlocks_multiply] using (hasDerivAt_const u (0 : ℝ))
    · simpa [F, Q, Matrix.fromBlocks_multiply] using (hasDerivAt_const u (0 : ℝ))
    · simpa [F, Q, Matrix.fromBlocks_multiply] using exp_entry_hasDerivAt B _ _ u
  have he := finiteMatrix_solution_eq_transition (fun _ => Q) F
    (fun _ _ => continuous_const) 0 hd t
  have hz : F 0 = 1 := by simp [F, Matrix.fromBlocks_one]
  rw [hz, Matrix.one_mul, transition_const_eq_exp, sub_zero] at he
  exact he.symm

variable {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι']
  [Fintype κ'] [DecidableEq κ']

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] in
lemma kernel_block_difference (α : ι → ℝ) (β : ι' → ℝ)
    (F : Matrix ι κ ℝ) (G : Matrix ι' κ' ℝ) (v : κ → ℝ) (w : κ' → ℝ)
    (X : Matrix ι ι ℝ) (X' : Matrix ι' ι' ℝ)
    (Y : Matrix κ κ ℝ) (Y' : Matrix κ' κ' ℝ) :
    kernelValue (Sum.elim α (-β)) (Matrix.fromBlocks F 0 0 G) (Sum.elim v w)
      (Matrix.fromBlocks X 0 0 X') (Matrix.fromBlocks Y 0 0 Y') =
      kernelValue α F v X Y - kernelValue β G w X' Y' := by
  simp [kernelValue, Matrix.fromBlocks_mulVec, Function.comp_def,
    sumElim_dotProduct_sumElim, sub_eq_add_neg]

theorem positive_kernels_equal_iff_finite [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (A' : Matrix ι' ι' ℝ) (B' : Matrix κ' κ' ℝ)
    (α : ι → ℝ) (β : ι' → ℝ) (F : Matrix ι κ ℝ) (G : Matrix ι' κ' ℝ)
    (v : κ → ℝ) (w : κ' → ℝ) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)) =
        kernelValue β G w (NormedSpace.exp (s • A')) (NormedSpace.exp (t • B'))) ↔
    (∀ i : ℕ, i < Fintype.card ι + Fintype.card ι' →
      ∀ j : ℕ, j < Fintype.card κ + Fintype.card κ' →
      kernelValue α F v (A ^ i) (B ^ j) = kernelValue β G w (A' ^ i) (B' ^ j)) := by
  have h := positive_kernel_zero_iff_finite
    (Matrix.fromBlocks A 0 0 A') (Matrix.fromBlocks B 0 0 B')
    (Sum.elim α (-β)) (Matrix.fromBlocks F 0 0 G) (Sum.elim v w)
  simpa only [exp_fromBlocks_diagonal, Matrix.fromBlocks_diagonal_pow,
    kernel_block_difference, sub_eq_zero, Fintype.card_sum] using h

end Rhone.Statistics.Identifiability.FiniteExponentialJets
