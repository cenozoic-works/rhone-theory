/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MatrixFlow
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Tactic.Positivity

/-! # Finite conservative generators give stochastic transition matrices -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability

def IsMetzler {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 ≤ Q i j

def IsConservative {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Q *ᵥ (fun _ => 1) = 0

theorem exp_entry_hasSum {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    HasSum (fun n : Nat => ((n.factorial : ℝ)⁻¹) * (A^n) i j)
      (NormedSpace.exp A i j) := by
  have h := (rowFunctional i (Pi.single j 1)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A)
  convert! (show HasSum _ _ from h) using 1 <;> simp [rowFunctional_apply]

theorem exp_nonneg_of_nonneg {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ NormedSpace.exp A i j := by
  intro i j
  apply (exp_entry_hasSum A i j).nonneg
  intro n
  exact mul_nonneg (by positivity) (Matrix.pow_apply_nonneg hA n i j)

theorem exp_smul_identity {d : Nat} (x : ℝ) :
    NormedSpace.exp (x • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      Real.exp x • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have h := NormedSpace.map_exp (algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ))
    (continuous_algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ)) x
  convert! h.symm using 1 <;> simp only [← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]

theorem exp_generator_nonneg {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i j, 0 ≤ NormedSpace.exp (t • Q) i j := by
  let b : ℝ := ∑ i, |Q i i|
  have hdiag : ∀ i, -Q i i ≤ b := by
    intro i
    exact le_trans (neg_le_abs (Q i i))
      (Finset.single_le_sum (fun j _ => abs_nonneg (Q j j)) (Finset.mem_univ i))
  have hA : ∀ i j, 0 ≤ (Q + b • 1) i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [add_comm] using (neg_le_iff_add_nonneg.mp (hdiag i))
    · simpa [Matrix.one_apply, hij] using hQ i j hij
  have hsplit : t • Q = (-t*b) • 1 + t • (Q + b • 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((-t*b) • (1 : Matrix (Fin d) (Fin d) ℝ))
      (t • (Q + b • 1)) := (Commute.one_left _).smul_left _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_identity]
  intro i j
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
  apply mul_nonneg (Real.exp_pos _).le
  exact exp_nonneg_of_nonneg _ (fun a b => mul_nonneg ht (hA a b)) i j

theorem conservative_power {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsConservative Q) (k : Nat) :
    Q^(k+1) *ᵥ (fun _ => 1) = 0 := by
  rw [pow_succ, ← Matrix.mulVec_mulVec, hQ, Matrix.mulVec_zero]

theorem exp_generator_rows {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsConservative Q) (t : ℝ) :
    NormedSpace.exp (t • Q) *ᵥ (fun _ => 1) = (fun _ => 1) := by
  have htQ : IsConservative (t • Q) := by
    dsimp [IsConservative] at *
    rw [Matrix.smul_mulVec, hQ, smul_zero]
  ext i
  have hs := (rowFunctional i (fun _ => 1)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q))
  simp only [map_smul, rowFunctional_apply, smul_eq_mul] at hs
  have heq : (NormedSpace.exp (t • Q) *ᵥ (fun _ => 1)) i =
      ∑' n : Nat, ((n.factorial : ℝ)⁻¹) * ((t • Q)^n *ᵥ (fun _ => 1)) i := by
    convert! hs.tsum_eq.symm using 1
  rw [heq, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [conservative_power _ htQ]

theorem exp_generator_stochastic {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : IsConservative Q) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • Q) ∈ Matrix.rowStochastic ℝ (Fin d) :=
  ⟨exp_generator_nonneg Q hQ ht, exp_generator_rows Q hrow t⟩

end Rhone.Statistics.Identifiability
