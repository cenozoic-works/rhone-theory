/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.Construction
public import Rhone.Statistics.ErlangPhase.ScalarDiscount

/-! # Resolvent and Laplace potential equation of the Erlang-phase generator -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Matrix Topology
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability FinitePhase
variable {J N : ℕ}

set_option backward.isDefEq.respectTransparency false

lemma sum_next_weight (i : Fin N) (f : Fin N → ℝ) :
    (∑ j : Fin N, if i.val + 1 = j.val then f j else 0) =
      if h : i.val + 1 < N then f ⟨i.val + 1, h⟩ else 0 := by
  split_ifs with h
  · let j : Fin N := ⟨i.val + 1, h⟩
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro k _ hk
      split_ifs with he
      · exact (hk (Fin.ext he.symm)).elim
      · rfl
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    split_ifs with he
    · exact (h (he ▸ j.isLt)).elim
    · rfl

lemma pre_mulVec (r : Fin J → ℝ) (v : Fin (J * N) → ℝ) (i : Fin (J * N)) :
    (pre r *ᵥ v) i = -r (coordinates i).1 * v i +
      if h : (coordinates i).2.val + 1 < N then
        r (coordinates i).1 * v (coordinates.symm ((coordinates i).1,
          ⟨(coordinates i).2.val + 1, h⟩)) else 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_coordinates]
  simp only [pre, Equiv.apply_symm_apply, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [chain, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Prod.mk.eta,
    Equiv.symm_apply_apply]
  rw [sum_next_weight]

abbrev generator (r : Fin J → ℝ) : Matrix (Fin (J * N)) (Fin (J * N)) ℝ := pre r

def laplacePotential (r : Fin J → ℝ) (s : ℝ) (i : Fin (J * N)) : ℝ :=
  (r (coordinates i).1 / (r (coordinates i).1 + s)) ^ (N - (coordinates i).2.val)

lemma laplacePotential_equation (r : Fin J → ℝ) (s : ℝ)
    (hr : ∀ j, 0 < r j) (hs : 0 ≤ s) :
    (generator (N := N) r - s • 1) *ᵥ laplacePotential r s = -exitRate (pre r) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change (pre r *ᵥ laplacePotential r s) i - _ = _
  rw [pre_mulVec]
  have hd : r (coordinates i).1 + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (hr _) hs)
  have hex : exitRate (pre r) i =
      if (coordinates i).2.val + 1 < N then 0 else r (coordinates i).1 := by
    simp only [exitRate, Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply]
    rw [pre_row]
    split_ifs <;> ring
  simp only [Pi.neg_apply, hex]
  by_cases h : (coordinates i).2.val + 1 < N
  · have hn : N - (coordinates i).2.val = (N - ((coordinates i).2.val + 1)) + 1 := by omega
    simp only [h, dite_true, ite_true, laplacePotential, Equiv.apply_symm_apply]
    rw [hn, pow_succ]
    field_simp
    ring
  · have hn : N - (coordinates i).2.val = 1 := by have := (coordinates i).2.isLt; omega
    simp only [h, dite_false, ite_false, laplacePotential, hn, pow_one]
    field_simp
    ring

end Rhone.Statistics.ErlangPhase
