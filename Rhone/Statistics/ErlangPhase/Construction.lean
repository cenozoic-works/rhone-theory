/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseBlockConstructor
public import Rhone.Statistics.Identifiability.FinitePhaseAlgebraicMembership

/-! # Erlang-phase pan model: construction of the chain, weights, and flux identity -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory
open scoped Matrix
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability FinitePhase

variable {J N : ℕ}

def chain (r : ℝ) (i j : Fin N) : ℝ :=
  (if i = j then -r else 0) + (if i.val + 1 = j.val then r else 0)

lemma sum_next (i : Fin N) (r : ℝ) :
    (∑ j : Fin N, if i.val + 1 = j.val then r else 0) =
      if i.val + 1 < N then r else 0 := by
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

lemma chain_row (r : ℝ) (i : Fin N) :
    ∑ j, chain r i j = if i.val + 1 < N then 0 else -r := by
  simp only [chain, Finset.sum_add_distrib]
  rw [sum_next]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> ring

lemma chain_column (r c : ℝ) (j : Fin N) :
    (∑ i, c * chain r i j) = if j.val = 0 then -(c * r) else 0 := by
  simp only [chain, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  have hd : (∑ i : Fin N, if i = j then c * -r else 0) = c * -r := by simp
  rw [hd]
  by_cases h : j.val = 0
  · have hz : (∑ i : Fin N, if i.val + 1 = j.val then c * r else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : i.val + 1 ≠ j.val := by omega
      simp [hi]
    rw [hz]
    simp [h]
  · let i : Fin N := ⟨j.val - 1, by omega⟩
    have hi : i.val + 1 = j.val := by dsimp [i]; omega
    have hs : (∑ k : Fin N, if k.val + 1 = j.val then c * r else 0) = c * r := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro k _ hk
        have hn : k.val + 1 ≠ j.val := by
          intro he
          apply hk
          apply Fin.ext
          dsimp [i]
          omega
        simp [hn]
      · simp
    rw [hs]
    simp [h]

def coordinates : Fin (J * N) ≃ Fin J × Fin N := finProdFinEquiv.symm

def pre (r : Fin J → ℝ) (i j : Fin (J * N)) : ℝ :=
  if (coordinates i).1 = (coordinates j).1 then
    chain (r (coordinates i).1) (coordinates i).2 (coordinates j).2 else 0

def weights (w : Fin J → ℝ) (i : Fin (J * N)) : ℝ :=
  if (coordinates i).2.val = 0 then w (coordinates i).1 else 0

def flux (r : Fin J → ℝ) (i : Fin (J * N)) (_j : Fin 1) : ℝ :=
  if (coordinates i).2.val + 1 < N then 0 else r (coordinates i).1

def post (b : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -b

lemma sum_coordinates (f : Fin (J * N) → ℝ) :
    ∑ i, f i = ∑ j : Fin J, ∑ k : Fin N, f (coordinates.symm (j, k)) := by
  calc
    _ = ∑ p : Fin J × Fin N, f (coordinates.symm p) :=
      (Equiv.sum_comp coordinates.symm f).symm
    _ = _ := Fintype.sum_prod_type _

lemma pre_row (r : Fin J → ℝ) (i : Fin (J * N)) :
    ∑ j, pre r i j = if (coordinates i).2.val + 1 < N then 0 else -r (coordinates i).1 := by
  rw [sum_coordinates]
  simp only [pre, Equiv.apply_symm_apply]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact chain_row _ _

lemma pre_metzler (r : Fin J → ℝ) (hr : ∀ j, 0 < r j) : IsMetzler (pre (N := N) r) := by
  intro i j hij
  unfold pre
  split_ifs with hb
  · have hk : (coordinates i).2 ≠ (coordinates j).2 := by
      intro h
      exact hij (coordinates.injective (Prod.ext hb h))
    simp only [chain, ite_eq_right hk, zero_add]
    split_ifs
    · exact (hr _).le
    · exact le_refl 0
  · exact le_refl 0

lemma weights_sum (w : Fin J → ℝ) (hN : 0 < N) : ∑ i, weights (N := N) w i = ∑ j, w j := by
  rw [sum_coordinates]
  simp only [weights, Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single ⟨0, hN⟩]
  · simp
  · intro k _ hk
    have hn : k.val ≠ 0 := by intro h; exact hk (Fin.ext h)
    simp [hn]
  · simp

lemma flux_identity (r : Fin J → ℝ) : flux (N := N) r *ᵥ (fun _ => 1) = exitRate (pre r) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mul_one, exitRate, Pi.neg_apply]
  rw [pre_row]
  simp only [Fin.sum_univ_one, flux]
  split_ifs <;> ring

def model (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hs : ∑ j, w j = 1) (hb : 0 < b) :
    Model (J * N) 1 :=
  Model.ofBlocks (pre r) (flux r) (post b) (weights w)
    (pre_metzler r hr)
    (by
      intro i
      rw [pre_row]
      split_ifs
      · exact le_refl 0
      · exact neg_nonpos.mpr (hr _).le)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (by intro i; simpa only [post, Fin.sum_univ_one, neg_nonpos] using hb.le)
    (by
      intro i j
      unfold flux
      split_ifs
      · exact le_refl 0
      · exact (hr _).le)
    (by
      intro i
      unfold weights
      split_ifs
      · exact (hw _).le
      · exact le_refl 0)
    (by rw [weights_sum w hN, hs])
    (flux_identity r)

lemma initial_exit_zero (r w : Fin J → ℝ) (hN : 2 ≤ N) :
    dotProduct (weights w) (exitRate (pre (N := N) r)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : (coordinates i).2.val = 0
  · have hn : (coordinates i).2.val + 1 < N := by omega
    simp only [exitRate, Pi.neg_apply, Matrix.mulVec, dotProduct, mul_one]
    rw [pre_row]
    simp [hn]
  · simp [weights, h]

def potentialPre (r w : Fin J → ℝ) (i : Fin (J * N)) : ℝ :=
  -w (coordinates i).1 / r (coordinates i).1

lemma potential_pre_mul (r w : Fin J → ℝ) (hr : ∀ j, 0 < r j) :
    potentialPre r w ᵥ* pre (N := N) r = weights w := by
  funext j
  simp only [Matrix.vecMul, dotProduct]
  rw [sum_coordinates]
  simp only [potentialPre, pre, Equiv.apply_symm_apply, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [chain_column]
  unfold weights
  split_ifs
  · field_simp [ne_of_gt (hr _)]
  · rfl

lemma potential_flux (r w : Fin J → ℝ) (hr : ∀ j, 0 < r j) (hN : 0 < N) (j : Fin 1) :
    (potentialPre r w ᵥ* flux (N := N) r) j = -(∑ k, w k) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [sum_coordinates]
  simp only [potentialPre, flux, Equiv.apply_symm_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single ⟨N - 1, by omega⟩]
  · have hn : ¬N - 1 + 1 < N := by omega
    simp only [hn, ite_false]
    exact div_mul_cancel₀ _ (ne_of_gt (hr k))
  · intro l _ hl
    have hn : l.val + 1 < N := by
      have hne : l.val ≠ N - 1 := by intro h; exact hl (Fin.ext h)
      omega
    simp [hn]
  · simp

def potential (r w : Fin J → ℝ) (b : ℝ) : Fin (J * N + 1) → ℝ :=
  Fin.addCases (potentialPre r w) (fun _ => -1 / b)

lemma potential_mul (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hs : ∑ j, w j = 1) (hb : 0 < b) :
    potential (N := N) r w b ᵥ* blockGenerator (pre r) (flux r) (post b) = initial (weights w) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_add, potential, blockGenerator,
      Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, add_zero,
      initial]
    exact congrFun (potential_pre_mul r w hr) j
  · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_add, potential, blockGenerator,
      Fin.addCases_left, Fin.addCases_right, initial, Fin.sum_univ_one, post]
    have hf := potential_flux r w hr hN j
    simp only [Matrix.vecMul, dotProduct] at hf
    rw [hf, hs]
    field_simp
    ring

lemma model_probability (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hs : ∑ j, w j = 1) (hb : 0 < b) :
    IsProbabilityMeasure (model r w b hN hr hw hs hb).law := by
  apply (model r w b hN hr hw hs hb).probability_iff_linear_system.mpr
  exact ⟨potential r w b, potential_mul r w b hN hr hs hb⟩

end Rhone.Statistics.ErlangPhase
