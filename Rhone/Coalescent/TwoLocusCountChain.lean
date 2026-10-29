/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusIntervalGenerator
public import Rhone.MarkovChain.JumpHoldLaplace

/-!
# The two-locus count chain on a finite box, and its Laplace transform

Source: griffiths1991_two_locus_graph, pp. 106–107, 110–111. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open Finset MarkovChain

abbrev CountBox (N : ℕ) := Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

variable {N : ℕ}

def boxVal (k : CountBox N) : Counts := ((k.1 : ℕ), (k.2.1 : ℕ), (k.2.2 : ℕ))

theorem boxVal_injective : Function.Injective (boxVal (N := N)) := by
  intro k k' h
  simp only [boxVal, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Prod.ext (Fin.ext h.2.1) (Fin.ext h.2.2))

def boxExt (f : CountBox N → ℝ) (t : Counts) : ℝ :=
  if h : t.1 < N + 1 ∧ t.2.1 < N + 1 ∧ t.2.2 < N + 1 then
    f (⟨t.1, h.1⟩, ⟨t.2.1, h.2.1⟩, ⟨t.2.2, h.2.2⟩) else 0

theorem boxExt_boxVal (f : CountBox N → ℝ) (k : CountBox N) : boxExt f (boxVal k) = f k := by
  simp [boxExt, boxVal, k.1.isLt, k.2.1.isLt, k.2.2.isLt]

noncomputable def coef (ρ : ℝ) (k : Counts) : Fin 5 → ℝ :=
  ![(k.1 : ℝ) * ((k.1 : ℝ) - 1) / 2 + (k.1 : ℝ) * (k.2.2 : ℝ),
    (k.2.1 : ℝ) * ((k.2.1 : ℝ) - 1) / 2 + (k.2.1 : ℝ) * (k.2.2 : ℝ),
    (k.2.2 : ℝ) * ((k.2.2 : ℝ) - 1) / 2,
    (k.1 : ℝ) * (k.2.1 : ℝ),
    (k.2.2 : ℝ) * (ρ / 2)]

def tgt (k : Counts) : Fin 5 → Counts :=
  ![(k.1 - 1, k.2.1, k.2.2), (k.1, k.2.1 - 1, k.2.2), (k.1, k.2.1, k.2.2 - 1),
    (k.1 - 1, k.2.1 - 1, k.2.2 + 1), recCounts k]

theorem countGen_eq_sum (ρ : ℝ) (g : Counts → ℝ) (k : Counts) :
    countGen ρ g k = ∑ i, coef ρ k i * (g (tgt k i) - g k) := by
  simp [countGen, coef, tgt, Fin.sum_univ_five]

theorem nat_mul_pred_div_two_nonneg (a : ℕ) : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    have : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    linarith

theorem coef_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (k : Counts) (i : Fin 5) : 0 ≤ coef ρ k i := by
  fin_cases i <;> simp only [coef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact add_nonneg (nat_mul_pred_div_two_nonneg _) (by positivity)
  · exact add_nonneg (nat_mul_pred_div_two_nonneg _) (by positivity)
  · exact nat_mul_pred_div_two_nonneg _
  · positivity
  · positivity

noncomputable def countRate (ρ : ℝ) (k k' : CountBox N) : ℝ :=
  countGen ρ (fun j => if j = boxVal k' then 1 else 0) (boxVal k)

theorem countRate_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) {k k' : CountBox N} (h : k ≠ k') :
    0 ≤ countRate ρ k k' := by
  rw [countRate, countGen_eq_sum]
  have h0 : (if boxVal k = boxVal k' then (1 : ℝ) else 0) = 0 :=
    ite_eq_right fun e => h (boxVal_injective e)
  rw [h0]
  refine Finset.sum_nonneg fun i _ => mul_nonneg (coef_nonneg hρ _ i) ?_
  split_ifs <;> norm_num

noncomputable def countChain (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) : RateChain (CountBox N) where
  Q k k' := if k = k' then -∑ k'' ∈ univ.erase k, countRate ρ k k'' else countRate ρ k k'
  off_diag_nonneg k k' h := by
    rw [ite_eq_right h]
    exact countRate_nonneg hρ h
  row_sum k := by
    rw [← Finset.add_sum_erase univ _ (mem_univ k), ite_eq_left rfl]
    rw [Finset.sum_congr rfl fun k' hk' => ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hk'))]
    ring

theorem sum_countChain_Q_mul_eq (ρ : ℝ) (hρ : 0 ≤ ρ) (k : CountBox N) (f : CountBox N → ℝ) :
    ∑ k', (countChain ρ hρ N).Q k k' * f k' =
      ∑ k', countRate ρ k k' * (f k' - f k) := by
  have hdiag : (countChain ρ hρ N).Q k k = -∑ k'' ∈ univ.erase k, countRate ρ k k'' :=
    ite_eq_left rfl
  have hoff : ∀ k' ∈ univ.erase k, (countChain ρ hρ N).Q k k' = countRate ρ k k' :=
    fun k' hk' => ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hk'))
  have hL : ∑ k', (countChain ρ hρ N).Q k k' * f k' = (countChain ρ hρ N).Q k k * f k +
      ∑ k' ∈ univ.erase k, (countChain ρ hρ N).Q k k' * f k' :=
    (Finset.add_sum_erase univ (fun k' => (countChain ρ hρ N).Q k k' * f k') (mem_univ k)).symm
  have hR : ∑ k', countRate ρ k k' * (f k' - f k) = countRate ρ k k * (f k - f k) +
      ∑ k' ∈ univ.erase k, countRate ρ k k' * (f k' - f k) :=
    (Finset.add_sum_erase univ (fun k' => countRate ρ k k' * (f k' - f k)) (mem_univ k)).symm
  have hE : ∑ k' ∈ univ.erase k, (countChain ρ hρ N).Q k k' * f k' =
      ∑ k' ∈ univ.erase k, countRate ρ k k' * f k' :=
    Finset.sum_congr rfl fun k' hk' => by rw [hoff k' hk']
  rw [hL, hR, hE, hdiag, sub_self, mul_zero, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem tgt_mem_box {ρ : ℝ} {k : Counts} (ha : k.1 + k.2.2 ≤ N) (hb : k.2.1 + k.2.2 ≤ N)
    (i : Fin 5) (hi : coef ρ k i ≠ 0) :
    ∃ k' : CountBox N, boxVal k' = tgt k i := by
  have mk : ∀ t : Counts, t.1 ≤ N → t.2.1 ≤ N → t.2.2 ≤ N → ∃ k' : CountBox N, boxVal k' = t :=
    fun t h1 h2 h3 => ⟨(⟨t.1, by omega⟩, ⟨t.2.1, by omega⟩, ⟨t.2.2, by omega⟩), rfl⟩
  fin_cases i <;> simp only [tgt, coef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    recCounts] at hi ⊢
  · exact mk _ (by simp; omega) (by simp; omega) (by simp; omega)
  · exact mk _ (by simp; omega) (by simp; omega) (by simp; omega)
  · exact mk _ (by simp; omega) (by simp; omega) (by simp; omega)
  · have h1 : k.1 ≠ 0 := fun h => hi (by simp [h])
    exact mk _ (by simp; omega) (by simp; omega) (by simp; omega)
  · have h1 : k.2.2 ≠ 0 := fun h => hi (by simp [h])
    exact mk _ (by simp; omega) (by simp; omega) (by simp; omega)

theorem sum_countChain_Q_mul (ρ : ℝ) (hρ : 0 ≤ ρ) {k : CountBox N}
    (ha : (boxVal k).1 + (boxVal k).2.2 ≤ N) (hb : (boxVal k).2.1 + (boxVal k).2.2 ≤ N)
    (g : Counts → ℝ) :
    ∑ k', (countChain ρ hρ N).Q k k' * g (boxVal k') = countGen ρ g (boxVal k) := by
  classical
  rw [sum_countChain_Q_mul_eq, countGen_eq_sum]
  have hrate : ∀ k', countRate ρ k k' = ∑ i, coef ρ (boxVal k) i *
      ((if tgt (boxVal k) i = boxVal k' then 1 else 0) -
        (if boxVal k = boxVal k' then 1 else 0)) := fun k' => by
    rw [countRate, countGen_eq_sum]
  simp only [hrate, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdrop : ∀ k' : CountBox N, coef ρ (boxVal k) i *
      ((if tgt (boxVal k) i = boxVal k' then (1 : ℝ) else 0) -
        (if boxVal k = boxVal k' then 1 else 0)) * (g (boxVal k') - g (boxVal k)) =
      coef ρ (boxVal k) i * ((if tgt (boxVal k) i = boxVal k' then (1 : ℝ) else 0) *
        (g (boxVal k') - g (boxVal k))) := fun k' => by
    by_cases h : boxVal k = boxVal k'
    · rw [← h]; ring
    · rw [ite_eq_right h]; ring
  simp only [hdrop, ← Finset.mul_sum]
  by_cases hc : coef ρ (boxVal k) i = 0
  · rw [hc, zero_mul, zero_mul]
  · obtain ⟨k0, hk0⟩ := tgt_mem_box ha hb i hc
    congr 1
    have hiff : ∀ k', (tgt (boxVal k) i = boxVal k') ↔ k0 = k' := fun k' => by
      rw [← hk0]
      exact boxVal_injective.eq_iff
    simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true, hk0]

noncomputable def countCost (lam mu : ℝ) (k : Counts) : ℝ :=
  (if 2 ≤ k.1 + k.2.2 then lam else 0) + (if 2 ≤ k.2.1 + k.2.2 then mu else 0)

theorem countCost_nonneg {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) (k : Counts) :
    0 ≤ countCost lam mu k := by
  unfold countCost
  split_ifs <;> linarith

theorem countCost_eq_zero_of_rate_eq_zero (ρ : ℝ) (hρ : 0 ≤ ρ) (lam mu : ℝ) {k : CountBox N}
    (ha : (boxVal k).1 + (boxVal k).2.2 ≤ N) (hb : (boxVal k).2.1 + (boxVal k).2.2 ≤ N)
    (h0 : (countChain ρ hρ N).rate k = 0) :
    countCost lam mu (boxVal k) = 0 ∧ ∀ g, countGen ρ g (boxVal k) = 0 := by
  have hQ : ∀ k', (countChain ρ hρ N).Q k k' = 0 := by
    have hsum := (countChain ρ hρ N).rate_eq_sum k
    rw [h0] at hsum
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k' hk' =>
      (countChain ρ hρ N).off_diag_nonneg k k' (Finset.ne_of_mem_erase hk').symm).1 hsum.symm
    intro k'
    by_cases hk : k = k'
    · subst hk
      have : (countChain ρ hρ N).Q k k = -(countChain ρ hρ N).rate k := by
        simp [RateChain.rate]
      rw [this, h0, neg_zero]
    · exact hz k' (Finset.mem_erase.2 ⟨Ne.symm hk, mem_univ _⟩)
  have hgen : ∀ g, countGen ρ g (boxVal k) = 0 := fun g => by
    rw [← sum_countChain_Q_mul ρ hρ ha hb g]
    simp [hQ]
  refine ⟨?_, hgen⟩
  have hl := hgen (fun j => if j = boxVal k then 0 else 1)
  rw [countGen_leave] at hl
  set a := (boxVal k).1
  set b := (boxVal k).2.1
  set c := (boxVal k).2.2
  have hc0 : 0 ≤ (c : ℝ) * (ρ / 2) := by positivity
  have hn := nat_mul_pred_div_two_nonneg (a + b + c)
  have hn0 : ((a + b + c : ℕ) : ℝ) * (((a + b + c : ℕ) : ℝ) - 1) / 2 = 0 := by linarith
  have hle : a + b + c ≤ 1 := by
    by_contra hgt
    have h2 : (2 : ℝ) ≤ ((a + b + c : ℕ) : ℝ) := by exact_mod_cast (not_le.1 hgt)
    nlinarith
  unfold countCost
  rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

theorem countCost_mul_laplace_eq_countGen (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) {k : CountBox N} (ha : (boxVal k).1 + (boxVal k).2.2 ≤ N)
    (hb : (boxVal k).2.1 + (boxVal k).2.2 ≤ N) :
    countCost lam mu (boxVal k) *
        (countChain ρ hρ N).laplace (fun k' => countCost lam mu (boxVal k')) k =
      countGen ρ (boxExt ((countChain ρ hρ N).laplace
        (fun k' => countCost lam mu (boxVal k')))) (boxVal k) := by
  set ψ := (countChain ρ hρ N).laplace (fun k' => countCost lam mu (boxVal k')) with hψ
  by_cases h0 : (countChain ρ hρ N).rate k = 0
  · obtain ⟨hc, hg⟩ := countCost_eq_zero_of_rate_eq_zero ρ hρ lam mu ha hb h0
    rw [hc, zero_mul, hg]
  · have h := (countChain ρ hρ N).mul_laplace_eq_generator
      (c := fun k' => countCost lam mu (boxVal k')) (fun k' => countCost_nonneg hl hm _) h0
    rw [← sum_countChain_Q_mul ρ hρ ha hb]
    simp only [boxExt_boxVal]
    exact h

theorem tgt_sum_le {ρ : ℝ} {k : Counts} {i : Fin 5} (hi : coef ρ k i ≠ 0) :
    (tgt k i).1 + (tgt k i).2.2 ≤ k.1 + k.2.2 ∧
      (tgt k i).2.1 + (tgt k i).2.2 ≤ k.2.1 + k.2.2 := by
  fin_cases i <;> simp only [tgt, coef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, recCounts] at hi ⊢
  · refine ⟨?_, ?_⟩ <;> omega
  · refine ⟨?_, ?_⟩ <;> omega
  · refine ⟨?_, ?_⟩ <;> omega
  · have h1 : k.1 ≠ 0 := fun h => hi (by simp [h])
    have h2 : k.2.1 ≠ 0 := fun h => hi (by simp [h])
    refine ⟨?_, ?_⟩ <;> omega
  · have h1 : k.2.2 ≠ 0 := fun h => hi (by simp [h])
    refine ⟨?_, ?_⟩ <;> omega

theorem countCost_tgt_eq_zero {ρ lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) {k : Counts}
    (hk : countCost lam mu k = 0) {i : Fin 5} (hi : coef ρ k i ≠ 0) :
    countCost lam mu (tgt k i) = 0 := by
  obtain ⟨h1, h2⟩ := tgt_sum_le hi
  unfold countCost at hk ⊢
  split_ifs at hk ⊢ <;> linarith

theorem countChain_isClosedSet_cost (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) :
    (countChain ρ hρ N).jumpChain.IsClosedSet
      (univ.filter fun k : CountBox N => countCost lam mu (boxVal k) = 0) := by
  classical
  refine (countChain ρ hρ N).isClosedSet_jumpChain fun k hk k' hk' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  have hne : k ≠ k' := fun e => hk' (e ▸ hk)
  rw [show (countChain ρ hρ N).Q k k' = countRate ρ k k' from ite_eq_right hne]
  simp only [countRate, countGen_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hc : coef ρ (boxVal k) i = 0
  · rw [hc, zero_mul]
  · have ht := countCost_tgt_eq_zero hl hm hk hc
    have h1 : tgt (boxVal k) i ≠ boxVal k' := fun e => hk' (e ▸ ht)
    have h2 : boxVal k ≠ boxVal k' := fun e => hne (boxVal_injective e)
    simp [h1, h2]

theorem countChain_laplace_eq_one (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) {k : CountBox N} (hk : countCost lam mu (boxVal k) = 0) :
    (countChain ρ hρ N).laplace (fun k' => countCost lam mu (boxVal k')) k = 1 :=
  (countChain ρ hρ N).laplace_eq_one_of_isClosedSet (fun _ => countCost_nonneg hl hm _)
    (countChain_isClosedSet_cost ρ hρ hl hm) (fun _ hk' => (Finset.mem_filter.1 hk').2)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)

end Rhone.Coalescent.IntervalCounts
