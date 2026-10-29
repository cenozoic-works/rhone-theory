/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.MullerRatchetClasses
public import Rhone.MarkovChain.ClosedFundamentalMatrix
public import Rhone.MarkovChain.ClosedHitting
public import Rhone.MarkovChain.GreenMatrix
public import Rhone.MarkovChain.StationaryLaw

/-!
# The truncated class-count chain of Muller's ratchet

Source: haigh1978, eq. (1), p. 252; etheridge_etal2007, sec. 2, eq. (2.3). -/

@[expose] public section

namespace Rhone.MarkovChain.TruncatedRatchet

open Finset Matrix MeasureTheory ProbabilityTheory
open Dynamics.HaighRecursion MullerRatchet
open scoped ENNReal NNReal

variable {N K : ℕ}

abbrev State (N K : ℕ) : Type := AlleleCounts N (K + 1)

def count (n : State N K) (k : ℕ) : ℕ := if h : k < K + 1 then n.val ⟨k, h⟩ else 0

noncomputable def fitnessSum (s : ℝ) (n : State N K) : ℝ :=
  ∑ k ∈ range (K + 1), (count n k : ℝ) * (1 - s) ^ k

noncomputable def cellWeight (s U : ℝ) (n : State N K) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1),
    (count n j : ℝ) * (1 - s) ^ j / fitnessSum s n * poissonWeight U (m - j)

noncomputable def cellNorm (s U : ℝ) (n : State N K) : ℝ :=
  ∑ m ∈ range (K + 1), cellWeight s U n m

noncomputable def cellProb (s U : ℝ) (n : State N K) (l : Fin (K + 1)) : ℝ :=
  cellWeight s U n l / cellNorm s U n

noncomputable def trans (s U : ℝ) (n b : State N K) : ℝ :=
  (Nat.multinomial (Finset.univ : Finset (Fin (K + 1))) b.val : ℝ) *
    ∏ l, cellProb s U n l ^ b.val l

def clickSet (N K : ℕ) : Finset (State N K) := univ.filter fun n => n.val 0 = 0

theorem count_coe (n : State N K) (l : Fin (K + 1)) : count n l = n.val l := by
  rw [count, dite_eq_left l.isLt]

theorem count_zero (n : State N K) : count n 0 = n.val 0 := count_coe n 0

theorem sum_fin_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ l : Fin (K + 1), f l = ∑ k ∈ range (K + 1), f k :=
  Fin.sum_univ_eq_sum_range f (K + 1)

theorem sum_count (n : State N K) : ∑ k ∈ range (K + 1), count n k = N := by
  rw [← sum_fin_eq_sum_range]
  simp only [count_coe]
  exact n.sum

theorem fitnessSum_nonneg {s : ℝ} (hs : s < 1) (n : State N K) : 0 ≤ fitnessSum s n :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)

theorem fitnessSum_pos [NeZero N] {s : ℝ} (hs : s < 1) (n : State N K) :
    0 < fitnessSum s n := by
  have h1 : (0 : ℝ) < 1 - s := by linarith
  have hne : ∑ k ∈ range (K + 1), count n k ≠ 0 := by
    rw [sum_count]
    exact NeZero.ne N
  obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h1.le _))
    ⟨k, hk, ?_⟩
  have hpos : (0 : ℝ) < count n k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  exact mul_pos hpos (pow_pos h1 _)

theorem sum_selection [NeZero N] {s : ℝ} (hs : s < 1) (n : State N K) :
    ∑ k ∈ range (K + 1), (count n k : ℝ) * (1 - s) ^ k / fitnessSum s n = 1 := by
  rw [← Finset.sum_div]
  exact div_self (fitnessSum_pos hs n).ne'

theorem term_nonneg {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) (j i : ℕ) :
    0 ≤ (count n j : ℝ) * (1 - s) ^ j / fitnessSum s n * poissonWeight U i :=
  mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
    (fitnessSum_nonneg hs n)) (poissonWeight_nonneg hU _)

theorem cellWeight_nonneg {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) (m : ℕ) :
    0 ≤ cellWeight s U n m :=
  Finset.sum_nonneg fun _ _ => term_nonneg hs hU n _ _

theorem term_le_cellWeight {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) {j m : ℕ}
    (hjm : j ≤ m) :
    (count n j : ℝ) * (1 - s) ^ j / fitnessSum s n * poissonWeight U (m - j) ≤
      cellWeight s U n m :=
  Finset.single_le_sum
    (f := fun j => (count n j : ℝ) * (1 - s) ^ j / fitnessSum s n * poissonWeight U (m - j))
    (fun _ _ => term_nonneg hs hU n _ _) (mem_range.2 (Nat.lt_succ_of_le hjm))

theorem cellWeight_zero (s U : ℝ) (n : State N K) :
    cellWeight s U n 0 = (n.val 0 : ℝ) / fitnessSum s n * Real.exp (-U) := by
  rw [cellWeight, zero_add, range_one, sum_singleton, pow_zero, mul_one, Nat.sub_self,
    poissonWeight_zero, count_zero]

theorem exp_le_cellNorm [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) :
    Real.exp (-U) ≤ cellNorm s U n := by
  calc Real.exp (-U)
      = ∑ m ∈ range (K + 1),
          (count n m : ℝ) * (1 - s) ^ m / fitnessSum s n * poissonWeight U 0 := by
        rw [← Finset.sum_mul, sum_selection hs n, one_mul, poissonWeight_zero]
    _ ≤ cellNorm s U n := Finset.sum_le_sum fun m _ => by
        have h := term_le_cellWeight hs hU n (le_refl m)
        rwa [Nat.sub_self] at h

theorem cellNorm_pos [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) :
    0 < cellNorm s U n :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_le_cellNorm hs hU n)

theorem cellProb_nonneg [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K)
    (l : Fin (K + 1)) : 0 ≤ cellProb s U n l :=
  div_nonneg (cellWeight_nonneg hs hU n l) (cellNorm_pos hs hU n).le

theorem sum_cellProb [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) :
    ∑ l, cellProb s U n l = 1 := by
  simp only [cellProb]
  rw [← Finset.sum_div, sum_fin_eq_sum_range (fun k => cellWeight s U n k)]
  exact div_self (cellNorm_pos hs hU n).ne'

theorem cellProb_zero (s U : ℝ) (n : State N K) :
    cellProb s U n 0 = cellWeight s U n 0 / cellNorm s U n := by
  rw [cellProb, Fin.val_zero]

theorem trans_nonneg [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n b : State N K) :
    0 ≤ trans s U n b :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun l _ => pow_nonneg (cellProb_nonneg hs hU n l) _)

theorem sum_trans [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) :
    ∑ b, trans s U n b = 1 := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (K + 1)))
    (fun l => cellProb s U n l) N
  rw [← Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin (K + 1))) N)] at h
  have h' : (∑ b : State N K, trans s U n b) = (∑ l, cellProb s U n l) ^ N := by
    simpa [trans] using h.symm
  rw [h', sum_cellProb hs hU n, one_pow]

noncomputable def chain [NeZero N] (K : ℕ) {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) :
    FinChain (State N K) where
  P := trans s U
  nonneg := trans_nonneg hs hU
  row_sum := sum_trans hs hU

theorem mem_clickSet {n : State N K} : n ∈ clickSet N K ↔ n.val 0 = 0 := by
  simp [clickSet]

theorem isClosedSet_clickSet [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) :
    (chain (N := N) K hs hU).IsClosedSet (clickSet N K) := by
  intro x hx y hy
  rw [mem_clickSet] at hx hy
  change trans s U x y = 0
  rw [trans, Finset.prod_eq_zero (Finset.mem_univ 0), mul_zero]
  rw [cellProb_zero, cellWeight_zero, hx, Nat.cast_zero, zero_div, zero_mul, zero_div,
    zero_pow hy]

theorem cellProb_pos [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) {n : State N K}
    (hn : n.val 0 ≠ 0) (l : Fin (K + 1)) : 0 < cellProb s U n l := by
  refine div_pos (lt_of_lt_of_le ?_ (term_le_cellWeight hs hU.le n (Nat.zero_le l)))
    (cellNorm_pos hs hU.le n)
  have h0 : (0 : ℝ) < count n 0 := by
    rw [count_zero]
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hq : 0 < poissonWeight U (l - 0) := by
    rw [poissonWeight]
    positivity
  exact mul_pos (div_pos (mul_pos h0 (pow_pos (by linarith) _)) (fitnessSum_pos hs n)) hq

theorem trans_pos [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) {n : State N K}
    (hn : n.val 0 ≠ 0) (b : State N K) : 0 < trans s U n b := by
  refine mul_pos ?_ (Finset.prod_pos fun l _ => pow_pos (cellProb_pos hs hU hn l) _)
  exact_mod_cast Nat.pos_of_ne_zero (Nat.multinomial_pos _ _).ne'

theorem cellProb_zero_le [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (hK : 1 ≤ K)
    (n : State N K) : cellProb s U n 0 ≤ 1 / (1 + U) := by
  have hZ := cellNorm_pos hs hU n
  have h1 : (count n 0 : ℝ) * (1 - s) ^ 0 / fitnessSum s n * poissonWeight U (1 - 0) ≤
      cellWeight s U n 1 := term_le_cellWeight hs hU n (Nat.zero_le 1)
  have hq1 : poissonWeight U (1 - 0) = Real.exp (-U) * U := by
    simp [poissonWeight]
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (K + 1) := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rw [mem_range]
    omega
  have hpair : cellWeight s U n 0 + cellWeight s U n 1 ≤ cellNorm s U n := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun m => cellWeight s U n m) hsub
      fun m _ _ => cellWeight_nonneg hs hU n m
    rwa [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at h
  rw [cellProb_zero, div_le_div_iff₀ hZ (by linarith), one_mul]
  rw [hq1, pow_zero, mul_one, count_zero] at h1
  have h0 := cellWeight_zero s U n
  calc cellWeight s U n 0 * (1 + U)
      = cellWeight s U n 0 + (n.val 0 : ℝ) / fitnessSum s n * (Real.exp (-U) * U) := by
        rw [h0]
        ring
    _ ≤ cellWeight s U n 0 + cellWeight s U n 1 := by linarith
    _ ≤ cellNorm s U n := hpair

theorem sum_clickSet_trans [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (n : State N K) :
    ∑ b ∈ clickSet N K, trans s U n b = (1 - cellProb s U n 0) ^ N := by
  rw [clickSet, Finset.sum_filter]
  have h := sum_multinomial_of_apply_eq_zero N (K + 1) (cellProb s U n) 0
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), sum_cellProb hs hU n] at h
  exact h

theorem le_sum_clickSet_trans [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (hK : 1 ≤ K)
    (n : State N K) : (U / (1 + U)) ^ N ≤ ∑ b ∈ clickSet N K, trans s U n b := by
  rw [sum_clickSet_trans hs hU n]
  have h1U : (0 : ℝ) < 1 + U := by linarith
  refine pow_le_pow_left₀ (div_nonneg hU h1U.le) ?_ N
  have h := cellProb_zero_le hs hU hK n
  have he : U / (1 + U) = 1 - 1 / (1 + U) := by
    field_simp
    ring
  rw [he]
  linarith

theorem reaches_clickSet [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) (hK : 1 ≤ K) :
    (chain (N := N) K hs hU.le).Reaches (clickSet N K) := by
  refine FinChain.reaches_of_rank _ _ (fun n => if n ∈ clickSet N K then 0 else 1) fun x hx => ?_
  have hpos : 0 < ∑ b ∈ clickSet N K, trans s U x b :=
    lt_of_lt_of_le (pow_pos (div_pos hU (by linarith)) N) (le_sum_clickSet_trans hs hU.le hK x)
  by_contra hcon
  push Not at hcon
  refine absurd hpos (not_lt.2 (Finset.sum_nonpos fun b hb => ?_))
  by_contra hb0
  have := hcon b (not_le.1 hb0)
  simp [hb, hx] at this

theorem isUnit_one_sub_transientBlock [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U)
    (hK : 1 ≤ K) :
    IsUnit (1 - (chain (N := N) K hs hU.le).transientBlock (clickSet N K)) :=
  (isClosedSet_clickSet hs hU.le).isUnit_one_sub_transientBlock (reaches_clickSet hs hU hK)

theorem killing_transientBlock [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (n : FinChain.Transient (clickSet N K)) :
    GreenMatrix.killing ((chain (N := N) K hs hU).transientBlock (clickSet N K)) n =
      (1 - cellProb s U n.1 0) ^ N := by
  have hsplit := FinChain.sum_P_mul_eq (C := chain (N := N) K hs hU) (clickSet N K)
    (fun _ => 1) n.1
  simp only [mul_one] at hsplit
  rw [(chain (N := N) K hs hU).row_sum,
    Finset.sum_coe_sort (clickSet N K) (fun a => (chain (N := N) K hs hU).P n.1 a)] at hsplit
  have hclick : ∑ a ∈ clickSet N K, (chain (N := N) K hs hU).P n.1 a =
      (1 - cellProb s U n.1 0) ^ N := sum_clickSet_trans hs hU n.1
  rw [GreenMatrix.killing_apply, ← hclick]
  have hQ : ∑ j, (chain (N := N) K hs hU).transientBlock (clickSet N K) n j =
      ∑ y : FinChain.Transient (clickSet N K), (chain (N := N) K hs hU).P n.1 y := rfl
  rw [hQ]
  linarith

theorem sum_transientBlock_le [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (hK : 1 ≤ K)
    (n : FinChain.Transient (clickSet N K)) :
    ∑ j, (chain (N := N) K hs hU).transientBlock (clickSet N K) n j ≤
      1 - (U / (1 + U)) ^ N := by
  have h := killing_transientBlock hs hU n
  rw [GreenMatrix.killing_apply, ← sum_clickSet_trans hs hU n.1] at h
  have hle := le_sum_clickSet_trans hs hU hK n.1
  linarith

theorem absorbTime_eq_meanTime [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) (hK : 1 ≤ K)
    (n : FinChain.Transient (clickSet N K)) :
    (chain (N := N) K hs hU.le).absorbTime (clickSet N K) n.1 =
      GreenMatrix.meanTime ((chain (N := N) K hs hU.le).transientBlock (clickSet N K)) n :=
  congrFun ((isClosedSet_clickSet hs hU.le).absorbTime_eq_fundamental_mulVec
    (reaches_clickSet hs hU hK)) n

theorem lintegral_hitTime_eq_meanTime [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U)
    (hK : 1 ≤ K) (n : FinChain.Transient (clickSet N K)) :
    ∫⁻ ω, (hitTime (clickSet N K) ω : ℝ≥0∞) ∂(chain (N := N) K hs hU.le).pathLaw n.1 =
      ENNReal.ofReal
        (GreenMatrix.meanTime ((chain (N := N) K hs hU.le).transientBlock (clickSet N K)) n) := by
  rw [(isClosedSet_clickSet hs hU.le).lintegral_hitTime (reaches_clickSet hs hU hK),
    absorbTime_eq_meanTime hs hU hK]

theorem eq_meanTime_iff [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) (hK : 1 ≤ K)
    (τ : FinChain.Transient (clickSet N K) → ℝ) :
    τ = 1 + (chain (N := N) K hs hU.le).transientBlock (clickSet N K) *ᵥ τ ↔
      τ = GreenMatrix.meanTime ((chain (N := N) K hs hU.le).transientBlock (clickSet N K)) := by
  have hQ := isUnit_one_sub_transientBlock (N := N) hs hU hK
  have key : ∀ τ : FinChain.Transient (clickSet N K) → ℝ,
      τ = 1 + (chain (N := N) K hs hU.le).transientBlock (clickSet N K) *ᵥ τ ↔
        (1 - (chain (N := N) K hs hU.le).transientBlock (clickSet N K)) *ᵥ τ = 1 := by
    intro τ
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add]
  constructor
  · intro h
    exact GreenMatrix.eq_meanTime hQ ((key τ).1 h)
  · intro h
    rw [h]
    exact (key _).2 (GreenMatrix.one_sub_mulVec_meanTime hQ)

theorem green_nonneg [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) (hK : 1 ≤ K)
    (n m : FinChain.Transient (clickSet N K)) :
    0 ≤ GreenMatrix.green ((chain (N := N) K hs hU.le).transientBlock (clickSet N K)) n m :=
  (isClosedSet_clickSet hs hU.le).fundamental_nonneg (reaches_clickSet hs hU hK) n m

def cell (K k : ℕ) : Fin (K + 1) := ⟨min k K, by omega⟩

noncomputable def ofPop (K : ℕ) (x : Fin N → ℕ) : State N K :=
  wfAlleleAllocationCounts N (K + 1) fun t => cell K (x t)

theorem count_ofPop {x : Fin N → ℕ} (hx : ∀ t, x t ≤ K) (j : ℕ) :
    count (ofPop K x) j = classCount x j := by
  rw [count]
  split_ifs with h
  · rw [ofPop, wfAlleleAllocationCounts_apply, classCount]
    congr 1
    ext t
    simp only [mem_filter, mem_univ, true_and, cell, Fin.mk.injEq]
    have := hx t
    omega
  · rw [classCount, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    have := hx t
    omega

theorem fitnessSum_ofPop (s : ℝ) {x : Fin N → ℕ} (hx : ∀ t, x t ≤ K) :
    fitnessSum s (ofPop K x) = ∑ q, (1 - s) ^ x q := by
  rw [fitnessSum]
  simp only [count_ofPop hx]
  exact sum_classCount_mul_pow s x hx

theorem cellWeight_ofPop (s U : ℝ) {x : Fin N → ℕ} (hx : ∀ t, x t ≤ K) (m : ℕ) :
    cellWeight s U (ofPop K x) m = classProb s U x m := by
  rw [cellWeight, classProb, fitnessSum_ofPop s hx]
  simp only [count_ofPop hx]

theorem offspringLaw_Iic [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) {x : Fin N → ℕ}
    (hx : ∀ t, x t ≤ K) :
    offspringLaw s U x (Set.Iic K) = ENNReal.ofReal (cellNorm s U (ofPop K x)) := by
  have hset : Set.Iic K = ((range (K + 1) : Finset ℕ) : Set ℕ) := by
    ext k
    simp
  rw [hset, ← sum_measure_singleton, cellNorm,
    ENNReal.ofReal_sum_of_nonneg fun m _ => cellWeight_nonneg hs U.coe_nonneg _ m]
  refine sum_congr rfl fun m _ => ?_
  rw [offspringLaw_singleton hs, cellWeight_ofPop _ _ hx]

theorem cond_offspringLaw_cell [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) {x : Fin N → ℕ}
    (hx : ∀ t, x t ≤ K) (l : Fin (K + 1)) :
    (offspringLaw s U x)[cell K ⁻¹' {l} | Set.Iic K] =
      ENNReal.ofReal (cellProb s U (ofPop K x) l) := by
  have hint : Set.Iic K ∩ cell K ⁻¹' {l} = {(l : ℕ)} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_preimage, Set.mem_singleton_iff, cell,
      Fin.ext_iff]
    have := l.isLt
    omega
  rw [cond_apply measurableSet_Iic, hint, offspringLaw_singleton hs, offspringLaw_Iic hs U hx,
    cellProb, ENNReal.ofReal_div_of_pos (cellNorm_pos hs U.coe_nonneg _),
    cellWeight_ofPop _ _ hx, ENNReal.div_eq_inv_mul]

theorem cond_stepLaw_ofPop [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) {x : Fin N → ℕ}
    (hx : ∀ t, x t ≤ K) (b : State N K) :
    (stepLaw s U x)[{y | ofPop K y = b} | {y | ∀ t, y t ≤ K}] =
      ENNReal.ofReal (trans s U (ofPop K x) b) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have h0 : offspringLaw s U x (Set.Iic K) ≠ 0 := by
    rw [offspringLaw_Iic hs U hx]
    exact (ENNReal.ofReal_pos.2 (cellNorm_pos hs U.coe_nonneg _)).ne'
  have hset : {y : Fin N → ℕ | ∀ t, y t ≤ K} = Set.pi Set.univ fun _ => Set.Iic K := by
    ext y
    simp [Pi.le_def]
  have := cond_isProbabilityMeasure h0
  rw [stepLaw, hset, cond_pi _ N measurableSet_Iic h0]
  refine (pi_allocationCounts ((offspringLaw s U x)[|Set.Iic K]) N (K + 1)
    (Measurable.of_discrete (f := cell K)) b).trans ?_
  simp only [cond_offspringLaw_cell hs U hx]
  rw [trans, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_prod_of_nonneg fun l _ =>
      pow_nonneg (cellProb_nonneg hs U.coe_nonneg _ l) _]
  simp only [ENNReal.ofReal_pow (cellProb_nonneg hs U.coe_nonneg _ _)]

theorem card_state (N K : ℕ) : Fintype.card (State N K) = (N + K).choose K := by
  have h : K + 1 + N - 1 = N + K := by omega
  rw [card_alleleCounts, h, Nat.choose_symm_add]

theorem sum_update_zero (f : Fin (K + 1) → ℕ) (c : ℕ) {M : ℕ} (hf : ∑ l, f l = M) :
    Finset.univ.sum (Function.update f 0 c) + f 0 = M + c := by
  have h1 : Finset.univ.sum (Function.update f 0 c) = c + ∑ x ∈ univ \ {0}, f x :=
    Finset.sum_update_of_mem (Finset.mem_univ (0 : Fin (K + 1))) f c
  have h2 := Finset.sum_update_of_mem (Finset.mem_univ (0 : Fin (K + 1))) f (f 0)
  rw [Function.update_eq_self] at h2
  rw [← hf]
  omega

theorem card_transient [NeZero N] (K : ℕ) :
    Fintype.card (FinChain.Transient (clickSet N K)) = (N - 1 + K).choose K := by
  rw [← card_state (N - 1) K]
  have hN : 1 ≤ N := NeZero.pos N
  let f : FinChain.Transient (clickSet N K) → State (N - 1) K := fun n =>
    ⟨Function.update n.1.val 0 (n.1.val 0 - 1), by
      have h0 : n.1.val 0 ≠ 0 := fun h => n.2 (mem_clickSet.2 h)
      have hu := sum_update_zero n.1.val (n.1.val 0 - 1) n.1.sum
      exact Finset.mem_piAntidiag.2 ⟨by omega, by simp⟩⟩
  let g : State (N - 1) K → FinChain.Transient (clickSet N K) := fun m =>
    ⟨⟨Function.update m.val 0 (m.val 0 + 1), by
      have hu := sum_update_zero m.val (m.val 0 + 1) m.sum
      exact Finset.mem_piAntidiag.2 ⟨by omega, by simp⟩⟩, by
      rw [mem_clickSet]
      simp⟩
  refine Fintype.card_congr ⟨f, g, fun n => ?_, fun m => ?_⟩
  · have h0 : n.1.val 0 ≠ 0 := fun h => n.2 (mem_clickSet.2 h)
    apply Subtype.ext
    apply Subtype.ext
    funext l
    by_cases hl : l = 0
    · rw [hl]
      simp only [f, g, Function.update_self]
      omega
    · simp [f, g, Function.update_of_ne hl]
  · apply Subtype.ext
    funext l
    by_cases hl : l = 0
    · rw [hl]
      simp [f, g]
    · simp [f, g, Function.update_of_ne hl]

noncomputable abbrev transientQ [NeZero N] (K : ℕ) {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) :
    Matrix (FinChain.Transient (clickSet N K)) (FinChain.Transient (clickSet N K)) ℝ :=
  (chain (N := N) K hs hU).transientBlock (clickSet N K)

noncomputable def restartBlock (s U : ℝ) (R : State N K → FinChain.Transient (clickSet N K)) :
    Matrix (FinChain.Transient (clickSet N K)) (FinChain.Transient (clickSet N K)) ℝ :=
  fun n m => ∑ z ∈ (clickSet N K).filter (fun z => R z = m), trans s U n.1 z

theorem restartBlock_nonneg [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (R : State N K → FinChain.Transient (clickSet N K))
    (n m : FinChain.Transient (clickSet N K)) : 0 ≤ restartBlock s U R n m :=
  Finset.sum_nonneg fun _ _ => trans_nonneg hs hU _ _

theorem restartBlock_mulVec_one [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (R : State N K → FinChain.Transient (clickSet N K)) :
    restartBlock s U R *ᵥ 1 = GreenMatrix.killing (transientQ (N := N) K hs hU) := by
  funext n
  rw [killing_transientBlock hs hU n, ← sum_clickSet_trans hs hU n.1]
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, restartBlock]
  exact Finset.sum_fiberwise (clickSet N K) R fun z => trans s U n.1 z

theorem sum_restartBlock [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (R : State N K → FinChain.Transient (clickSet N K))
    (n : FinChain.Transient (clickSet N K)) :
    ∑ m, restartBlock s U R n m = GreenMatrix.killing (transientQ (N := N) K hs hU) n := by
  rw [← restartBlock_mulVec_one hs hU R]
  simp [mulVec, dotProduct]

noncomputable def restartChain [NeZero N] (K : ℕ) {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (R : State N K → FinChain.Transient (clickSet N K)) :
    RateChain (FinChain.Transient (clickSet N K)) where
  Q := transientQ (N := N) K hs hU + restartBlock s U R - 1
  off_diag_nonneg := fun x y hxy => by
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hxy, sub_zero]
    exact add_nonneg (trans_nonneg hs hU _ _) (restartBlock_nonneg hs hU R x y)
  row_sum := fun x => by
    have h1 : ∑ y, (1 : Matrix (FinChain.Transient (clickSet N K))
        (FinChain.Transient (clickSet N K)) ℝ) x y = 1 := by
      simp [Matrix.one_apply]
    simp only [Matrix.sub_apply, Matrix.add_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, h1]
    rw [sum_restartBlock hs hU R x, GreenMatrix.killing_apply]
    ring

theorem isStationary_restartChain_iff [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U)
    (R : State N K → FinChain.Transient (clickSet N K))
    (π : FinChain.Transient (clickSet N K) → ℝ) :
    (restartChain K hs hU R).IsStationary π ↔
      (∀ n, 0 ≤ π n) ∧ ∑ n, π n = 1 ∧
        π ᵥ* (transientQ (N := N) K hs hU + restartBlock s U R) = π := by
  have key : π ᵥ* (restartChain K hs hU R).Q = 0 ↔
      π ᵥ* (transientQ (N := N) K hs hU + restartBlock s U R) = π := by
    change π ᵥ* (transientQ (N := N) K hs hU + restartBlock s U R - 1) = 0 ↔ _
    rw [vecMul_sub, vecMul_one, sub_eq_zero]
  exact ⟨fun h => ⟨h.nonneg, h.sum_eq_one, key.1 h.vecMul_Q⟩,
    fun h => ⟨h.1, h.2.1, key.2 h.2.2⟩⟩

theorem isIrreducible_restartChain [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U)
    (R : State N K → FinChain.Transient (clickSet N K)) :
    (restartChain K hs hU.le R).IsIrreducible := by
  intro x y
  by_cases hxy : x = y
  · rw [hxy]
  · refine Relation.ReflTransGen.single ⟨hxy, ?_⟩
    change 0 < (transientQ (N := N) K hs hU.le + restartBlock s U R - 1) x y
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hxy, sub_zero]
    exact add_pos_of_pos_of_nonneg (trans_pos hs hU (fun h => x.2 (mem_clickSet.2 h)) y.1)
      (restartBlock_nonneg hs hU.le R x y)

theorem existsUnique_stationary_restart [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U)
    (R : State N K → FinChain.Transient (clickSet N K)) :
    ∃! π : FinChain.Transient (clickSet N K) → ℝ, (∀ n, 0 ≤ π n) ∧ ∑ n, π n = 1 ∧
      π ᵥ* (transientQ (N := N) K hs hU.le + restartBlock s U R) = π := by
  have hne : Nonempty (FinChain.Transient (clickSet N K)) := by
    refine Fintype.card_pos_iff.1 ?_
    rw [card_transient]
    exact Nat.choose_pos (Nat.le_add_left K (N - 1))
  obtain ⟨π, hπ⟩ := (restartChain K hs hU.le R).exists_isStationary
  refine ⟨π, (isStationary_restartChain_iff hs hU.le R π).1 hπ, fun ρ hρ => ?_⟩
  exact RateChain.IsStationary.eq_of_irreducible (isIrreducible_restartChain hs hU R)
    ((isStationary_restartChain_iff hs hU.le R ρ).2 hρ) hπ

theorem stationary_restart_pos [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U)
    (R : State N K → FinChain.Transient (clickSet N K))
    {π : FinChain.Transient (clickSet N K) → ℝ} (h0 : ∀ n, 0 ≤ π n) (h1 : ∑ n, π n = 1)
    (hπ : π ᵥ* (transientQ (N := N) K hs hU.le + restartBlock s U R) = π)
    (n : FinChain.Transient (clickSet N K)) : 0 < π n :=
  RateChain.IsStationary.pos_of_irreducible (isIrreducible_restartChain hs hU R)
    ((isStationary_restartChain_iff hs hU.le R π).2 ⟨h0, h1, hπ⟩) n

theorem le_dotProduct_killing [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (hK : 1 ≤ K)
    {π : FinChain.Transient (clickSet N K) → ℝ} (h0 : ∀ n, 0 ≤ π n) (h1 : ∑ n, π n = 1) :
    (U / (1 + U)) ^ N ≤ π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU) := by
  calc (U / (1 + U)) ^ N = ∑ n, π n * (U / (1 + U)) ^ N := by
        rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ n, π n * GreenMatrix.killing (transientQ (N := N) K hs hU) n :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (by
          rw [killing_transientBlock hs hU n, ← sum_clickSet_trans hs hU n.1]
          exact le_sum_clickSet_trans hs hU hK n.1) (h0 n)

theorem kac_restart [NeZero N] {s U : ℝ} (hs : s < 1) (hU : 0 < U) (hK : 1 ≤ K)
    (R : State N K → FinChain.Transient (clickSet N K))
    {π : FinChain.Transient (clickSet N K) → ℝ} (h0 : ∀ n, 0 ≤ π n) (h1 : ∑ n, π n = 1)
    (hπ : π ᵥ* (transientQ (N := N) K hs hU.le + restartBlock s U R) = π) :
    0 < π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU.le) ∧
      ((π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU.le))⁻¹ •
        (π ᵥ* restartBlock s U R)) ⬝ᵥ 1 = 1 ∧
      ((π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU.le))⁻¹ •
        (π ᵥ* restartBlock s U R)) ⬝ᵥ GreenMatrix.meanTime (transientQ (N := N) K hs hU.le) =
        (π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU.le))⁻¹ := by
  have hpos : 0 < π ⬝ᵥ GreenMatrix.killing (transientQ (N := N) K hs hU.le) :=
    lt_of_lt_of_le (pow_pos (div_pos hU (by linarith)) N) (le_dotProduct_killing hs hU.le hK h0 h1)
  have h1' : π ⬝ᵥ 1 = 1 := by rw [dotProduct_one, h1]
  exact ⟨hpos, GreenMatrix.kac_formula (isUnit_one_sub_transientBlock hs hU hK) hπ
    (restartBlock_mulVec_one hs hU.le R) h1' hpos.ne'⟩

end Rhone.MarkovChain.TruncatedRatchet
