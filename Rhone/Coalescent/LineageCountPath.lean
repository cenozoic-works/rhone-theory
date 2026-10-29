/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.VariableSizeLineageCount
public import Rhone.Coalescent.KingmanFiniteRewards

/-!
# The number of lineages of the jump-and-hold Kingman path at one time

Source: tavare1984, eq. (3.8), (6.1), pp. 126, 132. -/

@[expose] public section

noncomputable section

namespace Rhone.Coalescent

open MeasureTheory Finset MarkovChain

def coalescenceCount (n : ℕ) (τ : ℝ) (p : VariableSizePath n) : ℕ :=
  ((Finset.Ico 1 n).filter fun m => (partitionChain (Fin n)).jumpTime p m ≤ τ).card

def lineageCountAt (n : ℕ) (τ : ℝ) (p : VariableSizePath n) : ℕ :=
  (p.1 (coalescenceCount n τ p)).parts.card

def levelEvent (n : ℕ) (τ : ℝ) (m : ℕ) : Set (VariableSizePath n) :=
  {p | (partitionChain (Fin n)).jumpTime p m ≤ τ ∧
    (m + 1 < n → τ < (partitionChain (Fin n)).jumpTime p (m + 1))}

theorem measurableSet_levelEvent (n : ℕ) (τ : ℝ) (m : ℕ) :
    MeasurableSet (levelEvent n τ m) := by
  by_cases hm : m + 1 < n
  · have h : levelEvent n τ m = {p | (partitionChain (Fin n)).jumpTime p m ≤ τ} ∩
        {p | τ < (partitionChain (Fin n)).jumpTime p (m + 1)} := by
      ext p
      simp [levelEvent, hm]
    rw [h]
    exact (measurableSet_le (measurable_partition_jumpTime n m) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_partition_jumpTime n (m + 1)))
  · have h : levelEvent n τ m = {p | (partitionChain (Fin n)).jumpTime p m ≤ τ} := by
      ext p
      simp [levelEvent, hm]
    rw [h]
    exact measurableSet_le (measurable_partition_jumpTime n m) measurable_const

theorem coalescenceCount_eq_of_mem {n : ℕ} {τ : ℝ} {p : VariableSizePath n}
    (hmono : ∀ i j, i ≤ j → j < n →
      (partitionChain (Fin n)).jumpTime p i ≤ (partitionChain (Fin n)).jumpTime p j)
    {m : ℕ} (hm : m < n) (hp : p ∈ levelEvent n τ m) : coalescenceCount n τ p = m := by
  obtain ⟨h1, h2⟩ := hp
  have hset : (Finset.Ico 1 n).filter
      (fun i => (partitionChain (Fin n)).jumpTime p i ≤ τ) = Finset.Ico 1 (m + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hi1, hin⟩, hiτ⟩
      refine ⟨hi1, ?_⟩
      by_contra hcon
      have hmn : m + 1 < n := by omega
      have := hmono (m + 1) i (by omega) hin
      linarith [h2 hmn]
    · rintro ⟨hi1, him⟩
      exact ⟨⟨hi1, by omega⟩, (hmono i m (by omega) hm).trans h1⟩
  rw [coalescenceCount, hset, Nat.card_Ico]
  omega

theorem exists_mem_levelEvent {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ)
    (p : VariableSizePath n) : ∃ m, m < n ∧ p ∈ levelEvent n τ m := by
  classical
  have hex : ∃ m, m + 1 < n → τ < (partitionChain (Fin n)).jumpTime p (m + 1) :=
    ⟨n - 1, fun h => absurd h (by omega)⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra hcon
    have := Nat.find_min' hex (m := n - 1) (fun h => absurd h (by omega))
    omega
  · simp only [levelEvent, Set.mem_ofPred_eq]
    refine ⟨?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      simpa [RateChain.jumpTime] using hτ
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
      simp only [not_imp, not_lt] at hmin
      rw [hk]
      exact hmin.2

theorem ae_jumpTime_monotone (n : ℕ) :
    ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥, ∀ i j, i ≤ j → j < n →
      (partitionChain (Fin n)).jumpTime p i ≤ (partitionChain (Fin n)).jumpTime p j := by
  filter_upwards [ae_jumpTime_eq_clockTime n, ae_jumpHoldLaw_clock_nonneg n]
    with p hT he i j hij hj
  rw [hT i (by omega), hT j hj]
  exact kingmanClockTime_mono n he hij

theorem ae_lineageCountAt_eq (n : ℕ) (τ : ℝ) :
    ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      lineageCountAt n τ p = n - coalescenceCount n τ p := by
  have hae : ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k : ℕ, (p.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown_general n)
  filter_upwards [hae] with p hp
  have hc : coalescenceCount n τ p ≤ n - 1 := by
    have := Finset.card_filter_le (Finset.Ico 1 n)
      (fun m => (partitionChain (Fin n)).jumpTime p m ≤ τ)
    rw [Nat.card_Ico] at this
    exact this
  rw [lineageCountAt, hp]
  omega

/-- Source: tavare1984, eq. (6.1), p. 132; bryant_etal2011_exact_likelihoods, sec. 2, eq. (2). -/
theorem jumpHoldLaw_real_levelEvent (n : ℕ) {m : ℕ} (hm : m < n) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).real (levelEvent n τ m) =
      lineageLaw n τ (n - m) := by
  by_cases hm1 : m + 1 < n
  · have h : levelEvent n τ m = {p | (partitionChain (Fin n)).jumpTime p m ≤ τ ∧
        τ < (partitionChain (Fin n)).jumpTime p (m + 1)} := by
      ext p
      simp [levelEvent, hm1]
    rw [h, jumpHoldLaw_real_lineageCount n hm1 hτ]
  · have h : levelEvent n τ m = {p | (partitionChain (Fin n)).jumpTime p m ≤ τ} := by
      ext p
      simp [levelEvent, hm1]
    rw [h, jumpHoldLaw_real_jumpTime_le n hm hτ, lineageCdf]
    obtain rfl : n = m + 1 := by omega
    have hrow := (blockChain (m + 1)).semigroup_row_sum τ (Fin.last (m + 1))
    simp only [blockChain_semigroup_last_eq_lineageLaw (m + 1) (by omega) τ] at hrow
    rw [Fin.sum_univ_eq_sum_range (fun j => lineageLaw (m + 1) τ j) (m + 1 + 1),
      ← Finset.sum_range_reflect, Finset.sum_range_succ, Finset.sum_range_succ] at hrow
    have h0 : lineageLaw (m + 1) τ 0 = 0 := by simp [lineageLaw]
    simp only [Nat.add_sub_cancel, Nat.sub_self, h0, add_zero] at hrow
    linarith

/--
Source: tavare1984, eq. (3.8), (6.1), pp. 126, 132; bryant_etal2011_exact_likelihoods, sec. 2, eq.
(2). -/
theorem integral_lineageCountAt (n : ℕ) (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) (F : ℕ → ℝ) :
    ∫ p, F (lineageCountAt n τ p) ∂((partitionChain (Fin n)).jumpHoldLaw ⊥) =
      ∑ j : Fin (n + 1), (blockChain n).semigroup τ (Fin.last n) j * F j := by
  have hpt : ∀ᵐ p ∂((partitionChain (Fin n)).jumpHoldLaw ⊥), F (lineageCountAt n τ p) =
      ∑ m ∈ Finset.range n, (levelEvent n τ m).indicator (fun _ => F (n - m)) p := by
    filter_upwards [ae_jumpTime_monotone n, ae_lineageCountAt_eq n τ] with p hmono hL
    obtain ⟨m, hm, hpm⟩ := exists_mem_levelEvent hn hτ p
    have hc := coalescenceCount_eq_of_mem hmono hm hpm
    rw [hL, hc, Finset.sum_eq_single m]
    · rw [Set.indicator_of_mem hpm]
    · intro m' hm' hne
      rw [Set.indicator_of_notMem]
      intro hp'
      exact hne ((coalescenceCount_eq_of_mem hmono (Finset.mem_range.1 hm') hp').symm.trans hc)
    · intro h
      exact absurd (Finset.mem_range.2 hm) h
  rw [integral_congr_ae hpt, integral_finsetSum]
  · simp_rw [integral_indicator_const _ (measurableSet_levelEvent n τ _)]
    rw [Finset.sum_congr rfl fun m hm => by
      rw [jumpHoldLaw_real_levelEvent n (Finset.mem_range.1 hm) hτ, smul_eq_mul]]
    have h0 : lineageLaw n τ 0 = 0 := by simp [lineageLaw]
    have hR : ∑ j ∈ Finset.range (n + 1), lineageLaw n τ j * F j =
        ∑ m ∈ Finset.range n, lineageLaw n τ (n - m) * F (n - m) := by
      rw [← Finset.sum_range_reflect (fun j => lineageLaw n τ j * F j) (n + 1),
        Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, h0, zero_mul, add_zero]
    simp only [blockChain_semigroup_last_eq_lineageLaw n hn τ]
    rw [Fin.sum_univ_eq_sum_range (fun j => lineageLaw n τ j * F j) (n + 1), hR]
  · intro m _
    exact (integrable_const _).indicator (measurableSet_levelEvent n τ m)

/-- Source: tavare1984, eq. (6.1), p. 132. -/
theorem blockChain_semigroup_eq_lineageLaw (n : ℕ) {x : ℕ} (hx1 : 1 ≤ x) (hxn : x ≤ n)
    (t : ℝ) (j : Fin (n + 1)) :
    (blockChain n).semigroup t ⟨x, by omega⟩ j = lineageLaw x t j := by
  have hf : ∀ t (y : Fin (n + 1)), HasDerivAt (fun s => lineageLaw x s (y : ℕ))
      (∑ z : Fin (n + 1), lineageLaw x t z * (blockChain n).Q z y) t := by
    intro t y
    rw [blockChain_Q, sum_mul_blockQ n (lineageLaw x t) y]
    by_cases hyx : (y : ℕ) ≤ x
    · have h := hasDerivAt_lineageLaw x y hyx t
      by_cases hy : (y : ℕ) + 1 ≤ n
      · rw [ite_eq_left hy]
        exact h
      · have hz : lineageLaw x t ((y : ℕ) + 1) = 0 := by
          unfold lineageLaw
          rw [ite_eq_left (by omega), Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        rw [hz, zero_mul] at h
        rw [ite_eq_right hy]
        exact h
    · have hz : ∀ s, lineageLaw x s (y : ℕ) = 0 := fun s => by
        unfold lineageLaw
        split_ifs
        · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        · rfl
      have hz1 : lineageLaw x t ((y : ℕ) + 1) = 0 := by
        unfold lineageLaw
        rw [ite_eq_left (by omega), Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp only [hz, hz1, zero_mul, ite_self, sub_self]
      exact hasDerivAt_const t (0 : ℝ)
  have h0 : ∀ z : Fin (n + 1),
      lineageLaw x 0 z = if z = (⟨x, by omega⟩ : Fin (n + 1)) then 1 else 0 := by
    intro z
    have hiff : z = (⟨x, by omega⟩ : Fin (n + 1)) ↔ (z : ℕ) = x := Fin.ext_iff
    by_cases hzx : (z : ℕ) = x
    · rw [ite_eq_left (hiff.2 hzx), hzx, lineageLaw_zero x hx1 le_rfl, ite_eq_left rfl]
    · rw [ite_eq_right (fun h => hzx (hiff.1 h))]
      by_cases hz1 : 1 ≤ (z : ℕ)
      · by_cases hzx' : (z : ℕ) ≤ x
        · rw [lineageLaw_zero x hz1 hzx', ite_eq_right hzx]
        · unfold lineageLaw
          rw [ite_eq_left hz1, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      · unfold lineageLaw
        rw [ite_eq_right hz1]
  have h := (blockChain n).eq_sum_semigroup_of_forward (fun s y => lineageLaw x s y) hf t j
  rw [h]
  simp [h0]

end Rhone.Coalescent

end
