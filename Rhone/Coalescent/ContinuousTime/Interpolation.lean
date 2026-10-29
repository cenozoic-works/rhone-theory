/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTimeGenealogy.Holding

/-! # Real-time interpolation of the killed ARG -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTime

open Finset MeasureTheory TypedAncestralChain BranchLengthMoments ContinuousTimeGenealogy

variable {n KA KB : ℕ} {θA θB ρ : ℝ}

noncomputable def holding (θA θB ρ : ℝ) (z : CtPath n KA KB) (k : ℕ) : ℝ :=
  max 0 (holdTime θA θB ρ z k)

noncomputable def arrival (θA θB ρ : ℝ) (z : CtPath n KA KB) (k : ℕ) : ℝ :=
  ∑ j ∈ range k, holding θA θB ρ z j

@[simp] theorem arrival_zero (z : CtPath n KA KB) : arrival θA θB ρ z 0 = 0 := by
  simp [arrival]

theorem arrival_succ (z : CtPath n KA KB) (k : ℕ) :
    arrival θA θB ρ z (k + 1) = arrival θA θB ρ z k + holding θA θB ρ z k := by
  exact sum_range_succ _ _

theorem arrival_nonneg (z : CtPath n KA KB) (k : ℕ) :
    0 ≤ arrival θA θB ρ z k := by
  exact sum_nonneg fun _ _ => le_max_left _ _

theorem arrival_mono (z : CtPath n KA KB) : Monotone (arrival θA θB ρ z) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [arrival_succ]
  exact le_add_of_nonneg_right (le_max_left _ _)

noncomputable def timeIndex (θA θB ρ : ℝ) (z : CtPath n KA KB) (t : ℝ) : ℕ :=
  ((range (absTime z.1 + 1)).filter (fun k => arrival θA θB ρ z k ≤ t)).sup id

noncomputable def process (θA θB ρ : ℝ) (z : CtPath n KA KB) (t : ℝ) : TS n KA KB :=
  z.1 (timeIndex θA θB ρ z t)

theorem timeIndex_le (z : CtPath n KA KB) (t : ℝ) :
    timeIndex θA θB ρ z t ≤ absTime z.1 := by
  apply Finset.sup_le
  intro k hk
  have hk' := mem_range.mp (mem_filter.mp hk).1
  exact Nat.le_of_lt_succ hk'

theorem timeIndex_at_absorption (z : CtPath n KA KB) {t : ℝ}
    (ht : arrival θA θB ρ z (absTime z.1) ≤ t) :
    timeIndex θA θB ρ z t = absTime z.1 := by
  apply le_antisymm (timeIndex_le z t)
  exact le_sup (f := id) (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self _), ht⟩)

theorem timeIndex_on_interval (z : CtPath n KA KB) {k : ℕ} (hk : k ≤ absTime z.1)
    {t : ℝ} (hlo : arrival θA θB ρ z k ≤ t)
    (hhi : t < arrival θA θB ρ z (k + 1)) : timeIndex θA θB ρ z t = k := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    change j ≤ k
    have hjt := (mem_filter.mp hj).2
    by_contra hjk
    have hjk' : k + 1 ≤ j := by omega
    exact (not_le.mpr hhi) ((arrival_mono z hjk').trans hjt)
  · exact le_sup (f := id) (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hk), hlo⟩)

theorem process_on_interval (z : CtPath n KA KB) {k : ℕ} (hk : k ≤ absTime z.1)
    {t : ℝ} (hlo : arrival θA θB ρ z k ≤ t)
    (hhi : t < arrival θA θB ρ z (k + 1)) : process θA θB ρ z t = z.1 k := by
  rw [process, timeIndex_on_interval z hk hlo hhi]

theorem arrival_timeIndex_le (z : CtPath n KA KB) {t : ℝ} (ht : 0 ≤ t) :
    arrival θA θB ρ z (timeIndex θA θB ρ z t) ≤ t := by
  let S := (range (absTime z.1 + 1)).filter (fun k => arrival θA θB ρ z k ≤ t)
  have hS : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ _),
    by simpa using ht⟩⟩
  obtain ⟨j, hj, hjindex⟩ := Finset.sup_mem_of_nonempty (f := id) hS
  have hjt := (mem_filter.mp hj).2
  change j = timeIndex θA θB ρ z t at hjindex
  rw [← hjindex]
  exact hjt

theorem timeIndex_next_arrival (z : CtPath n KA KB) {t : ℝ}
    (hk : timeIndex θA θB ρ z t < absTime z.1) :
    t < arrival θA θB ρ z (timeIndex θA θB ρ z t + 1) := by
  by_contra hfuture
  have hm : timeIndex θA θB ρ z t + 1 ∈
      (range (absTime z.1 + 1)).filter (fun k => arrival θA θB ρ z k ≤ t) :=
    mem_filter.mpr ⟨mem_range.mpr (by omega), le_of_not_gt hfuture⟩
  have hh := le_sup (f := id) hm
  change timeIndex θA θB ρ z t + 1 ≤ timeIndex θA θB ρ z t at hh
  omega

theorem process_after_absorption (z : CtPath n KA KB) {t : ℝ}
    (ht : arrival θA θB ρ z (absTime z.1) ≤ t) :
    process θA θB ρ z t = z.1 (absTime z.1) := by
  rw [process, timeIndex_at_absorption z ht]

theorem process_locally_constant_right (z : CtPath n KA KB) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, t ≤ u → u < t + ε →
      process θA θB ρ z u = process θA θB ρ z t := by
  have hlo := arrival_timeIndex_le (θA := θA) (θB := θB) (ρ := ρ) z ht
  by_cases hk : timeIndex θA θB ρ z t < absTime z.1
  · have hhi := timeIndex_next_arrival z hk
    refine ⟨arrival θA θB ρ z (timeIndex θA θB ρ z t + 1) - t,
      sub_pos.mpr hhi, fun u htu hu => ?_⟩
    have hu' : u < arrival θA θB ρ z (timeIndex θA θB ρ z t + 1) := by linarith
    exact process_on_interval z (timeIndex_le z t) (hlo.trans htu) hu'
  · have hidx : timeIndex θA θB ρ z t = absTime z.1 := by
      have := timeIndex_le (θA := θA) (θB := θB) (ρ := ρ) z t
      omega
    rw [hidx] at hlo
    refine ⟨1, zero_lt_one, fun u htu _ => ?_⟩
    rw [process_after_absorption z (hlo.trans htu), process_after_absorption z hlo]

theorem process_locally_constant_left (z : CtPath n KA KB) {t : ℝ} (ht : 0 < t) :
    ∃ y : TS n KA KB, ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, t - ε < u → u < t →
      process θA θB ρ z u = y := by
  let S := (range (absTime z.1 + 1)).filter (fun k => arrival θA θB ρ z k < t)
  let k := S.sup id
  have hS : S.Nonempty := ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ _),
    by simpa using ht⟩⟩
  obtain ⟨j, hj, hjk⟩ := Finset.sup_mem_of_nonempty (f := id) hS
  change j = k at hjk
  have hkarr : arrival θA θB ρ z k < t := by
    have hjt := (mem_filter.mp hj).2
    rw [← hjk]
    exact hjt
  have hkT : k ≤ absTime z.1 := by
    apply Finset.sup_le
    intro j hj
    exact Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hj).1)
  refine ⟨z.1 k, t - arrival θA θB ρ z k, sub_pos.mpr hkarr, fun u hu hut => ?_⟩
  have hku : arrival θA θB ρ z k ≤ u := by linarith
  by_cases hk : k < absTime z.1
  · have hfuture : t ≤ arrival θA θB ρ z (k + 1) := by
      by_contra hc
      have hm : k + 1 ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_not_ge hc⟩
      have hh := le_sup (f := id) hm
      change k + 1 ≤ k at hh
      omega
    exact process_on_interval z hkT hku (hut.trans_le hfuture)
  · have hfinal : k = absTime z.1 := by omega
    rw [hfinal] at hku ⊢
    exact process_after_absorption z hku

theorem process_mem_implies_jump_mem (z : CtPath n KA KB) (E : Set (TS n KA KB))
    {t : ℝ} (ht : process θA θB ρ z t ∈ E) : ∃ k, z.1 k ∈ E :=
  ⟨timeIndex θA θB ρ z t, ht⟩

theorem terminal_mem_implies_process_mem (z : CtPath n KA KB) (E : Set (TS n KA KB))
    (hz : z.1 (absTime z.1) ∈ E) :
    ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E := by
  refine ⟨arrival θA θB ρ z (absTime z.1), arrival_nonneg _ _, ?_⟩
  rw [process_after_absorption z le_rfl]
  exact hz

end Rhone.Coalescent.ContinuousTime
