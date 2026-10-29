/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanInventory

/-! # Active child branches identify exactly the contemporaneous live UID clades -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_live_active (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N - 1)
    (ha : ∃ v, ((ω k).1.2.2.2 v).1 = a) (q : ℝ)
    (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1) :
    ∃ i ∈ activeBranches (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q,
      ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i).1 =
        historyClade N (fun j : Fin N => ω j.val) k a := by
  classical
  obtain ⟨m, r, hkm, hm⟩ := kingman_live_child N ω hinit hvalid hstep k a hk ha
  obtain ⟨i, hi⟩ := historyChildBranch_mem_tree N (fun j : Fin N => ω j.val) m r
  have hp := (history_child_branch_positive N ω hinit hvalid hstep m r).1
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hb := pair_birth_time_le_current_time ω (hvalid 0).1 hmono k a
  refine ⟨i, ?_, ?_⟩
  · simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, hi]
    refine ⟨hp, ?_, ?_⟩
    · rw [hm]
      exact hb.trans hlo
    · rw [hm]
      exact hhi.trans_le (hmono (by omega))
  · rw [hi, hm]

theorem kingman_active_live (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N - 1)
    (q : ℝ) (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1)
    (i : Fin (metricTreeFromHistory N (fun j : Fin N => ω j.val)).1)
    (hi : i ∈ activeBranches (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q) :
    ∃ a, (∃ v, ((ω k).1.2.2.2 v).1 = a) ∧
      ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i).1 =
        historyClade N (fun j : Fin N => ω j.val) k a := by
  classical
  obtain ⟨m, r, hm⟩ := metric_tree_branch_from_child N (fun j : Fin N => ω j.val) i
  obtain ⟨a, ha, hdata⟩ := kingman_child_data N ω hinit hvalid hstep m r
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, hm, hdata] at hi
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hkm : k ≤ m.val := by
    by_contra h
    have hmk : m.val + 1 ≤ k := by omega
    have := hmono hmk
    exact (not_lt_of_ge (this.trans hlo)) hi.2.2
  have haf : a < (ω m.val).1.2.1 := by
    obtain ⟨v, hv⟩ := ha
    rw [← hv]
    exact (hvalid m.val).2.2.1 v
  have hf := kingman_path_fresh N ω hinit hstep m.val (by have := m.isLt; omega)
  have haBorn : a < N + k := by
    by_contra hn
    have hacond : N ≤ a ∧ a < N + m.val := by omega
    have htindex : k + 1 ≤ a - N + 1 := by omega
    have hb := kingman_pair_birth_time N ω hinit hstep m.val a (by have := m.isLt; omega)
    rw [ite_eq_left hacond] at hb
    have hbirthle := hi.2.1
    rw [hb] at hbirthle
    have := hmono htindex
    exact (not_lt_of_ge (this.trans hbirthle)) hhi
  have hafk : a < (ω k).1.2.1 := by
    rw [kingman_path_fresh N ω hinit hstep k (by omega)]
    exact haBorn
  have hap := kingman_uid_present_earlier ω hvalid hstep k m.val a hkm hafk ha
  refine ⟨a, hap, ?_⟩
  rw [hm, hdata, historyClade_of_path N ω m.val a (by have := m.isLt; omega),
    historyClade_of_path N ω k a (by omega)]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact kingman_sample_descendants_persist N ω hvalid hstep k m.val a hkm hafk ha j

end Rhone.Coalescent.SmcPrime
