/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanUnique
public import Rhone.Coalescent.SmcPrimeActiveUniqueMeas

/-! # Active branch indices of the Kingman initial tree are unique -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

theorem kingman_active_uid_data (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N - 1)
    (q : ℝ) (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1)
    (i : Fin (metricTreeFromHistory N (fun j : Fin N => ω j.val)).1)
    (hi : i ∈ activeBranches (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q) :
    ∃ m : Fin (N - 1), ∃ a, k ≤ m.val ∧
      (∃ v, ((ω k).1.2.2.2 v).1 = a) ∧
      (∃ v, ((ω m.val).1.2.2.2 v).1 = a) ∧
      ¬ (∃ v, ((ω (m.val + 1)).1.2.2.2 v).1 = a) ∧
      (metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i =
        (historyClade N (fun j : Fin N => ω j.val) k a,
          pairBirthTime ω k a, (ω (m.val + 1)).1.1) := by
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
  have hcl : historyClade N (fun j : Fin N => ω j.val) m.val a =
      historyClade N (fun j : Fin N => ω j.val) k a := by
    rw [historyClade_of_path N ω m.val a (by have := m.isLt; omega),
      historyClade_of_path N ω k a (by omega)]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact kingman_sample_descendants_persist N ω hvalid hstep k m.val a hkm hafk ha j
  have hdies := kingman_child_uid_dies N ω hinit hvalid hstep m r a
    (congrArg Prod.fst hdata)
  have hb := kingman_birth_persist N ω hinit hstep k m.val a hkm
    (by have := m.isLt; omega) haBorn
  refine ⟨m, a, hkm, hap, ha, hdies, ?_⟩
  rw [hm, hdata, hcl, hb]

theorem metric_tree_active_unique (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 0 < N) :
    TreeActiveUnique (metricTreeFromHistory N (fun j : Fin N => ω j.val)) := by
  classical
  intro q hq i hi j hj he
  have hiper : 0 < branchLength ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i) ∧
      ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i).2.1 ≤ q ∧
      q < ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i).2.2 := by
    simpa only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hroot : q < (ω (N - 1)).1.1 := by
    rw [← metric_tree_root_height_of_pos N ω hinit hvalid hstep hN]
    exact hiper.2.2.trans_le (branch_hi_le_root _ i hiper.1)
  obtain ⟨k, hk, hlo, hhi⟩ := kingman_clock_epoch N ω hinit q hq hroot
  obtain ⟨m, a, hkm, hak, ham, hda, hia⟩ :=
    kingman_active_uid_data N ω hinit hvalid hstep k hk q hlo hhi i hi
  obtain ⟨l, b, hkl, hbk, hbl, hdb, hjb⟩ :=
    kingman_active_uid_data N ω hinit hvalid hstep k hk q hlo hhi j hj
  have hab : a = b := by
    obtain ⟨v, hva⟩ := hak
    obtain ⟨u, hua⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep k v
    rw [hva] at hua
    have hmem : u ∈ historyClade N (fun j : Fin N => ω j.val) k a := by
      rw [historyClade_of_path N ω k a (by omega)]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hua⟩
    rw [hia, hjb] at he
    change historyClade N (fun j : Fin N => ω j.val) k a =
      historyClade N (fun j : Fin N => ω j.val) k b at he
    rw [he, historyClade_of_path N ω k b (by omega)] at hmem
    exact hua.symm.trans (Finset.mem_filter.mp hmem).2
  subst b
  have hfmono : Monotone (fun k => (ω k).1.2.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).fresh_le)
  have haf : a < (ω k).1.2.1 := by
    obtain ⟨v, hv⟩ := hak
    rw [← hv]
    exact (hvalid k).2.2.1 v
  have hml : m = l := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact hda (kingman_uid_present_earlier ω hvalid hstep (m.val + 1) l.val a
        (by omega) (haf.trans_le (hfmono (by omega))) hbl)
    · exact hdb (kingman_uid_present_earlier ω hvalid hstep (l.val + 1) m.val a
        (by omega) (haf.trans_le (hfmono (by omega))) ham)
  apply kingman_tree_branch_injective N ω hinit hvalid hstep
  rw [hia, hjb, hml]

theorem kingman_live_active_unique (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N - 1)
    (ha : ∃ v, ((ω k).1.2.2.2 v).1 = a) (q : ℝ)
    (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1) :
    ∃! i, i ∈ activeBranches (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q ∧
      ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 i).1 =
        historyClade N (fun j : Fin N => ω j.val) k a := by
  obtain ⟨i, hi, hc⟩ := kingman_live_active N ω hinit hvalid hstep k a hk ha q hlo hhi
  refine ⟨i, ⟨hi, hc⟩, ?_⟩
  intro j hj
  exact metric_tree_active_unique N ω hinit hvalid hstep (by omega)
    q ((hvalid k).1.trans hlo) j hj.1 i hi (hj.2.trans hc.symm)

theorem metric_tree_from_history_active_unique (N : ℕ) (h : KingmanHistory N)
    (hN : 0 < N) (hs : KingmanHistorySupported N h) :
    TreeActiveUnique (metricTreeFromHistory N h) := by
  have he : (fun j : Fin N => kingmanCompletion N h j.val) = h := by
    funext j
    exact kingmanCompletion_prefix N h j.val j.isLt
  have hu := metric_tree_active_unique N (kingmanCompletion N h)
    hs.completion_init hs.completion_valid hs.completion_step hN
  rw [he] at hu
  exact hu

theorem kingmanHistoryLaw_tree_active_unique (N : ℕ) (hN : 0 < N) :
    ∀ᵐ h ∂kingmanHistoryLaw N, TreeActiveUnique (metricTreeFromHistory N h) := by
  filter_upwards [kingmanHistoryLaw_supported N] with h hs
  exact metric_tree_from_history_active_unique N h hN hs

theorem kingmanTreeLaw_active_unique (N : ℕ) (hN : 0 < N) :
    ∀ᵐ T ∂kingmanTreeLaw N, TreeActiveUnique T := by
  unfold kingmanTreeLaw
  exact (ae_map_iff (metricTreeFromHistory_measurable N).aemeasurable
    (TreeActiveUnique_measurable N)).mpr (kingmanHistoryLaw_tree_active_unique N hN)

end Rhone.Coalescent.SmcPrime
