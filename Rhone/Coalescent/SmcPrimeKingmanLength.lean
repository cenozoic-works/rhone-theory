/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeKingmanActiveUnique
public import Rhone.Coalescent.SmcPrimeKingmanChronology
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative
public import Rhone.Coalescent.SmcPrimeTreeRootExposure
/-!
# Exact finite Kingman live-count exposure

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess
open scoped BigOperators
theorem kingman_active_branch_card (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N - 1)
    (q : ℝ) (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1) :
    (activeBranches (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q).card =
      (ω k).1.2.2.1 := by
  classical
  let T := metricTreeFromHistory N (fun j : Fin N => ω j.val)
  have hex (v : Fin (ω k).1.2.2.1) := kingman_live_active_unique N ω hinit hvalid hstep
    k ((ω k).1.2.2.2 v).1 hk ⟨v, rfl⟩ q hlo hhi
  let f (v : Fin (ω k).1.2.2.1) : {i // i ∈ activeBranches T q} :=
    ⟨(hex v).exists.choose, (hex v).exists.choose_spec.1⟩
  have hf (v : Fin (ω k).1.2.2.1) : (T.2 (f v).val).1 =
      historyClade N (fun j : Fin N => ω j.val) k ((ω k).1.2.2.2 v).1 :=
    (hex v).exists.choose_spec.2
  have hcl (a b : ℕ) (ha : ∃ v, ((ω k).1.2.2.2 v).1 = a)
      (he : historyClade N (fun j : Fin N => ω j.val) k a =
        historyClade N (fun j : Fin N => ω j.val) k b) : a = b := by
    obtain ⟨v, hv⟩ := ha
    obtain ⟨u, hu⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep k v
    rw [hv] at hu
    have hm : u ∈ historyClade N (fun j : Fin N => ω j.val) k a := by
      rw [historyClade_of_path N ω k a (by omega)]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    rw [he, historyClade_of_path N ω k b (by omega)] at hm
    exact hu.symm.trans (Finset.mem_filter.mp hm).2
  have hinj : Function.Injective f := by
    intro v w he
    apply (hvalid k).2.2.2
    apply hcl _ _ ⟨v, rfl⟩
    rw [← hf v, ← hf w, he]
  have hsurj : Function.Surjective f := by
    intro i
    obtain ⟨a, ⟨v, hv⟩, hc⟩ :=
      kingman_active_live N ω hinit hvalid hstep k hk q hlo hhi i.val i.property
    apply Exists.intro v
    apply Subtype.ext
    apply metric_tree_active_unique N ω hinit hvalid hstep (by omega)
      q ((hvalid k).1.trans hlo) (f v).val (f v).property i.val i.property
    rw [hf v, hv]
    exact hc.symm
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa using hc.symm

theorem metric_tree_length (N : ℕ) (ω : EventPath)
    (hN : 1 ≤ N) (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) :
    treeLength (metricTreeFromHistory N (fun j : Fin N => ω j.val)) =
      ∑ k : Fin (N - 1), ((ω k.val).1.2.2.1 : ℝ) *
        ((ω (k.val + 1)).1.1 - (ω k.val).1.1) := by
  let T := metricTreeFromHistory N (fun j : Fin N => ω j.val)
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hn : TreeNonnegative T := metric_tree_from_history_nonnegative N _
    (fun k => (hvalid k.val).1)
  have hroot := metric_tree_root_height_of_pos N ω hinit hvalid hstep (by omega)
  have hzero : (ω 0).1.1 = 0 := by rw [hinit]; rfl
  have he : treeLength T = attachmentHazard T 0 (ω (N - 1)).1.1 := by
    rw [← hroot, attachment_hazard_root_stem T hn (rootHeight T) le_rfl]
    simp
  rw [he, attachmentHazard, ← hzero,
    ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => attachmentRate_intervalIntegrable T (ω k).1.1 (ω (k + 1)).1.1),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  have hi : (∫ q in (ω k.val).1.1..(ω (k.val + 1)).1.1, attachmentRate T q) =
      ∫ _q in (ω k.val).1.1..(ω (k.val + 1)).1.1, ((ω k.val).1.2.2.1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (ω (k.val + 1)).1.1] with q hneq hmem
    rw [Set.uIoc_of_le (hmono (Nat.le_succ k.val))] at hmem
    have hhi : q < (ω (k.val + 1)).1.1 := lt_of_le_of_ne hmem.2 hneq
    have hqr : q < rootHeight T := by
      rw [hroot]
      exact hhi.trans_le (hmono (by have := k.isLt; omega))
    simp only [attachmentRate, not_le.mpr hqr, ite_false]
    rw [kingman_active_branch_card N ω hinit hvalid hstep k.val k.isLt q hmem.1.le hhi]
  rw [hi, intervalIntegral.integral_const, smul_eq_mul, mul_comm]

theorem metric_tree_from_history_length (N : ℕ) (h : KingmanHistory N)
    (hN : 1 ≤ N) (hs : KingmanHistorySupported N h) :
    treeLength (metricTreeFromHistory N h) =
      ∑ k : Fin (N - 1), ((h ⟨k.val, by omega⟩).1.2.2.1 : ℝ) *
        ((h ⟨k.val + 1, by omega⟩).1.1 - (h ⟨k.val, by omega⟩).1.1) := by
  have hp : (fun j : Fin N => kingmanCompletion N h j.val) = h := by
    funext j
    exact kingmanCompletion_prefix N h j.val j.isLt
  have he := metric_tree_length N (kingmanCompletion N h) hN
    hs.completion_init hs.completion_valid hs.completion_step
  rw [hp] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  rw [kingmanCompletion_prefix N h k.val (by omega),
    kingmanCompletion_prefix N h (k.val + 1) (by omega)]
end Rhone.Coalescent.SmcPrime
