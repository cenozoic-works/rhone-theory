/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanActiveUnique
public import Rhone.Coalescent.SmcPrimeGenealogyLaw

/-! # The Kingman initial tree has exactly the observed event-path genealogy -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_ancestorLabel_probe (N : ℕ) (ω : EventPath)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1)))
    (q : GenomicProbe) (i : Fin N) (k : ℕ) :
    ancestorLabel N ω q i k = ancestorLabel N ω leftBoundaryProbe i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hm : 2 ≤ (ω k).1.2.2.1
    · obtain ⟨ij, _, _, hev, _, _⟩ := (ite_eq_left hm).mp (hstep k)
      change (ω (k + 1)).2.2 = .inr (.inl ij) at hev
      simp only [ancestorLabel, hev, ancestorStep, ih]
    · obtain ⟨_, hev⟩ := (ite_eq_right hm).mp (hstep k)
      change (ω (k + 1)).2.2 = .inl () at hev
      simp only [ancestorLabel, hev, ancestorStep, ih]

theorem kingman_last_agreement (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 0 < N)
    (i j : Fin N) :
    ancestorLabel N ω leftBoundaryProbe i (N - 1) =
      ancestorLabel N ω leftBoundaryProbe j (N - 1) := by
  obtain ⟨v, hv⟩ := kingman_sample_present N ω hinit hvalid hstep i (N - 1)
  obtain ⟨w, hw⟩ := kingman_sample_present N ω hinit hvalid hstep j (N - 1)
  have hc := kingman_path_count N ω hinit hstep (N - 1) (by omega)
  have he : v = w := by
    apply Fin.ext
    have := v.isLt
    have := w.isLt
    omega
  rw [← hv, ← hw, he]

theorem kingman_genealogy_le_uid_birth (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (m a : ℕ) (hm : m < N)
    (ha : ∃ v, ((ω m).1.2.2.2 v).1 = a) (i j : Fin N)
    (hi : ancestorLabel N ω leftBoundaryProbe i m = a)
    (hj : ancestorLabel N ω leftBoundaryProbe j m = a) :
    genealogyObservation N ω leftBoundaryProbe i j ≤ ENNReal.ofReal (pairBirthTime ω m a) := by
  have haf : a < (ω m).1.2.1 := by
    obtain ⟨v, hv⟩ := ha
    rw [← hv]
    exact (hvalid m).2.2.1 v
  rw [kingman_path_fresh N ω hinit hstep m hm] at haf
  rw [kingman_pair_birth_time N ω hinit hstep m a hm]
  by_cases han : N ≤ a
  · have hb : a - N + 1 ≤ m := by omega
    have haBirth : a < (ω (a - N + 1)).1.2.1 := by
      rw [kingman_path_fresh N ω hinit hstep (a - N + 1) (by omega)]
      omega
    have hei := (kingman_sample_descendants_persist N ω hvalid hstep
      (a - N + 1) m a hb haBirth ha i).mp hi
    have hej := (kingman_sample_descendants_persist N ω hvalid hstep
      (a - N + 1) m a hb haBirth ha j).mp hj
    rw [ite_eq_left (show N ≤ a ∧ a < N + m from ⟨han, haf⟩)]
    exact iInf_le_of_le (a - N + 1) (by simp only [hei, hej, ite_true]; exact le_rfl)
  · have haBirth : a < (ω 0).1.2.1 := by
      rw [hinit]
      change a < N
      omega
    have hei := (kingman_sample_descendants_persist N ω hvalid hstep 0 m a
      (Nat.zero_le m) haBirth ha i).mp hi
    have hej := (kingman_sample_descendants_persist N ω hvalid hstep 0 m a
      (Nat.zero_le m) haBirth ha j).mp hj
    have ht : (ω 0).1.1 = 0 := by rw [hinit]; rfl
    rw [ite_eq_right (show ¬ (N ≤ a ∧ a < N + m) from fun h => han h.1)]
    exact iInf_le_of_le 0 (by simp only [hei, hej, ite_true, ht]; exact le_rfl)

theorem metric_tree_pair_mrca (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 0 < N)
    (q : GenomicProbe) (i j : Fin N) :
    treePairMRCA (metricTreeFromHistory N (fun j : Fin N => ω j.val)) i j =
      genealogyObservation N ω q i j := by
  classical
  have hprobe : genealogyObservation N ω q i j =
      genealogyObservation N ω leftBoundaryProbe i j := by
    simp only [genealogyObservation, kingman_ancestorLabel_probe N ω hstep]
  rw [hprobe]
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hroot := metric_tree_root_height_of_pos N ω hinit hvalid hstep hN
  have hagree := kingman_last_agreement N ω hinit hvalid hstep hN i j
  by_cases hij : i = j
  · subst j
    simp only [treePairMRCA]
    apply le_antisymm zero_le
    have ht : (ω 0).1.1 = 0 := by rw [hinit]; rfl
    exact iInf_le_of_le 0 (by simp only [ht, ENNReal.ofReal_zero]; exact le_rfl)
  · rw [treePairMRCA, ite_eq_right hij]
    apply le_antisymm
    · apply le_iInf
      intro k
      by_cases he : ancestorLabel N ω leftBoundaryProbe i k =
          ancestorLabel N ω leftBoundaryProbe j k
      · simp only [ite_eq_left he]
        by_cases hk : k < N - 1
        · let a := ancestorLabel N ω leftBoundaryProbe i k
          obtain ⟨m, r, _, hm⟩ := kingman_live_child N ω hinit hvalid hstep k a hk
            (kingman_sample_present N ω hinit hvalid hstep i k)
          obtain ⟨b, hb⟩ := historyChildBranch_mem_tree N (fun j : Fin N => ω j.val) m r
          have hpos := (history_child_branch_positive N ω hinit hvalid hstep m r).1
          have hci : i ∈ historyClade N (fun j : Fin N => ω j.val) k a := by
            rw [historyClade_of_path N ω k a (by omega)]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
          have hcj : j ∈ historyClade N (fun j : Fin N => ω j.val) k a := by
            rw [historyClade_of_path N ω k a (by omega)]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, he.symm⟩
          apply le_trans (inf_le_right.trans (iInf_le _ b))
          rw [hb]
          have hcond : i ∈ (historyChildBranch N (fun j : Fin N => ω j.val) m r).1 ∧
              j ∈ (historyChildBranch N (fun j : Fin N => ω j.val) m r).1 ∧
              0 < branchLength (historyChildBranch N (fun j : Fin N => ω j.val) m r) := by
            rw [hm]
            exact ⟨hci, hcj, by rw [← hm]; exact hpos⟩
          rw [ite_eq_left hcond, hm]
          exact ENNReal.ofReal_le_ofReal
            (pair_birth_time_le_current_time ω (hvalid 0).1 hmono k a)
        · apply inf_le_left.trans
          rw [hroot]
          exact ENNReal.ofReal_le_ofReal (hmono (by omega))
      · simp only [ite_eq_right he]
        exact le_top
    · apply le_inf
      · rw [hroot]
        exact iInf_le_of_le (N - 1) (by simp only [ite_eq_left hagree]; exact le_rfl)
      · apply le_iInf
        intro b
        by_cases hcond : i ∈ ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 b).1 ∧
            j ∈ ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 b).1 ∧
            0 < branchLength ((metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 b)
        · rw [ite_eq_left hcond]
          obtain ⟨m, r, hm⟩ := metric_tree_branch_from_child N (fun j : Fin N => ω j.val) b
          obtain ⟨a, ha, hdata⟩ := kingman_child_data N ω hinit hvalid hstep m r
          rw [hm, hdata] at hcond ⊢
          rw [historyClade_of_path N ω m.val a (by have := m.isLt; omega)] at hcond
          exact kingman_genealogy_le_uid_birth N ω hinit hvalid hstep m.val a
            (by have := m.isLt; omega) ha i j (Finset.mem_filter.mp hcond.1).2
            (Finset.mem_filter.mp hcond.2.1).2
        · rw [ite_eq_right hcond]
          exact le_top

theorem metric_tree_from_history_pair_mrca (N : ℕ) (h : KingmanHistory N)
    (hN : 0 < N) (hs : KingmanHistorySupported N h) (q : GenomicProbe) (i j : Fin N) :
    treePairMRCA (metricTreeFromHistory N h) i j =
      genealogyObservation N (kingmanCompletion N h) q i j := by
  have he : (fun j : Fin N => kingmanCompletion N h j.val) = h := by
    funext j
    exact kingmanCompletion_prefix N h j.val j.isLt
  have ho := metric_tree_pair_mrca N (kingmanCompletion N h)
    hs.completion_init hs.completion_valid hs.completion_step hN q i j
  rw [he] at ho
  exact ho

end Rhone.Coalescent.SmcPrime
