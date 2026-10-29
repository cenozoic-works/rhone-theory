/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanActive
public import Rhone.Coalescent.SmcPrimeKingmanRoot

/-! # Sample clades of Kingman histories: partition, coarsening, and epochs -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

noncomputable def kingmanSampleClades (N : ℕ) (ω : EventPath) (k : ℕ) :
    Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.image (fun i => Finset.univ.filter
    (fun j => ancestorLabel N ω leftBoundaryProbe j k = ancestorLabel N ω leftBoundaryProbe i k))

theorem kingmanSampleClades_partition (N : ℕ) (ω : EventPath) (k : ℕ) :
    (∀ c ∈ kingmanSampleClades N ω k, c ≠ ∅) ∧
    (∀ i : Fin N, ∃ c ∈ kingmanSampleClades N ω k, i ∈ c) ∧
    (∀ c ∈ kingmanSampleClades N ω k, ∀ d ∈ kingmanSampleClades N ω k,
      c ≠ d → Disjoint c d) := by
  classical
  have hmem (i : Fin N) : i ∈ Finset.univ.filter
      (fun j => ancestorLabel N ω leftBoundaryProbe j k =
        ancestorLabel N ω leftBoundaryProbe i k) := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.nonempty_iff_ne_empty.mp ⟨i, hmem i⟩
  · intro i
    exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hmem i⟩
  · intro c hc d hd hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have he : ancestorLabel N ω leftBoundaryProbe i k = ancestorLabel N ω leftBoundaryProbe j k :=
      (Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2
    exact hne (by simp only [he])

theorem kingmanSampleClades_coarsen (N : ℕ) (ω : EventPath) (k l : ℕ) (hkl : k ≤ l)
    (c : Finset (Fin N)) (hc : c ∈ kingmanSampleClades N ω k) :
    ∃ d ∈ kingmanSampleClades N ω l, c ⊆ d := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  refine ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ancestorLabel_equal_later N ω leftBoundaryProbe j i k l hkl hj

theorem kingman_timeClades_epoch (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N - 1)
    (q : ℝ) (hlo : (ω k).1.1 ≤ q) (hhi : q < (ω (k + 1)).1.1) :
    timeClades (metricTreeFromHistory N (fun j : Fin N => ω j.val)) q =
      kingmanSampleClades N ω k := by
  classical
  have hroot := metric_tree_root_height N ω hinit hvalid hstep (by omega)
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hqr : q < rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) := by
    rw [hroot]
    exact hhi.trans_le (hmono (by omega))
  simp only [timeClades, not_le.mpr hqr, ite_false]
  ext c
  constructor
  · intro hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a, ⟨v, hv⟩, he⟩ := kingman_active_live N ω hinit hvalid hstep k hk q hlo hhi i hi
    obtain ⟨j, hj⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep k v
    rw [hv] at hj
    rw [he, historyClade_of_path N ω k a (by omega)]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp only [hj]⟩
  · intro hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i, hi, he⟩ := kingman_live_active N ω hinit hvalid hstep k
      (ancestorLabel N ω leftBoundaryProbe j k) hk
      (kingman_sample_present N ω hinit hvalid hstep j k) q hlo hhi
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    rw [he, historyClade_of_path N ω k _ (by omega)]

theorem kingman_clock_epoch (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (q : ℝ) (hq : 0 ≤ q)
    (hroot : q < (ω (N - 1)).1.1) :
    ∃ k, k < N - 1 ∧ (ω k).1.1 ≤ q ∧ q < (ω (k + 1)).1.1 := by
  classical
  have hex : ∃ j, j ≤ N - 1 ∧ q < (ω j).1.1 := ⟨N - 1, le_rfl, hroot⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change j ≤ N - 1 ∧ q < (ω j).1.1 at hj
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    have hztime : (ω 0).1.1 = 0 := by rw [hinit]; rfl
    rw [hz, hztime] at hj
    exact (not_lt_of_ge hq) hj.2
  have hp : (ω (j - 1)).1.1 ≤ q := by
    by_contra hn
    have hh : j - 1 ≤ N - 1 ∧ q < (ω (j - 1)).1.1 := ⟨by omega, lt_of_not_ge hn⟩
    have hmin := Nat.find_min' hex hh
    change j ≤ j - 1 at hmin
    omega
  refine ⟨j - 1, by omega, hp, ?_⟩
  have he : j - 1 + 1 = j := by omega
  rw [he]
  exact hj.2

theorem metric_tree_root_height_of_pos (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 0 < N) :
    rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) = (ω (N - 1)).1.1 := by
  by_cases hN2 : 2 ≤ N
  · exact metric_tree_root_height N ω hinit hvalid hstep hN2
  · have hn : N = 1 := by omega
    subst N
    have ht : (ω 0).1.1 = 0 := by rw [hinit]; rfl
    rw [show 1 - 1 = 0 from rfl, ht]
    change rootHeight (treeOfList ([] : List (Branch 1))) = 0
    rfl

end Rhone.Coalescent.SmcPrime
