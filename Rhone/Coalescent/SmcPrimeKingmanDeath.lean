/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanClock

/-! # Every non-root lineage identifier has a unique later removal event -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_root_uid_present_eq (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 2 ≤ N)
    (a : ℕ) (ha : ∃ i, ((ω (N - 1)).1.2.2.2 i).1 = a) : a = 2 * N - 2 := by
  classical
  let k := N - 2
  have hk : k < N := by omega
  have hc := kingman_path_count N ω hinit hstep k hk
  have hc' : (ω k).1.2.2.1 = 2 := by omega
  have hm : 2 ≤ (ω k).1.2.2.1 := by omega
  obtain ⟨ij, hij, hj, _, he, _⟩ := (ite_eq_left hm).mp (hstep k)
  change ij.2 < (ω k).1.2.2.1 at hj
  have hi : ij.1 < (ω k).1.2.2.1 := lt_trans hij hj
  have he' : (ω (k + 1)).1 =
      atTime (ω (k + 1)).1.1 (coalSuccessor (ω k).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
    simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
  have hindex : N - 1 = k + 1 := by omega
  rw [hindex, he'] at ha
  change ∃ i, ((coalSuccessor (ω k).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩).2.2.2 i).1 = a at ha
  rcases (coalSuccessor_uid_present (ω k).1 (hvalid k)
    ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij a).mp ha with hnew | ⟨⟨v, hva⟩, hni, hnj⟩
  · have hf := kingman_path_fresh N ω hinit hstep k hk
    omega
  · have hv : v.val < 2 := by have := v.isLt; omega
    have hij0 : ij.1 = 0 := by omega
    have hij1 : ij.2 = 1 := by omega
    have hvi : v = ⟨ij.1, hi⟩ ∨ v = ⟨ij.2, hj⟩ := by
      by_cases hv0 : v.val = 0
      · left
        apply Fin.ext
        change v.val = ij.1
        omega
      · right
        apply Fin.ext
        change v.val = ij.2
        omega
    rcases hvi with hvi | hvj
    · subst v
      exact False.elim (hni hva.symm)
    · subst v
      exact False.elim (hnj hva.symm)

theorem kingman_uid_death (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N - 1)
    (ha : ∃ i, ((ω k).1.2.2.2 i).1 = a) :
    ∃ m, k ≤ m ∧ m < N - 1 ∧ (∃ i, ((ω m).1.2.2.2 i).1 = a) ∧
      ¬ (∃ i, ((ω (m + 1)).1.2.2.2 i).1 = a) := by
  classical
  have hN : 2 ≤ N := by omega
  have haf : a < (ω k).1.2.1 := by
    obtain ⟨i, hi⟩ := ha
    rw [← hi]
    exact (hvalid k).2.2.1 i
  have hf := kingman_path_fresh N ω hinit hstep k (by omega)
  have hroot : ¬ (∃ i, ((ω (N - 1)).1.2.2.2 i).1 = a) := by
    intro h
    have he := kingman_root_uid_present_eq N ω hinit hvalid hstep hN a h
    omega
  have hex : ∃ j, k ≤ j ∧ j ≤ N - 1 ∧ ¬ (∃ i, ((ω j).1.2.2.2 i).1 = a) :=
    ⟨N - 1, by omega, le_rfl, hroot⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change k ≤ j ∧ j ≤ N - 1 ∧ ¬ (∃ i, ((ω j).1.2.2.2 i).1 = a) at hj
  have hjk : k < j := by
    have hj0 : k ≤ j := hj.1
    by_contra h
    have he : j = k := by omega
    apply hj.2.2
    rw [he]
    exact ha
  have hpre : ∃ i, ((ω (j - 1)).1.2.2.2 i).1 = a := by
    by_contra hn
    have hmin := Nat.find_min' hex (show k ≤ j - 1 ∧ j - 1 ≤ N - 1 ∧
        ¬ (∃ i, ((ω (j - 1)).1.2.2.2 i).1 = a) from ⟨by omega, by omega, hn⟩)
    change j ≤ j - 1 at hmin
    omega
  refine ⟨j - 1, by omega, by omega, hpre, ?_⟩
  have he : j - 1 + 1 = j := by omega
  rw [he]
  exact hj.2.2

theorem kingman_uid_death_parent (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N - 1)
    (ha : ∃ i, ((ω k).1.2.2.2 i).1 = a) :
    ∃ m, k ≤ m ∧ m < N - 1 ∧ ∃ ij : ℕ × ℕ,
      (ω (m + 1)).2.2 = .inr (.inl ij) ∧ ij.1 < ij.2 ∧ ij.2 < (ω m).1.2.2.1 ∧
      (liveLabelAt (ω m).1 ij.1 = a ∨ liveLabelAt (ω m).1 ij.2 = a) := by
  classical
  obtain ⟨m, hkm, hmN, hpre, hn⟩ := kingman_uid_death N ω hinit hvalid hstep k a hk ha
  have hc := kingman_path_count N ω hinit hstep m (by omega)
  have hm : 2 ≤ (ω m).1.2.2.1 := by omega
  obtain ⟨ij, hij, hj, hev, he, _⟩ := (ite_eq_left hm).mp (hstep m)
  change (ω (m + 1)).2.2 = .inr (.inl ij) at hev
  change ij.2 < (ω m).1.2.2.1 at hj
  have hi : ij.1 < (ω m).1.2.2.1 := lt_trans hij hj
  have he' : (ω (m + 1)).1 =
      atTime (ω (m + 1)).1.1 (coalSuccessor (ω m).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
    simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
  have hhit : a = ((ω m).1.2.2.2 ⟨ij.1, hi⟩).1 ∨
      a = ((ω m).1.2.2.2 ⟨ij.2, hj⟩).1 := by
    by_contra hh
    have hni : a ≠ ((ω m).1.2.2.2 ⟨ij.1, hi⟩).1 := fun h => hh (Or.inl h)
    have hnj : a ≠ ((ω m).1.2.2.2 ⟨ij.2, hj⟩).1 := fun h => hh (Or.inr h)
    have hp := (coalSuccessor_uid_present (ω m).1 (hvalid m)
      ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij a).mpr (Or.inr ⟨hpre, hni, hnj⟩)
    apply hn
    rw [he']
    exact hp
  refine ⟨m, hkm, hmN, ij, hev, hij, hj, ?_⟩
  simp only [liveLabelAt, dite_eq_left hi, dite_eq_left hj]
  exact hhit.imp Eq.symm Eq.symm

end Rhone.Coalescent.SmcPrime
