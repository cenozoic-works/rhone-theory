/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Types

/-! # The `A`-marginal of the ancestral recombination graph is the Kingman coalescent -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy

variable {n : ℕ} {ρ : ℝ} {L : Finset (Lin n)} {p q : Lin n}

def stepArg (ρ : ℝ) (g : Finset (Lin n) → ℝ) (L : Finset (Lin n)) : ℝ :=
  (∑ p ∈ L, ∑ q ∈ L.erase p, g (coalL L p q)) + ρ * (∑ p ∈ carC L, g (recL L p))

def dtotArg (ρ : ℝ) (L : Finset (Lin n)) : ℝ :=
  ((L.card * (L.card - 1) : ℕ) : ℝ) + ρ * ((tt L : ℕ) : ℝ)

theorem sum_pairs_const {α : Type*} [DecidableEq α] (L : Finset α) (c : ℝ) :
    (∑ _p ∈ L, ∑ _q ∈ L.erase _p, c) = ((L.card * (L.card - 1) : ℕ) : ℝ) * c := by
  have hin : ∀ p ∈ L, (∑ _q ∈ L.erase p, c) = ((L.card - 1 : ℕ) : ℝ) * c := by
    intro p hp
    rw [Finset.sum_const, Finset.card_erase_of_mem hp, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hin, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

def partA (L : Finset (Lin n)) : Finset (Finset (Fin n)) := (carA L).image Prod.fst

def mergeP (P : Finset (Finset (Fin n))) (S T : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  insert (S ∪ T) ((P.erase S).erase T)

theorem mem_partA {S : Finset (Fin n)} : S ∈ partA L ↔ ∃ p ∈ carA L, p.1 = S := by
  simp [partA]

theorem fst_injOn (hw : WF L) : ∀ p ∈ carA L, ∀ r ∈ carA L, p.1 = r.1 → p = r := by
  intro p hp r hr hpr
  by_contra hne
  obtain ⟨hpL, hp1⟩ := mem_carA.1 hp
  obtain ⟨hrL, _⟩ := mem_carA.1 hr
  obtain ⟨k, hk⟩ := hp1
  have hd := hw.disjA p hpL r hrL hne
  exact (Finset.disjoint_left.1 hd) hk (hpr ▸ hk)

theorem card_partA (hw : WF L) : (partA L).card = na L :=
  Finset.card_image_of_injOn (fun p hp r hr hpr => fst_injOn hw p hp r hr hpr)

theorem image_erase_carA (hw : WF L) {r : Lin n} (hr : r ∈ carA L) :
    ((carA L).erase r).image Prod.fst = (partA L).erase r.1 := by
  ext S
  simp only [Finset.mem_image, Finset.mem_erase, mem_partA]
  constructor
  · rintro ⟨u, ⟨hur, huA⟩, rfl⟩
    exact ⟨fun hc => hur (fst_injOn hw u huA r hr hc), ⟨u, huA, rfl⟩⟩
  · rintro ⟨hSr, ⟨u, huA, rfl⟩⟩
    exact ⟨u, ⟨fun hc => hSr (by rw [hc]), huA⟩, rfl⟩

theorem carA_erase (L : Finset (Lin n)) (r : Lin n) : carA (L.erase r) = (carA L).erase r := by
  ext u
  simp only [mem_carA, Finset.mem_erase]
  tauto

theorem carA_insert_of_nonempty {m : Lin n} (X : Finset (Lin n)) (hm : m.1.Nonempty) :
    carA (insert m X) = insert m (carA X) := by
  ext u
  simp only [mem_carA, Finset.mem_insert]
  constructor
  · rintro ⟨hu | hu, h1⟩
    · exact Or.inl hu
    · exact Or.inr ⟨hu, h1⟩
  · rintro (rfl | ⟨hu, h1⟩)
    · exact ⟨Or.inl rfl, hm⟩
    · exact ⟨Or.inr hu, h1⟩

theorem carA_insert_of_empty {m : Lin n} (X : Finset (Lin n)) (hm : ¬ m.1.Nonempty) :
    carA (insert m X) = carA X := by
  ext u
  simp only [mem_carA, Finset.mem_insert]
  constructor
  · rintro ⟨hu | hu, h1⟩
    · exact absurd (hu ▸ h1) hm
    · exact ⟨hu, h1⟩
  · rintro ⟨hu, h1⟩
    exact ⟨Or.inr hu, h1⟩

theorem partA_coal_both (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p) (h1 : p.1.Nonempty)
    (h2 : q.1.Nonempty) : partA (coalL L p q) = mergeP (partA L) p.1 q.1 := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hpA : p ∈ carA L := mem_carA.2 ⟨hp, h1⟩
  have hqA : q ∈ carA L := mem_carA.2 ⟨hqL, h2⟩
  have hqA' : q ∈ (carA L).erase p := Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hq, hqA⟩
  have hmne : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty :=
    h1.mono Finset.subset_union_left
  have hsub : WF (L.erase p) := hw.erase p
  have e2 : partA (L.erase p) = (partA L).erase p.1 := by
    rw [partA, carA_erase, image_erase_carA hw hpA]
  have hq' : q ∈ carA (L.erase p) := by rw [carA_erase]; exact hqA'
  have e1 : ((carA (L.erase p)).erase q).image Prod.fst
      = ((partA L).erase p.1).erase q.1 := by
    rw [image_erase_carA hsub hq', e2]
  rw [partA, coalL, carA_insert_of_nonempty _ hmne, Finset.image_insert, mergeP,
    carA_erase, e1]

theorem partA_coal_not (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p)
    (h : ¬ (p.1.Nonempty ∧ q.1.Nonempty)) : partA (coalL L p q) = partA L := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hpq : q ≠ p := Finset.ne_of_mem_erase hq
  rcases not_and_or.1 h with h1 | h2
  · have hpe : p.1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 h1
    have hpA : p ∉ carA L := fun hc => h1 (mem_carA.1 hc).2
    by_cases h2 : q.1.Nonempty
    · have hqA : q ∈ carA L := mem_carA.2 ⟨hqL, h2⟩
      have hmne : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty :=
        h2.mono Finset.subset_union_right
      have hun : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1 = q.1 := by
        simp only [hpe, Finset.empty_union]
      rw [partA, coalL, carA_insert_of_nonempty _ hmne, carA_erase, carA_erase,
        Finset.image_insert, hun,
        show ((carA L).erase p).erase q = (carA L).erase q by
          rw [Finset.erase_right_comm, Finset.erase_eq_of_notMem
            (fun hc => hpA (Finset.mem_of_mem_erase hc))],
        image_erase_carA hw hqA, Finset.insert_erase (mem_partA.2 ⟨q, hqA, rfl⟩)]
    · have hqe : q.1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 h2
      have hqA : q ∉ carA L := fun hc => h2 (mem_carA.1 hc).2
      have hmne : ¬ ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty := by
        simp [hpe, hqe]
      rw [partA, coalL, carA_insert_of_empty _ hmne, carA_erase, carA_erase,
        Finset.erase_eq_of_notMem (fun hc => hqA (Finset.mem_of_mem_erase hc)),
        Finset.erase_eq_of_notMem hpA, partA]
  · have hqe : q.1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 h2
    have hqA : q ∉ carA L := fun hc => h2 (mem_carA.1 hc).2
    by_cases h1 : p.1.Nonempty
    · have hpA : p ∈ carA L := mem_carA.2 ⟨hp, h1⟩
      have hmne : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty :=
        h1.mono Finset.subset_union_left
      have hun : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1 = p.1 := by
        simp only [hqe, Finset.union_empty]
      rw [partA, coalL, carA_insert_of_nonempty _ hmne, carA_erase, carA_erase,
        Finset.image_insert, hun,
        show ((carA L).erase p).erase q = (carA L).erase p by
          rw [Finset.erase_eq_of_notMem (fun hc => hqA (Finset.mem_of_mem_erase hc))],
        image_erase_carA hw hpA, Finset.insert_erase (mem_partA.2 ⟨p, hpA, rfl⟩)]
    · have hpe : p.1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 h1
      have hpA : p ∉ carA L := fun hc => h1 (mem_carA.1 hc).2
      have hmne : ¬ ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty := by
        simp [hpe, hqe]
      rw [partA, coalL, carA_insert_of_empty _ hmne, carA_erase, carA_erase,
        Finset.erase_eq_of_notMem (fun hc => hqA (Finset.mem_of_mem_erase hc)),
        Finset.erase_eq_of_notMem hpA, partA]

theorem partA_rec (hw : WF L) (hp : p ∈ carC L) : partA (recL L p) = partA L := by
  obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
  have hpA : p ∈ carA L := mem_carA.2 ⟨hpL, h1⟩
  have hne1 : ((p.1, (∅ : Finset (Fin n))) : Lin n).1.Nonempty := h1
  have hne2 : ¬ (((∅ : Finset (Fin n)), p.2) : Lin n).1.Nonempty := by simp
  rw [partA, recL, carA_insert_of_nonempty _ hne1, carA_insert_of_empty _ hne2, carA_erase,
    Finset.image_insert, image_erase_carA hw hpA,
    Finset.insert_erase (mem_partA.2 ⟨p, hpA, rfl⟩), partA]

theorem kingman_generator (hw : WF L) (f : Finset (Finset (Fin n)) → ℝ) :
    stepArg ρ (fun M => f (partA M)) L - dtotArg ρ L * f (partA L)
      = ∑ S ∈ partA L, ∑ T ∈ (partA L).erase S,
          (f (mergeP (partA L) S T) - f (partA L)) := by
  have hrec : (∑ p ∈ carC L, f (partA (recL L p))) = ((tt L : ℕ) : ℝ) * f (partA L) := by
    rw [Finset.sum_congr rfl fun p hp => by rw [partA_rec hw hp], Finset.sum_const,
      nsmul_eq_mul, tt]
  have hsplit : ∀ p ∈ L, ∀ q ∈ L.erase p,
      f (partA (coalL L p q)) - f (partA L)
        = if p.1.Nonempty ∧ q.1.Nonempty then f (mergeP (partA L) p.1 q.1) - f (partA L)
          else 0 := by
    intro p hp q hq
    by_cases hb : p.1.Nonempty ∧ q.1.Nonempty
    · rw [ite_eq_left hb, partA_coal_both hw hp hq hb.1 hb.2]
    · rw [ite_eq_right hb, partA_coal_not hw hp hq hb, sub_self]
  have hinner : ∀ p ∈ L,
      (∑ q ∈ L.erase p, if p.1.Nonempty ∧ q.1.Nonempty then
          f (mergeP (partA L) p.1 q.1) - f (partA L) else 0)
        = if p.1.Nonempty then
            ∑ q ∈ (carA L).erase p, (f (mergeP (partA L) p.1 q.1) - f (partA L)) else 0 := by
    intro p _
    by_cases h1 : p.1.Nonempty
    · rw [ite_eq_left h1]
      have hset : (carA L).erase p = (L.erase p).filter fun u => u.1.Nonempty := by
        rw [← carA_erase, carA]
      rw [hset, Finset.sum_filter]
      exact Finset.sum_congr rfl fun q _ => by
        by_cases h2 : q.1.Nonempty
        · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h2]
        · rw [ite_eq_right (fun hc => h2 hc.2), ite_eq_right h2]
    · rw [ite_eq_right h1]
      exact Finset.sum_eq_zero fun q _ => ite_eq_right fun hc => h1 hc.1
  have hcoal : (∑ p ∈ L, ∑ q ∈ L.erase p, (f (partA (coalL L p q)) - f (partA L)))
      = ∑ p ∈ carA L, ∑ q ∈ (carA L).erase p,
          (f (mergeP (partA L) p.1 q.1) - f (partA L)) := by
    rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl (hsplit p hp),
      Finset.sum_congr rfl hinner, carA, Finset.sum_filter]
  have hout : ∀ g : Finset (Fin n) → ℝ, (∑ S ∈ partA L, g S) = ∑ p ∈ carA L, g p.1 := by
    intro g
    rw [partA]
    exact Finset.sum_image (fun p hp r hr hpr => fst_injOn hw p hp r hr hpr)
  have hin : ∀ p : Lin n, p ∈ carA L → ∀ g : Finset (Fin n) → ℝ,
      (∑ T ∈ (partA L).erase p.1, g T) = ∑ q ∈ (carA L).erase p, g q.1 := by
    intro p hp g
    rw [← image_erase_carA hw hp]
    exact Finset.sum_image (fun u hu r hr hur => fst_injOn hw u (Finset.mem_of_mem_erase hu)
      r (Finset.mem_of_mem_erase hr) hur)
  have hindex : (∑ S ∈ partA L, ∑ T ∈ (partA L).erase S,
        (f (mergeP (partA L) S T) - f (partA L)))
      = ∑ p ∈ carA L, ∑ q ∈ (carA L).erase p,
        (f (mergeP (partA L) p.1 q.1) - f (partA L)) := by
    rw [hout]
    exact Finset.sum_congr rfl fun p hp => hin p hp _
  have hexp : (∑ p ∈ L, ∑ q ∈ L.erase p, f (partA (coalL L p q)))
      = (∑ p ∈ L, ∑ q ∈ L.erase p, (f (partA (coalL L p q)) - f (partA L)))
        + ((L.card * (L.card - 1) : ℕ) : ℝ) * f (partA L) := by
    rw [← sum_pairs_const L (f (partA L)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [stepArg, hexp, hcoal, ← hindex, hrec, dtotArg]
  ring

theorem card_partA_coal (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p) (h1 : p.1.Nonempty)
    (h2 : q.1.Nonempty) : (partA (coalL L p q)).card + 1 = (partA L).card := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hqp : q ≠ p := Finset.ne_of_mem_erase hq
  have hpA : p ∈ carA L := mem_carA.2 ⟨hp, h1⟩
  have hqA : q ∈ carA L := mem_carA.2 ⟨hqL, h2⟩
  have hqA' : q ∈ (carA L).erase p := Finset.mem_erase.2 ⟨hqp, hqA⟩
  have hmne : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1.Nonempty :=
    h1.mono Finset.subset_union_left
  have hnm : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n) ∉ ((carA L).erase p).erase q := by
    intro hc
    refine coal_not_mem hw hp hqL ?_
    refine Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hc, ?_⟩
    exact Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc),
      carA_subset L (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))⟩
  have hcar : carA (coalL L p q) = insert ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n)
      (((carA L).erase p).erase q) := by
    rw [coalL, carA_insert_of_nonempty _ hmne, carA_erase, carA_erase]
  have hc1 : (partA (coalL L p q)).card = (carA (coalL L p q)).card :=
    card_partA (hw.coal hp hqL)
  have hc2 : (partA L).card = (carA L).card := card_partA hw
  have hc3 : (carA (coalL L p q)).card = 1 + (((carA L).erase p).erase q).card := by
    rw [hcar, Finset.card_insert_of_notMem hnm]
    ring
  have hc4 : (((carA L).erase p).erase q).card = (carA L).card - 1 - 1 := by
    rw [Finset.card_erase_of_mem hqA', Finset.card_erase_of_mem hpA]
  have hc5 : 2 ≤ (carA L).card := by
    have h2' : ({p, q} : Finset (Lin n)) ⊆ carA L := by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hpA
      · rw [Finset.mem_singleton.1 hu]; exact hqA
    have := Finset.card_le_card h2'
    rwa [Finset.card_insert_of_notMem (by simpa using fun hc => hqp hc.symm),
      Finset.card_singleton] at this
  rw [hc1, hc2, hc3, hc4]
  omega

end Rhone.Coalescent.TypedAncestralChain
