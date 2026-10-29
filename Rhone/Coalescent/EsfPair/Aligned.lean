/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Final

/-! # At `ρ = 0` the two loci ride one tree -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy

variable {n : ℕ}

def Aligned (L : Finset (Lin n)) : Prop := ∀ p ∈ L, ∀ q ∈ L, p ≠ q → Disjoint p.1 q.2

theorem aligned_fullState : Aligned (fullState n) := by
  intro p hp q hq hne
  obtain ⟨k, rfl⟩ := mem_fullState.1 hp
  obtain ⟨l, rfl⟩ := mem_fullState.1 hq
  have hkl : k ≠ l := fun h => hne (by rw [h])
  simpa using hkl

theorem Aligned.mono {L M : Finset (Lin n)} (h : Aligned L) (hML : M ⊆ L) : Aligned M :=
  fun p hp q hq hne => h p (hML hp) q (hML hq) hne

theorem Aligned.coal {L : Finset (Lin n)} (h : Aligned L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L) : Aligned (coalL L p q) := by
  have hsub : Aligned ((L.erase p).erase q) :=
    h.mono ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have hkey : ∀ r ∈ (L.erase p).erase q,
      Disjoint (p.1 ∪ q.1) r.2 ∧ Disjoint r.1 (p.2 ∪ q.2) := by
    intro r hr
    have hrL : r ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
    have hrp : r ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
    have hrq : r ≠ q := Finset.ne_of_mem_erase hr
    exact ⟨Finset.disjoint_union_left.2 ⟨h p hp r hrL fun hc => hrp hc.symm,
        h q hq r hrL fun hc => hrq hc.symm⟩,
      Finset.disjoint_union_right.2 ⟨h r hrL p hp hrp, h r hrL q hq hrq⟩⟩
  intro r hr r' hr' hne
  rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
  · exact absurd rfl hne
  · exact (hkey r' hr').1
  · exact (hkey r hr).2
  · exact hsub r hr r' hr' hne

theorem Aligned.mutA {L : Finset (Lin n)} (h : Aligned L) {p : Lin n} (hp : p ∈ L) :
    Aligned (mutAL L p) := by
  have hsub : Aligned (L.erase p) := h.mono (Finset.erase_subset _ _)
  unfold mutAL
  split_ifs with hp2
  · exact hsub
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · simp
    · exact h r (Finset.mem_of_mem_erase hr) p hp (Finset.ne_of_mem_erase hr)
    · exact hsub r hr r' hr' hne

theorem Aligned.mutB {L : Finset (Lin n)} (h : Aligned L) {p : Lin n} (hp : p ∈ L) :
    Aligned (mutBL L p) := by
  have hsub : Aligned (L.erase p) := h.mono (Finset.erase_subset _ _)
  unfold mutBL
  split_ifs with hp1
  · exact hsub
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · exact h p hp r' (Finset.mem_of_mem_erase hr') fun hc => (Finset.ne_of_mem_erase hr') hc.symm
    · simp
    · exact hsub r hr r' hr' hne

theorem not_aligned_recL {L : Finset (Lin n)} {p : Lin n} (h : (p.1 ∩ p.2).Nonempty) :
    ¬ Aligned (recL L p) := by
  intro hal
  obtain ⟨k, hk⟩ := h
  obtain ⟨hk1, hk2⟩ := Finset.mem_inter.1 hk
  have h1 : (p.1, (∅ : Finset (Fin n))) ∈ recL L p := Finset.mem_insert_self _ _
  have h2 : ((∅ : Finset (Fin n)), p.2) ∈ recL L p :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hne : (p.1, (∅ : Finset (Fin n))) ≠ ((∅ : Finset (Fin n)), p.2) :=
    rec_ne ⟨k, hk1⟩
  exact (Finset.disjoint_left.1 (hal _ h1 _ h2 hne)) hk1 hk2

theorem inter_union_union {L : Finset (Lin n)} (h : Aligned L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L) (hne : p ≠ q) :
    (p.1 ∪ q.1) ∩ (p.2 ∪ q.2) = (p.1 ∩ p.2) ∪ (q.1 ∩ q.2) := by
  have h1 : Disjoint p.1 q.2 := h p hp q hq hne
  have h2 : Disjoint q.1 p.2 := h q hq p hp fun hc => hne hc.symm
  ext k
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h3 | h3, h4 | h4⟩
    · exact Or.inl ⟨h3, h4⟩
    · exact absurd h4 (Finset.disjoint_left.1 h1 h3)
    · exact absurd h4 (Finset.disjoint_left.1 h2 h3)
    · exact Or.inr ⟨h3, h4⟩
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact ⟨Or.inl h3, Or.inl h4⟩
    · exact ⟨Or.inr h3, Or.inr h4⟩

theorem star_mutA {p : Lin n} : ((∅ : Finset (Fin n)), p.2).1 ∩ ((∅ : Finset (Fin n)), p.2).2
    = ∅ := by simp

theorem star_mutB {p : Lin n} : (p.1, (∅ : Finset (Fin n))).1 ∩ (p.1, (∅ : Finset (Fin n))).2
    = ∅ := by simp

end Rhone.Coalescent.EsfPair
