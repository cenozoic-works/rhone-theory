/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # The two-locus ancestral recombination graph: backward states and their moves -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset

variable {n : ℕ}

abbrev Lin (n : ℕ) : Type := Finset (Fin n) × Finset (Fin n)

structure WF (L : Finset (Lin n)) : Prop where
  carries : ∀ p ∈ L, p.1.Nonempty ∨ p.2.Nonempty
  disjA : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → Disjoint p.1 q.1
  disjB : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → Disjoint p.2 q.2

namespace WF

theorem mono {L M : Finset (Lin n)} (h : WF L) (hML : M ⊆ L) : WF M :=
  ⟨fun p hp => h.carries p (hML hp), fun p hp q hq => h.disjA p (hML hp) q (hML hq),
    fun p hp q hq => h.disjB p (hML hp) q (hML hq)⟩

theorem erase {L : Finset (Lin n)} (h : WF L) (p : Lin n) : WF (L.erase p) :=
  h.mono (Finset.erase_subset _ _)

end WF

def carA (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.1.Nonempty

def carB (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.2.Nonempty

def carC (L : Finset (Lin n)) : Finset (Lin n) :=
  L.filter fun p => p.1.Nonempty ∧ p.2.Nonempty

def na (L : Finset (Lin n)) : ℕ := (carA L).card

def nb (L : Finset (Lin n)) : ℕ := (carB L).card

def tt (L : Finset (Lin n)) : ℕ := (carC L).card

theorem mem_carA {L : Finset (Lin n)} {p : Lin n} : p ∈ carA L ↔ p ∈ L ∧ p.1.Nonempty := by
  simp [carA]

theorem mem_carB {L : Finset (Lin n)} {p : Lin n} : p ∈ carB L ↔ p ∈ L ∧ p.2.Nonempty := by
  simp [carB]

theorem mem_carC {L : Finset (Lin n)} {p : Lin n} :
    p ∈ carC L ↔ p ∈ L ∧ p.1.Nonempty ∧ p.2.Nonempty := by
  simp [carC]

theorem carA_subset (L : Finset (Lin n)) : carA L ⊆ L := Finset.filter_subset _ _

theorem carB_subset (L : Finset (Lin n)) : carB L ⊆ L := Finset.filter_subset _ _

theorem carC_subset (L : Finset (Lin n)) : carC L ⊆ L := Finset.filter_subset _ _

theorem carA_union_carB {L : Finset (Lin n)} (h : WF L) : carA L ∪ carB L = L := by
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (carA_subset L) (carB_subset L)
  · intro p hp
    rcases h.carries p hp with h1 | h1
    · exact Finset.mem_union_left _ (mem_carA.2 ⟨hp, h1⟩)
    · exact Finset.mem_union_right _ (mem_carB.2 ⟨hp, h1⟩)

theorem na_add_nb_pos {L : Finset (Lin n)} (h : WF L) (hL : L.Nonempty) : 0 < na L + nb L := by
  obtain ⟨p, hp⟩ := hL
  rcases h.carries p hp with h1 | h1
  · have hm : p ∈ carA L := mem_carA.2 ⟨hp, h1⟩
    have := Finset.card_pos.2 ⟨p, hm⟩
    unfold na
    omega
  · have hm : p ∈ carB L := mem_carB.2 ⟨hp, h1⟩
    have := Finset.card_pos.2 ⟨p, hm⟩
    unfold nb
    omega

theorem na_le_card (L : Finset (Lin n)) : na L ≤ L.card :=
  Finset.card_le_card (carA_subset L)

theorem nb_le_card (L : Finset (Lin n)) : nb L ≤ L.card :=
  Finset.card_le_card (carB_subset L)

theorem tt_le_na (L : Finset (Lin n)) : tt L ≤ na L :=
  Finset.card_le_card fun _ hp => mem_carA.2 ⟨(mem_carC.1 hp).1, (mem_carC.1 hp).2.1⟩

theorem tt_le_nb (L : Finset (Lin n)) : tt L ≤ nb L :=
  Finset.card_le_card fun _ hp => mem_carB.2 ⟨(mem_carC.1 hp).1, (mem_carC.1 hp).2.2⟩

def coalL (L : Finset (Lin n)) (p q : Lin n) : Finset (Lin n) :=
  insert (p.1 ∪ q.1, p.2 ∪ q.2) ((L.erase p).erase q)

def mutAL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  if p.2 = ∅ then L.erase p else insert (∅, p.2) (L.erase p)

def mutBL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  if p.1 = ∅ then L.erase p else insert (p.1, ∅) (L.erase p)

def recL (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) :=
  insert (p.1, ∅) (insert (∅, p.2) (L.erase p))

theorem coalL_comm (L : Finset (Lin n)) (p q : Lin n) : coalL L p q = coalL L q p := by
  unfold coalL
  rw [Finset.erase_right_comm, Finset.union_comm p.1 q.1, Finset.union_comm p.2 q.2]

theorem coal_not_mem {L : Finset (Lin n)} (h : WF L) {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) :
    (p.1 ∪ q.1, p.2 ∪ q.2) ∉ (L.erase p).erase q := by
  intro hmem
  set m : Lin n := (p.1 ∪ q.1, p.2 ∪ q.2) with hm
  have hmL : m ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
  have hmp : m ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmem)
  have hmq : m ≠ q := Finset.ne_of_mem_erase hmem
  have h1 : Disjoint m.1 p.1 := h.disjA m hmL p hp hmp
  have h1' : Disjoint m.1 q.1 := h.disjA m hmL q hq hmq
  have h2 : Disjoint m.2 p.2 := h.disjB m hmL p hp hmp
  have h2' : Disjoint m.2 q.2 := h.disjB m hmL q hq hmq
  have e1 : m.1 = p.1 ∪ q.1 := rfl
  have e2 : m.2 = p.2 ∪ q.2 := rfl
  have hA : m.1 = ∅ := by
    have hd : Disjoint m.1 (p.1 ∪ q.1) := Finset.disjoint_union_right.2 ⟨h1, h1'⟩
    rw [← e1] at hd
    simpa using disjoint_self.1 hd
  have hB : m.2 = ∅ := by
    have hd : Disjoint m.2 (p.2 ∪ q.2) := Finset.disjoint_union_right.2 ⟨h2, h2'⟩
    rw [← e2] at hd
    simpa using disjoint_self.1 hd
  rcases h.carries m hmL with hc | hc
  · exact absurd hA (Finset.nonempty_iff_ne_empty.1 hc)
  · exact absurd hB (Finset.nonempty_iff_ne_empty.1 hc)

theorem mutA_not_mem {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ L)
    (h2 : p.2.Nonempty) : ((∅ : Finset (Fin n)), p.2) ∉ L.erase p := by
  intro hmem
  have hmL : ((∅ : Finset (Fin n)), p.2) ∈ L := Finset.mem_of_mem_erase hmem
  have hne : ((∅ : Finset (Fin n)), p.2) ≠ p := Finset.ne_of_mem_erase hmem
  have hd := h.disjB _ hmL p hp hne
  have hd2 : p.2 = ∅ := by simpa using disjoint_self.1 hd
  exact absurd hd2 (Finset.nonempty_iff_ne_empty.1 h2)

theorem mutB_not_mem {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ L)
    (h1 : p.1.Nonempty) : (p.1, (∅ : Finset (Fin n))) ∉ L.erase p := by
  intro hmem
  have hmL : (p.1, (∅ : Finset (Fin n))) ∈ L := Finset.mem_of_mem_erase hmem
  have hne : (p.1, (∅ : Finset (Fin n))) ≠ p := Finset.ne_of_mem_erase hmem
  have hd := h.disjA _ hmL p hp hne
  have hd2 : p.1 = ∅ := by simpa using disjoint_self.1 hd
  exact absurd hd2 (Finset.nonempty_iff_ne_empty.1 h1)

theorem rec_ne {p : Lin n} (h1 : p.1.Nonempty) :
    (p.1, (∅ : Finset (Fin n))) ≠ ((∅ : Finset (Fin n)), p.2) := by
  intro hEq
  have hp : p.1 = (∅ : Finset (Fin n)) := congrArg Prod.fst hEq
  exact absurd hp (Finset.nonempty_iff_ne_empty.1 h1)

theorem WF.coal {L : Finset (Lin n)} (h : WF L) {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) :
    WF (coalL L p q) := by
  have key : ∀ r ∈ (L.erase p).erase q, Disjoint r.1 (p.1 ∪ q.1) ∧ Disjoint r.2 (p.2 ∪ q.2) := by
    intro r hr
    have hrL : r ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
    have hrp : r ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
    have hrq : r ≠ q := Finset.ne_of_mem_erase hr
    exact ⟨Finset.disjoint_union_right.2 ⟨h.disjA r hrL p hp hrp, h.disjA r hrL q hq hrq⟩,
      Finset.disjoint_union_right.2 ⟨h.disjB r hrL p hp hrp, h.disjB r hrL q hq hrq⟩⟩
  have hsub : WF ((L.erase p).erase q) := (h.erase p).erase q
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · rcases h.carries p hp with hc | hc
      · exact Or.inl (hc.mono Finset.subset_union_left)
      · exact Or.inr (hc.mono Finset.subset_union_left)
    · exact hsub.carries r hr
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · exact ((key r' hr').1).symm
    · exact (key r hr).1
    · exact hsub.disjA r hr r' hr' hne
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · exact ((key r' hr').2).symm
    · exact (key r hr).2
    · exact hsub.disjB r hr r' hr' hne

theorem WF.mutA {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ L) : WF (mutAL L p) := by
  unfold mutAL
  split_ifs with hp2
  · exact h.erase p
  · have h2 : p.2.Nonempty := Finset.nonempty_iff_ne_empty.2 hp2
    have hsub : WF (L.erase p) := h.erase p
    have key : ∀ r ∈ L.erase p, Disjoint r.2 p.2 := fun r hr =>
      h.disjB r (Finset.mem_of_mem_erase hr) p hp (Finset.ne_of_mem_erase hr)
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact Or.inr h2
      · exact hsub.carries r hr
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · simp
      · simp
      · exact hsub.disjA r hr r' hr' hne
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · exact ((key r' hr').symm : Disjoint p.2 r'.2)
      · exact key r hr
      · exact hsub.disjB r hr r' hr' hne

theorem WF.mutB {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ L) : WF (mutBL L p) := by
  unfold mutBL
  split_ifs with hp1
  · exact h.erase p
  · have h1 : p.1.Nonempty := Finset.nonempty_iff_ne_empty.2 hp1
    have hsub : WF (L.erase p) := h.erase p
    have key : ∀ r ∈ L.erase p, Disjoint r.1 p.1 := fun r hr =>
      h.disjA r (Finset.mem_of_mem_erase hr) p hp (Finset.ne_of_mem_erase hr)
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact Or.inl h1
      · exact hsub.carries r hr
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · exact ((key r' hr').symm : Disjoint p.1 r'.1)
      · exact key r hr
      · exact hsub.disjA r hr r' hr' hne
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · simp
      · simp
      · exact hsub.disjB r hr r' hr' hne

theorem WF.recomb {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ L)
    (h1 : p.1.Nonempty) (h2 : p.2.Nonempty) : WF (recL L p) := by
  have hsub : WF (L.erase p) := h.erase p
  have keyA : ∀ r ∈ L.erase p, Disjoint r.1 p.1 := fun r hr =>
    h.disjA r (Finset.mem_of_mem_erase hr) p hp (Finset.ne_of_mem_erase hr)
  have keyB : ∀ r ∈ L.erase p, Disjoint r.2 p.2 := fun r hr =>
    h.disjB r (Finset.mem_of_mem_erase hr) p hp (Finset.ne_of_mem_erase hr)
  have hstep : WF (insert ((∅ : Finset (Fin n)), p.2) (L.erase p)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact Or.inr h2
      · exact hsub.carries r hr
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · simp
      · simp
      · exact hsub.disjA r hr r' hr' hne
    · intro r hr r' hr' hne
      rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
      · exact absurd rfl hne
      · exact ((keyB r' hr').symm : Disjoint p.2 r'.2)
      · exact keyB r hr
      · exact hsub.disjB r hr r' hr' hne
  have keyA' : ∀ r ∈ insert ((∅ : Finset (Fin n)), p.2) (L.erase p), Disjoint r.1 p.1 := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · simp
    · exact keyA r hr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact Or.inl h1
    · exact hstep.carries r hr
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · exact ((keyA' r' hr').symm : Disjoint p.1 r'.1)
    · exact keyA' r hr
    · exact hstep.disjA r hr r' hr' hne
  · intro r hr r' hr' hne
    rcases Finset.mem_insert.1 hr with rfl | hr <;> rcases Finset.mem_insert.1 hr' with rfl | hr'
    · exact absurd rfl hne
    · simp
    · simp
    · exact hstep.disjB r hr r' hr' hne

end Rhone.Coalescent.TwoLocusGenealogy
