/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Phi

/-! # The two current partitions of a partition-carrying state, and the `ρ = 0` invariant -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair

variable {n : ℕ} {s : PSt n} {p q : Lin n} {k : Fin n}

def ablk (L : Finset (Lin n)) (k : Fin n) : Finset (Fin n) :=
  (L.filter fun p => k ∈ p.1).biUnion Prod.fst

def bblk (L : Finset (Lin n)) (k : Fin n) : Finset (Fin n) :=
  (L.filter fun p => k ∈ p.2).biUnion Prod.snd

theorem filterA_eq_singleton {L : Finset (Lin n)} (hw : WF L) (hp : p ∈ L) (hk : k ∈ p.1) :
    (L.filter fun r => k ∈ r.1) = {p} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hr, hkr⟩ => ?_, fun h => h ▸ ⟨hp, hk⟩⟩
  by_contra hne
  exact (Finset.disjoint_left.1 (hw.disjA r hr p hp hne)) hkr hk

theorem filterB_eq_singleton {L : Finset (Lin n)} (hw : WF L) (hp : p ∈ L) (hk : k ∈ p.2) :
    (L.filter fun r => k ∈ r.2) = {p} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hr, hkr⟩ => ?_, fun h => h ▸ ⟨hp, hk⟩⟩
  by_contra hne
  exact (Finset.disjoint_left.1 (hw.disjB r hr p hp hne)) hkr hk

theorem ablk_eq {L : Finset (Lin n)} (hw : WF L) (hp : p ∈ L) (hk : k ∈ p.1) :
    ablk L k = p.1 := by
  rw [ablk, filterA_eq_singleton hw hp hk, Finset.singleton_biUnion]

theorem bblk_eq {L : Finset (Lin n)} (hw : WF L) (hp : p ∈ L) (hk : k ∈ p.2) :
    bblk L k = p.2 := by
  rw [bblk, filterB_eq_singleton hw hp hk, Finset.singleton_biUnion]

theorem ablk_eq_empty {L : Finset (Lin n)} (hk : k ∉ coverA L) : ablk L k = ∅ := by
  rw [ablk, Finset.filter_eq_empty_iff.2 fun r hr hkr => hk (mem_coverA.2 ⟨r, hr, hkr⟩)]
  simp

theorem bblk_eq_empty {L : Finset (Lin n)} (hk : k ∉ coverB L) : bblk L k = ∅ := by
  rw [bblk, Finset.filter_eq_empty_iff.2 fun r hr hkr => hk (mem_coverB.2 ⟨r, hr, hkr⟩)]
  simp

theorem blockOf_eq_empty {η : Blocks n} (hk : k ∉ η.biUnion id) : blockOf η k = ∅ := by
  have h : (η.filter fun β => k ∈ β) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun β hβ hkβ => hk (Finset.mem_biUnion.2 ⟨β, hβ, hkβ⟩)
  rw [blockOf, h]
  simp

def abl (s : PSt n) (k : Fin n) : Finset (Fin n) := ablk s.1 k ∪ blockOf s.2.1 k

def bbl (s : PSt n) (k : Fin n) : Finset (Fin n) := bblk s.1 k ∪ blockOf s.2.2 k

def pib (s : PSt n) (k : Fin n) : Finset (Fin n) := abl s k ∩ bbl s k

def pend (s : PSt n) : Finset (Fin n) := coverA s.1 ∩ coverB s.1

structure Inv (s : PSt n) : Prop where
  wfp : WFP s
  aligned : Aligned s.1
  spA : spanA s = Finset.univ
  spB : spanB s = Finset.univ
  uA : ∀ β ∈ s.2.1, ∀ p ∈ s.1, ∀ q ∈ s.1, (β ∩ p.2).Nonempty → (β ∩ q.2).Nonempty → p = q
  uB : ∀ γ ∈ s.2.2, ∀ p ∈ s.1, ∀ q ∈ s.1, (γ ∩ p.1).Nonempty → (γ ∩ q.1).Nonempty → p = q

namespace Inv

theorem partA (hs : Inv s) : IsPartOf (Finset.univ \ coverA s.1) s.2.1 := by
  refine ⟨hs.wfp.neA, hs.wfp.pdA, ?_⟩
  have h1 : coverA s.1 ∪ s.2.1.biUnion id = Finset.univ := hs.spA
  ext l
  constructor
  · intro hl
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
      fun hc => (Finset.disjoint_left.1 hs.wfp.freshA) hc hl⟩
  · intro hl
    obtain ⟨-, hnc⟩ := Finset.mem_sdiff.1 hl
    have hu : l ∈ coverA s.1 ∪ s.2.1.biUnion id := by rw [h1]; exact Finset.mem_univ l
    exact (Finset.mem_union.1 hu).resolve_left hnc

theorem partB (hs : Inv s) : IsPartOf (Finset.univ \ coverB s.1) s.2.2 := by
  refine ⟨hs.wfp.neB, hs.wfp.pdB, ?_⟩
  have h1 : coverB s.1 ∪ s.2.2.biUnion id = Finset.univ := hs.spB
  ext l
  constructor
  · intro hl
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
      fun hc => (Finset.disjoint_left.1 hs.wfp.freshB) hc hl⟩
  · intro hl
    obtain ⟨-, hnc⟩ := Finset.mem_sdiff.1 hl
    have hu : l ∈ coverB s.1 ∪ s.2.2.biUnion id := by rw [h1]; exact Finset.mem_univ l
    exact (Finset.mem_union.1 hu).resolve_left hnc

end Inv

theorem abl_of_mem (hs : Inv s) (hp : p ∈ s.1) (hk : k ∈ p.1) : abl s k = p.1 := by
  have h1 : blockOf s.2.1 k = ∅ :=
    blockOf_eq_empty fun hc =>
      (Finset.disjoint_left.1 hs.wfp.freshA) (mem_coverA.2 ⟨p, hp, hk⟩) hc
  rw [abl, ablk_eq hs.wfp.wf hp hk, h1, Finset.union_empty]

theorem bbl_of_mem (hs : Inv s) (hp : p ∈ s.1) (hk : k ∈ p.2) : bbl s k = p.2 := by
  have h1 : blockOf s.2.2 k = ∅ :=
    blockOf_eq_empty fun hc =>
      (Finset.disjoint_left.1 hs.wfp.freshB) (mem_coverB.2 ⟨p, hp, hk⟩) hc
  rw [bbl, bblk_eq hs.wfp.wf hp hk, h1, Finset.union_empty]

theorem abl_of_not_cover (hk : k ∉ coverA s.1) : abl s k = blockOf s.2.1 k := by
  rw [abl, ablk_eq_empty hk, Finset.empty_union]

theorem bbl_of_not_cover (hk : k ∉ coverB s.1) : bbl s k = blockOf s.2.2 k := by
  rw [bbl, bblk_eq_empty hk, Finset.empty_union]

theorem mem_sdiff_coverA (hk : k ∉ coverA s.1) : k ∈ Finset.univ \ coverA s.1 :=
  Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩

theorem mem_sdiff_coverB (hk : k ∉ coverB s.1) : k ∈ Finset.univ \ coverB s.1 :=
  Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩

theorem blockOfA_mem (hs : Inv s) (hk : k ∉ coverA s.1) : blockOf s.2.1 k ∈ s.2.1 :=
  blockOf_mem hs.partA (mem_sdiff_coverA hk)

theorem mem_blockOfA (hs : Inv s) (hk : k ∉ coverA s.1) : k ∈ blockOf s.2.1 k :=
  mem_blockOf hs.partA (mem_sdiff_coverA hk)

theorem blockOfB_mem (hs : Inv s) (hk : k ∉ coverB s.1) : blockOf s.2.2 k ∈ s.2.2 :=
  blockOf_mem hs.partB (mem_sdiff_coverB hk)

theorem mem_blockOfB (hs : Inv s) (hk : k ∉ coverB s.1) : k ∈ blockOf s.2.2 k :=
  mem_blockOf hs.partB (mem_sdiff_coverB hk)

theorem mem_abl (hs : Inv s) (k : Fin n) : k ∈ abl s k := by
  by_cases hk : k ∈ coverA s.1
  · obtain ⟨p, hp, hkp⟩ := mem_coverA.1 hk
    rw [abl_of_mem hs hp hkp]
    exact hkp
  · rw [abl_of_not_cover hk]
    exact mem_blockOfA hs hk

theorem mem_bbl (hs : Inv s) (k : Fin n) : k ∈ bbl s k := by
  by_cases hk : k ∈ coverB s.1
  · obtain ⟨p, hp, hkp⟩ := mem_coverB.1 hk
    rw [bbl_of_mem hs hp hkp]
    exact hkp
  · rw [bbl_of_not_cover hk]
    exact mem_blockOfB hs hk

theorem mem_pib (hs : Inv s) (k : Fin n) : k ∈ pib s k :=
  Finset.mem_inter.2 ⟨mem_abl hs k, mem_bbl hs k⟩

theorem inter_coverB (hs : Inv s) (hp : p ∈ s.1) : p.1 ∩ coverB s.1 = p.1 ∩ p.2 := by
  ext l
  simp only [Finset.mem_inter]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, mem_coverB.2 ⟨p, hp, h2⟩⟩⟩
  obtain ⟨r, hr, hlr⟩ := mem_coverB.1 h2
  by_cases hrp : r = p
  · exact hrp ▸ hlr
  · exact absurd hlr (Finset.disjoint_left.1 (hs.aligned p hp r hr fun hc => hrp hc.symm) h1)

theorem coverA_inter (hs : Inv s) (hp : p ∈ s.1) : coverA s.1 ∩ p.2 = p.1 ∩ p.2 := by
  ext l
  simp only [Finset.mem_inter]
  refine ⟨fun ⟨h1, h2⟩ => ⟨?_, h2⟩, fun ⟨h1, h2⟩ => ⟨mem_coverA.2 ⟨p, hp, h1⟩, h2⟩⟩
  obtain ⟨r, hr, hlr⟩ := mem_coverA.1 h1
  by_cases hrp : r = p
  · exact hrp ▸ hlr
  · exact absurd h2 (Finset.disjoint_left.1 (hs.aligned r hr p hp hrp) hlr)

theorem mem_mutAL {L : Finset (Lin n)} {r : Lin n} :
    r ∈ mutAL L p ↔ (p.2 ≠ ∅ ∧ r = ((∅ : Finset (Fin n)), p.2)) ∨ r ∈ L.erase p := by
  rw [mutAL]
  split_ifs with h
  · simp [h]
  · simp [h, Finset.mem_insert]

theorem mem_mutBL {L : Finset (Lin n)} {r : Lin n} :
    r ∈ mutBL L p ↔ (p.1 ≠ ∅ ∧ r = (p.1, (∅ : Finset (Fin n)))) ∨ r ∈ L.erase p := by
  rw [mutBL]
  split_ifs with h
  · simp [h]
  · simp [h, Finset.mem_insert]

theorem erase_subset_mutAL {L : Finset (Lin n)} : L.erase p ⊆ mutAL L p :=
  fun _ hr => mem_mutAL.2 (Or.inr hr)

theorem erase_subset_mutBL {L : Finset (Lin n)} : L.erase p ⊆ mutBL L p :=
  fun _ hr => mem_mutBL.2 (Or.inr hr)

theorem nonempty_inter_union {β X Y : Finset (Fin n)} (h : (β ∩ (X ∪ Y)).Nonempty) :
    (β ∩ X).Nonempty ∨ (β ∩ Y).Nonempty := by
  obtain ⟨l, hl⟩ := h
  rw [Finset.mem_inter, Finset.mem_union] at hl
  rcases hl.2 with h' | h'
  · exact Or.inl ⟨l, Finset.mem_inter.2 ⟨hl.1, h'⟩⟩
  · exact Or.inr ⟨l, Finset.mem_inter.2 ⟨hl.1, h'⟩⟩

theorem inter_empty_not_nonempty {β : Finset (Fin n)} (h : (β ∩ (∅ : Finset (Fin n))).Nonempty) :
    False := by simp at h

theorem Inv.coal (hs : Inv s) (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) : Inv (coalP s p q) := by
  have hqL : q ∈ s.1 := Finset.mem_of_mem_erase hq
  have hqp : q ≠ p := Finset.ne_of_mem_erase hq
  refine ⟨hs.wfp.coal hp hq, hs.aligned.coal hp hqL, ?_, ?_, ?_, ?_⟩
  · rw [spanA_coal hp hq]; exact hs.spA
  · rw [spanB_coal hp hq]; exact hs.spB
  · intro β hβ p' hp' q' hq' h1 h2
    have hβ' : β ∈ s.2.1 := hβ
    rcases Finset.mem_insert.1 hp' with rfl | hp'e
    · rcases Finset.mem_insert.1 hq' with rfl | hq'e
      · rfl
      · exfalso
        have hq'L : q' ∈ s.1 :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'e)
        have hq'p : q' ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq'e)
        have hq'q : q' ≠ q := Finset.ne_of_mem_erase hq'e
        rcases nonempty_inter_union h1 with hc | hc
        · exact hq'p (hs.uA β hβ' q' hq'L p hp h2 hc)
        · exact hq'q (hs.uA β hβ' q' hq'L q hqL h2 hc)
    · rcases Finset.mem_insert.1 hq' with rfl | hq'e
      · exfalso
        have hp'L : p' ∈ s.1 :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'e)
        have hp'p : p' ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp'e)
        have hp'q : p' ≠ q := Finset.ne_of_mem_erase hp'e
        rcases nonempty_inter_union h2 with hc | hc
        · exact hp'p (hs.uA β hβ' p' hp'L p hp h1 hc)
        · exact hp'q (hs.uA β hβ' p' hp'L q hqL h1 hc)
      · exact hs.uA β hβ' p' (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'e)) q'
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'e)) h1 h2
  · intro γ hγ p' hp' q' hq' h1 h2
    have hγ' : γ ∈ s.2.2 := hγ
    rcases Finset.mem_insert.1 hp' with rfl | hp'e
    · rcases Finset.mem_insert.1 hq' with rfl | hq'e
      · rfl
      · exfalso
        have hq'L : q' ∈ s.1 :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'e)
        have hq'p : q' ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hq'e)
        have hq'q : q' ≠ q := Finset.ne_of_mem_erase hq'e
        rcases nonempty_inter_union h1 with hc | hc
        · exact hq'p (hs.uB γ hγ' q' hq'L p hp h2 hc)
        · exact hq'q (hs.uB γ hγ' q' hq'L q hqL h2 hc)
    · rcases Finset.mem_insert.1 hq' with rfl | hq'e
      · exfalso
        have hp'L : p' ∈ s.1 :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'e)
        have hp'p : p' ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp'e)
        have hp'q : p' ≠ q := Finset.ne_of_mem_erase hp'e
        rcases nonempty_inter_union h2 with hc | hc
        · exact hp'p (hs.uB γ hγ' p' hp'L p hp h1 hc)
        · exact hp'q (hs.uB γ hγ' p' hp'L q hqL h1 hc)
      · exact hs.uB γ hγ' p' (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'e)) q'
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'e)) h1 h2

theorem Inv.mutA (hs : Inv s) (hp : p ∈ carA s.1) : Inv (mutAP s p) := by
  obtain ⟨hpL, hpne⟩ := mem_carA.1 hp
  refine ⟨hs.wfp.mutA hp, hs.aligned.mutA hpL, ?_, ?_, ?_, ?_⟩
  · rw [spanA_mutA hs.wfp.wf hpL]; exact hs.spA
  · rw [spanB_mutA hs.wfp.wf hpL]; exact hs.spB
  · intro β hβ p' hp' q' hq' h1 h2
    rcases Finset.mem_insert.1 hβ with rfl | hβ'
    · have key : ∀ r ∈ mutAL s.1 p, (p.1 ∩ r.2).Nonempty →
          r = ((∅ : Finset (Fin n)), p.2) := by
        intro r hr hne
        rcases mem_mutAL.1 hr with ⟨-, hre⟩ | hre
        · exact hre
        · exfalso
          have hrL : r ∈ s.1 := Finset.mem_of_mem_erase hre
          have hrp : r ≠ p := Finset.ne_of_mem_erase hre
          obtain ⟨l, hl⟩ := hne
          rw [Finset.mem_inter] at hl
          exact (Finset.disjoint_left.1
            (hs.aligned p hpL r hrL fun hc => hrp hc.symm)) hl.1 hl.2
      rw [key p' hp' h1, key q' hq' h2]
    · have key : ∀ r ∈ mutAL s.1 p, (β ∩ r.2).Nonempty →
          (r = ((∅ : Finset (Fin n)), p.2) ∧ (β ∩ p.2).Nonempty)
            ∨ (r ∈ s.1 ∧ r ≠ p ∧ (β ∩ r.2).Nonempty) := by
        intro r hr hne
        rcases mem_mutAL.1 hr with ⟨-, hre⟩ | hre
        · exact Or.inl ⟨hre, by rw [hre] at hne; exact hne⟩
        · exact Or.inr ⟨Finset.mem_of_mem_erase hre, Finset.ne_of_mem_erase hre, hne⟩
      rcases key p' hp' h1 with ⟨he1, hn1⟩ | ⟨hm1, hne1, hn1⟩ <;>
        rcases key q' hq' h2 with ⟨he2, hn2⟩ | ⟨hm2, hne2, hn2⟩
      · rw [he1, he2]
      · exact absurd (hs.uA β hβ' p hpL q' hm2 hn1 hn2) fun hc => hne2 hc.symm
      · exact absurd (hs.uA β hβ' p' hm1 p hpL hn1 hn2) hne1
      · exact hs.uA β hβ' p' hm1 q' hm2 hn1 hn2
  · intro γ hγ p' hp' q' hq' h1 h2
    have key : ∀ r ∈ mutAL s.1 p, (γ ∩ r.1).Nonempty → r ∈ s.1 := by
      intro r hr hne
      rcases mem_mutAL.1 hr with ⟨-, hre⟩ | hre
      · exact absurd (by rw [hre] at hne; exact hne) inter_empty_not_nonempty
      · exact Finset.mem_of_mem_erase hre
    exact hs.uB γ hγ p' (key p' hp' h1) q' (key q' hq' h2) h1 h2

theorem Inv.mutB (hs : Inv s) (hp : p ∈ carB s.1) : Inv (mutBP s p) := by
  obtain ⟨hpL, hpne⟩ := mem_carB.1 hp
  refine ⟨hs.wfp.mutB hp, hs.aligned.mutB hpL, ?_, ?_, ?_, ?_⟩
  · rw [spanA_mutB hs.wfp.wf hpL]; exact hs.spA
  · rw [spanB_mutB hs.wfp.wf hpL]; exact hs.spB
  · intro β hβ p' hp' q' hq' h1 h2
    have key : ∀ r ∈ mutBL s.1 p, (β ∩ r.2).Nonempty → r ∈ s.1 := by
      intro r hr hne
      rcases mem_mutBL.1 hr with ⟨-, hre⟩ | hre
      · exact absurd (by rw [hre] at hne; exact hne) inter_empty_not_nonempty
      · exact Finset.mem_of_mem_erase hre
    exact hs.uA β hβ p' (key p' hp' h1) q' (key q' hq' h2) h1 h2
  · intro γ hγ p' hp' q' hq' h1 h2
    rcases Finset.mem_insert.1 hγ with rfl | hγ'
    · have key : ∀ r ∈ mutBL s.1 p, (p.2 ∩ r.1).Nonempty →
          r = (p.1, (∅ : Finset (Fin n))) := by
        intro r hr hne
        rcases mem_mutBL.1 hr with ⟨-, hre⟩ | hre
        · exact hre
        · exfalso
          have hrL : r ∈ s.1 := Finset.mem_of_mem_erase hre
          have hrp : r ≠ p := Finset.ne_of_mem_erase hre
          obtain ⟨l, hl⟩ := hne
          rw [Finset.mem_inter] at hl
          exact (Finset.disjoint_left.1 (hs.aligned r hrL p hpL hrp)) hl.2 hl.1
      rw [key p' hp' h1, key q' hq' h2]
    · have key : ∀ r ∈ mutBL s.1 p, (γ ∩ r.1).Nonempty →
          (r = (p.1, (∅ : Finset (Fin n))) ∧ (γ ∩ p.1).Nonempty)
            ∨ (r ∈ s.1 ∧ r ≠ p ∧ (γ ∩ r.1).Nonempty) := by
        intro r hr hne
        rcases mem_mutBL.1 hr with ⟨-, hre⟩ | hre
        · exact Or.inl ⟨hre, by rw [hre] at hne; exact hne⟩
        · exact Or.inr ⟨Finset.mem_of_mem_erase hre, Finset.ne_of_mem_erase hre, hne⟩
      rcases key p' hp' h1 with ⟨he1, hn1⟩ | ⟨hm1, hne1, hn1⟩ <;>
        rcases key q' hq' h2 with ⟨he2, hn2⟩ | ⟨hm2, hne2, hn2⟩
      · rw [he1, he2]
      · exact absurd (hs.uB γ hγ' p hpL q' hm2 hn1 hn2) fun hc => hne2 hc.symm
      · exact absurd (hs.uB γ hγ' p' hm1 p hpL hn1 hn2) hne1
      · exact hs.uB γ hγ' p' hm1 q' hm2 hn1 hn2

theorem inv_initP : Inv (initP n) :=
  ⟨wfp_initP, aligned_fullState, spanA_initP, spanB_initP,
    fun β hβ => absurd hβ (Finset.notMem_empty β),
    fun γ hγ => absurd hγ (Finset.notMem_empty γ)⟩

end Rhone.Coalescent.PartitionCarryingChain
