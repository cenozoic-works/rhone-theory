/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Star

/-! # The emitted star partition -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair

variable {n : ℕ} {s : PSt n} {p q : Lin n} {k : Fin n}

def emitStar (s : PSt n) : Blocks n := (Finset.univ \ pend s).image (pib s)

theorem mem_pend {s : PSt n} {k : Fin n} : k ∈ pend s ↔ k ∈ coverA s.1 ∧ k ∈ coverB s.1 :=
  Finset.mem_inter

theorem pib_of_mem_star (hs : Inv s) (hp : p ∈ s.1) (hk : k ∈ p.1 ∩ p.2) :
    pib s k = p.1 ∩ p.2 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_inter.1 hk
  rw [pib, abl_of_mem hs hp hk1, bbl_of_mem hs hp hk2]

theorem inter_union_eq_left_uA (hs : Inv s) (hp : p ∈ s.1) (hq : q ∈ s.1) (hpq : p ≠ q)
    {β : Finset (Fin n)} (hβ : β ∈ s.2.1) (h : (β ∩ p.2).Nonempty) :
    β ∩ (p.2 ∪ q.2) = β ∩ p.2 := by
  have hz : β ∩ q.2 = ∅ :=
    Finset.not_nonempty_iff_eq_empty.1 fun hc => hpq (hs.uA β hβ p hp q hq h hc)
  rw [Finset.inter_union_distrib_left, hz, Finset.union_empty]

theorem union_inter_eq_left_uB (hs : Inv s) (hp : p ∈ s.1) (hq : q ∈ s.1) (hpq : p ≠ q)
    {γ : Finset (Fin n)} (hγ : γ ∈ s.2.2) (h : (γ ∩ p.1).Nonempty) :
    (p.1 ∪ q.1) ∩ γ = p.1 ∩ γ := by
  have hz : q.1 ∩ γ = ∅ := by
    refine Finset.not_nonempty_iff_eq_empty.1 fun hc => hpq (hs.uB γ hγ p hp q hq h ?_)
    rwa [Finset.inter_comm] at hc
  rw [Finset.union_inter_distrib_right, hz, Finset.union_empty]

theorem pend_coal (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) : pend (coalP s p q) = pend s := by
  change coverA (coalL s.1 p q) ∩ coverB (coalL s.1 p q) = coverA s.1 ∩ coverB s.1
  rw [coverA_coal hp hq, coverB_coal hp hq]

theorem pib_coal (hs : Inv s) (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) (hk : k ∉ pend s) :
    pib (coalP s p q) k = pib s k := by
  have hqL : q ∈ s.1 := Finset.mem_of_mem_erase hq
  have hqp : q ≠ p := Finset.ne_of_mem_erase hq
  have hpq : p ≠ q := fun hc => hqp hc.symm
  have hs' : Inv (coalP s p q) := hs.coal hp hq
  have hcovA : coverA (coalP s p q).1 = coverA s.1 := coverA_coal hp hq
  have hcovB : coverB (coalP s p q).1 = coverB s.1 := coverB_coal hp hq
  have hmL : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n) ∈ (coalP s p q).1 := Finset.mem_insert_self _ _
  by_cases hkA : k ∈ coverA s.1
  · have hkB : k ∉ coverB s.1 := fun hc => hk (mem_pend.2 ⟨hkA, hc⟩)
    have hkB' : k ∉ coverB (coalP s p q).1 := by rw [hcovB]; exact hkB
    obtain ⟨r, hrL, hkr⟩ := mem_coverA.1 hkA
    have hγ : blockOf s.2.2 k ∈ s.2.2 := blockOfB_mem hs hkB
    have hkγ : k ∈ blockOf s.2.2 k := mem_blockOfB hs hkB
    have hbbl : bbl (coalP s p q) k = blockOf s.2.2 k := bbl_of_not_cover hkB'
    rw [pib, pib, hbbl, bbl_of_not_cover hkB, abl_of_mem hs hrL hkr]
    by_cases hrp : r = p
    · have hkr' : k ∈ p.1 := hrp ▸ hkr
      rw [abl_of_mem hs' hmL (Finset.mem_union_left _ hkr'), hrp]
      exact union_inter_eq_left_uB hs hp hqL hpq hγ ⟨k, Finset.mem_inter.2 ⟨hkγ, hkr'⟩⟩
    · by_cases hrq : r = q
      · have hkr' : k ∈ q.1 := hrq ▸ hkr
        rw [abl_of_mem hs' hmL (Finset.mem_union_right _ hkr'), hrq,
          Finset.union_comm p.1 q.1]
        exact union_inter_eq_left_uB hs hqL hp hqp hγ ⟨k, Finset.mem_inter.2 ⟨hkγ, hkr'⟩⟩
      · have hrm : r ∈ (coalP s p q).1 :=
          Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hrL⟩⟩)
        rw [abl_of_mem hs' hrm hkr]
  · have hkA' : k ∉ coverA (coalP s p q).1 := by rw [hcovA]; exact hkA
    have hβ : blockOf s.2.1 k ∈ s.2.1 := blockOfA_mem hs hkA
    have hkβ : k ∈ blockOf s.2.1 k := mem_blockOfA hs hkA
    have habl : abl (coalP s p q) k = blockOf s.2.1 k := abl_of_not_cover hkA'
    rw [pib, pib, habl, abl_of_not_cover hkA]
    by_cases hkB : k ∈ coverB s.1
    · obtain ⟨r, hrL, hkr⟩ := mem_coverB.1 hkB
      rw [bbl_of_mem hs hrL hkr]
      by_cases hrp : r = p
      · have hkr' : k ∈ p.2 := hrp ▸ hkr
        rw [bbl_of_mem hs' hmL (Finset.mem_union_left _ hkr'), hrp]
        exact inter_union_eq_left_uA hs hp hqL hpq hβ ⟨k, Finset.mem_inter.2 ⟨hkβ, hkr'⟩⟩
      · by_cases hrq : r = q
        · have hkr' : k ∈ q.2 := hrq ▸ hkr
          rw [bbl_of_mem hs' hmL (Finset.mem_union_right _ hkr'), hrq,
            Finset.union_comm p.2 q.2]
          exact inter_union_eq_left_uA hs hqL hp hqp hβ ⟨k, Finset.mem_inter.2 ⟨hkβ, hkr'⟩⟩
        · have hrm : r ∈ (coalP s p q).1 :=
            Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hrL⟩⟩)
          rw [bbl_of_mem hs' hrm hkr]
    · have hkB' : k ∉ coverB (coalP s p q).1 := by rw [hcovB]; exact hkB
      rw [bbl_of_not_cover hkB', bbl_of_not_cover hkB]
      rfl

theorem emitStar_coal (hs : Inv s) (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) :
    emitStar (coalP s p q) = emitStar s := by
  rw [emitStar, emitStar, pend_coal hp hq]
  refine Finset.image_congr fun k hk => ?_
  exact pib_coal hs hp hq (Finset.mem_sdiff.1 (Finset.mem_coe.1 hk)).2

theorem sdiff_pend_mutA (hs : Inv s) (hp : p ∈ carA s.1) :
    Finset.univ \ pend (mutAP s p) = (Finset.univ \ pend s) ∪ (p.1 ∩ p.2) := by
  obtain ⟨hpL, -⟩ := mem_carA.1 hp
  have hcovA : coverA (mutAP s p).1 = coverA s.1 \ p.1 := coverA_mutA hs.wfp.wf hpL
  have hcovB : coverB (mutAP s p).1 = coverB s.1 := coverB_mutA hs.wfp.wf hpL
  have hstar : p.1 ∩ coverB s.1 = p.1 ∩ p.2 := inter_coverB hs hpL
  ext l
  constructor
  · intro hl
    have hl' : l ∉ pend (mutAP s p) := (Finset.mem_sdiff.1 hl).2
    by_cases hla : l ∈ coverA s.1
    · by_cases hlb : l ∈ coverB s.1
      · refine Finset.mem_union_right _ ?_
        have hlp : l ∈ p.1 := by
          by_contra hc
          refine hl' (mem_pend.2 ⟨?_, ?_⟩)
          · rw [hcovA]; exact Finset.mem_sdiff.2 ⟨hla, hc⟩
          · rw [hcovB]; exact hlb
        rw [← hstar]
        exact Finset.mem_inter.2 ⟨hlp, hlb⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
          fun hc => hlb (mem_pend.1 hc).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
        fun hc => hla (mem_pend.1 hc).1⟩)
  · intro hl
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ l, fun hc => ?_⟩
    have hcA : l ∈ coverA s.1 \ p.1 := by rw [← hcovA]; exact (mem_pend.1 hc).1
    have hcB : l ∈ coverB s.1 := by rw [← hcovB]; exact (mem_pend.1 hc).2
    rcases Finset.mem_union.1 hl with h | h
    · exact (Finset.mem_sdiff.1 h).2 (mem_pend.2 ⟨(Finset.mem_sdiff.1 hcA).1, hcB⟩)
    · exact (Finset.mem_sdiff.1 hcA).2 (Finset.mem_inter.1 h).1

theorem sdiff_pend_mutB (hs : Inv s) (hp : p ∈ carB s.1) :
    Finset.univ \ pend (mutBP s p) = (Finset.univ \ pend s) ∪ (p.1 ∩ p.2) := by
  obtain ⟨hpL, -⟩ := mem_carB.1 hp
  have hcovA : coverA (mutBP s p).1 = coverA s.1 := coverA_mutB hs.wfp.wf hpL
  have hcovB : coverB (mutBP s p).1 = coverB s.1 \ p.2 := coverB_mutB hs.wfp.wf hpL
  have hstar : coverA s.1 ∩ p.2 = p.1 ∩ p.2 := coverA_inter hs hpL
  ext l
  constructor
  · intro hl
    have hl' : l ∉ pend (mutBP s p) := (Finset.mem_sdiff.1 hl).2
    by_cases hla : l ∈ coverA s.1
    · by_cases hlb : l ∈ coverB s.1
      · refine Finset.mem_union_right _ ?_
        have hlp : l ∈ p.2 := by
          by_contra hc
          refine hl' (mem_pend.2 ⟨?_, ?_⟩)
          · rw [hcovA]; exact hla
          · rw [hcovB]; exact Finset.mem_sdiff.2 ⟨hlb, hc⟩
        rw [← hstar]
        exact Finset.mem_inter.2 ⟨hla, hlp⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
          fun hc => hlb (mem_pend.1 hc).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ l,
        fun hc => hla (mem_pend.1 hc).1⟩)
  · intro hl
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ l, fun hc => ?_⟩
    have hcA : l ∈ coverA s.1 := by rw [← hcovA]; exact (mem_pend.1 hc).1
    have hcB : l ∈ coverB s.1 \ p.2 := by rw [← hcovB]; exact (mem_pend.1 hc).2
    rcases Finset.mem_union.1 hl with h | h
    · exact (Finset.mem_sdiff.1 h).2 (mem_pend.2 ⟨hcA, (Finset.mem_sdiff.1 hcB).1⟩)
    · exact (Finset.mem_sdiff.1 hcB).2 (Finset.mem_inter.1 h).2

theorem bbl_mutA (hs : Inv s) (hp : p ∈ carA s.1) (k : Fin n) :
    bbl (mutAP s p) k = bbl s k := by
  obtain ⟨hpL, -⟩ := mem_carA.1 hp
  have hs' : Inv (mutAP s p) := hs.mutA hp
  have hcovB : coverB (mutAP s p).1 = coverB s.1 := coverB_mutA hs.wfp.wf hpL
  by_cases hkB : k ∈ coverB s.1
  · obtain ⟨r, hrL, hkr⟩ := mem_coverB.1 hkB
    by_cases hrp : r = p
    · have hkr' : k ∈ p.2 := hrp ▸ hkr
      have hne : p.2 ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨k, hkr'⟩
      have hmem : ((∅ : Finset (Fin n)), p.2) ∈ (mutAP s p).1 := mem_mutAL.2 (Or.inl ⟨hne, rfl⟩)
      rw [bbl_of_mem hs' hmem hkr', bbl_of_mem hs hpL hkr']
    · have hmem : r ∈ (mutAP s p).1 := erase_subset_mutAL (Finset.mem_erase.2 ⟨hrp, hrL⟩)
      rw [bbl_of_mem hs' hmem hkr, bbl_of_mem hs hrL hkr]
  · have hkB' : k ∉ coverB (mutAP s p).1 := by rw [hcovB]; exact hkB
    rw [bbl_of_not_cover hkB', bbl_of_not_cover hkB]
    rfl

theorem abl_mutB (hs : Inv s) (hp : p ∈ carB s.1) (k : Fin n) :
    abl (mutBP s p) k = abl s k := by
  obtain ⟨hpL, -⟩ := mem_carB.1 hp
  have hs' : Inv (mutBP s p) := hs.mutB hp
  have hcovA : coverA (mutBP s p).1 = coverA s.1 := coverA_mutB hs.wfp.wf hpL
  by_cases hkA : k ∈ coverA s.1
  · obtain ⟨r, hrL, hkr⟩ := mem_coverA.1 hkA
    by_cases hrp : r = p
    · have hkr' : k ∈ p.1 := hrp ▸ hkr
      have hne : p.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨k, hkr'⟩
      have hmem : (p.1, (∅ : Finset (Fin n))) ∈ (mutBP s p).1 := mem_mutBL.2 (Or.inl ⟨hne, rfl⟩)
      rw [abl_of_mem hs' hmem hkr', abl_of_mem hs hpL hkr']
    · have hmem : r ∈ (mutBP s p).1 := erase_subset_mutBL (Finset.mem_erase.2 ⟨hrp, hrL⟩)
      rw [abl_of_mem hs' hmem hkr, abl_of_mem hs hrL hkr]
  · have hkA' : k ∉ coverA (mutBP s p).1 := by rw [hcovA]; exact hkA
    rw [abl_of_not_cover hkA', abl_of_not_cover hkA]
    rfl

theorem abl_mutA (hs : Inv s) (hp : p ∈ carA s.1) (k : Fin n) :
    abl (mutAP s p) k = abl s k := by
  obtain ⟨hpL, -⟩ := mem_carA.1 hp
  have hs' : Inv (mutAP s p) := hs.mutA hp
  have hcovA : coverA (mutAP s p).1 = coverA s.1 \ p.1 := coverA_mutA hs.wfp.wf hpL
  by_cases hkp : k ∈ p.1
  · have hkA' : k ∉ coverA (mutAP s p).1 := by
      rw [hcovA]
      exact fun hc => (Finset.mem_sdiff.1 hc).2 hkp
    rw [abl_of_not_cover hkA', abl_of_mem hs hpL hkp]
    exact blockOf_eq hs'.partA (Finset.mem_insert_self _ _) hkp
  · by_cases hkA : k ∈ coverA s.1
    · obtain ⟨r, hrL, hkr⟩ := mem_coverA.1 hkA
      have hrp : r ≠ p := fun hc => hkp (hc ▸ hkr)
      have hmem : r ∈ (mutAP s p).1 := erase_subset_mutAL (Finset.mem_erase.2 ⟨hrp, hrL⟩)
      rw [abl_of_mem hs' hmem hkr, abl_of_mem hs hrL hkr]
    · have hkA' : k ∉ coverA (mutAP s p).1 := by
        rw [hcovA]
        exact fun hc => hkA (Finset.mem_sdiff.1 hc).1
      rw [abl_of_not_cover hkA', abl_of_not_cover hkA]
      exact blockOf_eq hs'.partA (Finset.mem_insert_of_mem (blockOfA_mem hs hkA))
        (mem_blockOfA hs hkA)

theorem bbl_mutB (hs : Inv s) (hp : p ∈ carB s.1) (k : Fin n) :
    bbl (mutBP s p) k = bbl s k := by
  obtain ⟨hpL, -⟩ := mem_carB.1 hp
  have hs' : Inv (mutBP s p) := hs.mutB hp
  have hcovB : coverB (mutBP s p).1 = coverB s.1 \ p.2 := coverB_mutB hs.wfp.wf hpL
  by_cases hkp : k ∈ p.2
  · have hkB' : k ∉ coverB (mutBP s p).1 := by
      rw [hcovB]
      exact fun hc => (Finset.mem_sdiff.1 hc).2 hkp
    rw [bbl_of_not_cover hkB', bbl_of_mem hs hpL hkp]
    exact blockOf_eq hs'.partB (Finset.mem_insert_self _ _) hkp
  · by_cases hkB : k ∈ coverB s.1
    · obtain ⟨r, hrL, hkr⟩ := mem_coverB.1 hkB
      have hrp : r ≠ p := fun hc => hkp (hc ▸ hkr)
      have hmem : r ∈ (mutBP s p).1 := erase_subset_mutBL (Finset.mem_erase.2 ⟨hrp, hrL⟩)
      rw [bbl_of_mem hs' hmem hkr, bbl_of_mem hs hrL hkr]
    · have hkB' : k ∉ coverB (mutBP s p).1 := by
        rw [hcovB]
        exact fun hc => hkB (Finset.mem_sdiff.1 hc).1
      rw [bbl_of_not_cover hkB', bbl_of_not_cover hkB]
      exact blockOf_eq hs'.partB (Finset.mem_insert_of_mem (blockOfB_mem hs hkB))
        (mem_blockOfB hs hkB)

theorem pib_mutA (hs : Inv s) (hp : p ∈ carA s.1) (k : Fin n) :
    pib (mutAP s p) k = pib s k := by
  rw [pib, pib, abl_mutA hs hp k, bbl_mutA hs hp k]

theorem pib_mutB (hs : Inv s) (hp : p ∈ carB s.1) (k : Fin n) :
    pib (mutBP s p) k = pib s k := by
  rw [pib, pib, abl_mutB hs hp k, bbl_mutB hs hp k]

theorem emitStar_mutA (hs : Inv s) (hp : p ∈ carA s.1) :
    emitStar (mutAP s p)
      = if p.1 ∩ p.2 = ∅ then emitStar s else insert (p.1 ∩ p.2) (emitStar s) := by
  obtain ⟨hpL, -⟩ := mem_carA.1 hp
  have h1 : (Finset.univ \ pend s).image (pib (mutAP s p)) = emitStar s := by
    rw [emitStar]
    exact Finset.image_congr fun k _ => pib_mutA hs hp k
  rw [emitStar, sdiff_pend_mutA hs hp, Finset.image_union, h1]
  split_ifs with h
  · rw [h]
    simp
  · have hne : (p.1 ∩ p.2).Nonempty := Finset.nonempty_iff_ne_empty.2 h
    have hval : ∀ k ∈ p.1 ∩ p.2, pib (mutAP s p) k = p.1 ∩ p.2 := fun k hk => by
      rw [pib_mutA hs hp k, pib_of_mem_star hs hpL hk]
    have h2 : (p.1 ∩ p.2).image (pib (mutAP s p)) = {p.1 ∩ p.2} := by
      ext δ
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hval k hk
      · rintro rfl
        obtain ⟨k, hk⟩ := hne
        exact ⟨k, hk, hval k hk⟩
    rw [h2, Finset.union_comm, ← Finset.insert_eq]

theorem emitStar_mutB (hs : Inv s) (hp : p ∈ carB s.1) :
    emitStar (mutBP s p)
      = if p.1 ∩ p.2 = ∅ then emitStar s else insert (p.1 ∩ p.2) (emitStar s) := by
  obtain ⟨hpL, -⟩ := mem_carB.1 hp
  have h1 : (Finset.univ \ pend s).image (pib (mutBP s p)) = emitStar s := by
    rw [emitStar]
    exact Finset.image_congr fun k _ => pib_mutB hs hp k
  rw [emitStar, sdiff_pend_mutB hs hp, Finset.image_union, h1]
  split_ifs with h
  · rw [h]
    simp
  · have hne : (p.1 ∩ p.2).Nonempty := Finset.nonempty_iff_ne_empty.2 h
    have hval : ∀ k ∈ p.1 ∩ p.2, pib (mutBP s p) k = p.1 ∩ p.2 := fun k hk => by
      rw [pib_mutB hs hp k, pib_of_mem_star hs hpL hk]
    have h2 : (p.1 ∩ p.2).image (pib (mutBP s p)) = {p.1 ∩ p.2} := by
      ext δ
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hval k hk
      · rintro rfl
        obtain ⟨k, hk⟩ := hne
        exact ⟨k, hk, hval k hk⟩
    rw [h2, Finset.union_comm, ← Finset.insert_eq]

theorem star_notMem_emitStar (hs : Inv s) (hp : p ∈ s.1) : p.1 ∩ p.2 ∉ emitStar s := by
  intro hc
  obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1 hc
  have hkp : k ∈ p.1 ∩ p.2 := hkeq ▸ mem_pib hs k
  obtain ⟨hk1, hk2⟩ := Finset.mem_inter.1 hkp
  exact (Finset.mem_sdiff.1 hk).2
    (mem_pend.2 ⟨mem_coverA.2 ⟨p, hp, hk1⟩, mem_coverB.2 ⟨p, hp, hk2⟩⟩)

theorem meet_eq_image {ζA ζB : Blocks n} (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA)
    (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB) :
    meet ζA ζB = Finset.univ.image fun k => blockOf ζA k ∩ blockOf ζB k := by
  ext δ
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hδ
    obtain ⟨hne, β, hβ, γ, hγ, hbg⟩ := mem_meet.1 hδ
    obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [← hbg] at hl
    obtain ⟨hlβ, hlγ⟩ := Finset.mem_inter.1 hl
    exact ⟨l, by rw [blockOf_eq hA hβ hlβ, blockOf_eq hB hγ hlγ, hbg]⟩
  · rintro ⟨l, rfl⟩
    exact mem_meet.2 ⟨Finset.nonempty_iff_ne_empty.1
        ⟨l, Finset.mem_inter.2 ⟨mem_blockOf hA (Finset.mem_univ l),
          mem_blockOf hB (Finset.mem_univ l)⟩⟩,
      _, blockOf_mem hA (Finset.mem_univ l), _, blockOf_mem hB (Finset.mem_univ l), rfl⟩

theorem emitStar_of_absorbed (hs : Inv s) (h : s.1 = ∅) : emitStar s = meet s.2.1 s.2.2 := by
  have hcA : coverA s.1 = ∅ := by rw [h]; simp [coverA]
  have hcB : coverB s.1 = ∅ := by rw [h]; simp [coverB]
  have hkA : ∀ k : Fin n, k ∉ coverA s.1 := fun k hk => by
    rw [hcA] at hk
    exact absurd hk (Finset.notMem_empty k)
  have hkB : ∀ k : Fin n, k ∉ coverB s.1 := fun k hk => by
    rw [hcB] at hk
    exact absurd hk (Finset.notMem_empty k)
  have hidx : Finset.univ \ pend s = (Finset.univ : Finset (Fin n)) := by
    change Finset.univ \ (coverA s.1 ∩ coverB s.1) = Finset.univ
    rw [hcA, Finset.empty_inter, Finset.sdiff_empty]
  have hpA : IsPartOf (Finset.univ : Finset (Fin n)) s.2.1 := by
    have h' := hs.partA
    rwa [hcA, Finset.sdiff_empty] at h'
  have hpB : IsPartOf (Finset.univ : Finset (Fin n)) s.2.2 := by
    have h' := hs.partB
    rwa [hcB, Finset.sdiff_empty] at h'
  rw [emitStar, hidx, meet_eq_image hpA hpB]
  refine Finset.image_congr fun k _ => ?_
  rw [pib, abl_of_not_cover (hkA k), bbl_of_not_cover (hkB k)]

theorem emitStar_initP : emitStar (initP n) = ∅ := by
  have hp : pend (initP n) = (Finset.univ : Finset (Fin n)) := by
    change coverA (fullState n) ∩ coverB (fullState n) = Finset.univ
    rw [coverA_fullState, coverB_fullState, Finset.inter_self]
  rw [emitStar, hp, Finset.sdiff_self]
  simp

end Rhone.Coalescent.PartitionCarryingChain
