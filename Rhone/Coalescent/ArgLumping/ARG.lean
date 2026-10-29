/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ArgLumping.Tags
public import Rhone.MarkovChain.ArgLumping.Lumping
public import Rhone.Coalescent.BranchLengthMoments.Branch

/-! # The trimmed ARG chain, the block-structure invariant, and the 15-tag lumping -/

@[expose] public section

namespace Rhone.Coalescent.ArgLumping

open Finset TwoLocusGenealogy

variable {n : ℕ}

def trimLin (l : Lin n) : Lin n :=
  (if l.1 = Finset.univ then ∅ else l.1, if l.2 = Finset.univ then ∅ else l.2)

def trim (L : Finset (Lin n)) : Finset (Lin n) := (L.image trimLin).erase (∅, ∅)

def coalT (L : Finset (Lin n)) (p q : Lin n) : Finset (Lin n) := trim (coalL L p q)

def recT (L : Finset (Lin n)) (p : Lin n) : Finset (Lin n) := trim (recL L p)

theorem trimLin_of_ne {l : Lin n} (h1 : l.1 ≠ Finset.univ) (h2 : l.2 ≠ Finset.univ) :
    trimLin l = l := by
  rw [trimLin, ite_eq_right h1, ite_eq_right h2]

structure InvSide (f : Lin n → Finset (Fin n)) (L : Finset (Lin n)) : Prop where
  disj : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → Disjoint (f p) (f q)
  notUniv : ∀ l ∈ L, f l ≠ Finset.univ
  part : (∀ l ∈ L, f l = ∅) ∨ L.biUnion f = Finset.univ

structure Inv (L : Finset (Lin n)) : Prop where
  wf : WF L
  trimA : ∀ l ∈ L, l.1 ≠ Finset.univ
  trimB : ∀ l ∈ L, l.2 ≠ Finset.univ
  partA : (∀ l ∈ L, l.1 = ∅) ∨ L.biUnion Prod.fst = Finset.univ
  partB : (∀ l ∈ L, l.2 = ∅) ∨ L.biUnion Prod.snd = Finset.univ

theorem Inv.sideA {L : Finset (Lin n)} (h : Inv L) : InvSide Prod.fst L :=
  ⟨h.wf.disjA, h.trimA, h.partA⟩

theorem Inv.sideB {L : Finset (Lin n)} (h : Inv L) : InvSide Prod.snd L :=
  ⟨h.wf.disjB, h.trimB, h.partB⟩

theorem biUnion_filter_ne_empty (f : Lin n → Finset (Fin n)) (L : Finset (Lin n)) :
    (L.filter fun l => f l ≠ ∅).biUnion f = L.biUnion f := by
  refine Finset.Subset.antisymm
    (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _)) ?_
  intro a ha
  rw [Finset.mem_biUnion] at ha ⊢
  obtain ⟨l, hl, hal⟩ := ha
  refine ⟨l, Finset.mem_filter.2 ⟨hl, ?_⟩, hal⟩
  intro h0
  rw [h0] at hal
  exact Finset.notMem_empty a hal

theorem InvSide.biUnion_eq_univ {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)}
    (h : InvSide f L) {l₀ : Lin n} (hl₀ : l₀ ∈ L) (hne : f l₀ ≠ ∅) :
    L.biUnion f = Finset.univ := by
  rcases h.part with hall | hcov
  · exact absurd (hall l₀ hl₀) hne
  · exact hcov

theorem InvSide.card_le_one {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L)
    {S : Finset (Fin n)} (hS : S.Nonempty) : (L.filter fun l => f l = S).card ≤ 1 := by
  refine Finset.card_le_one.2 fun p hp q hq => ?_
  rw [Finset.mem_filter] at hp hq
  by_contra hne
  obtain ⟨a, ha⟩ := hS
  exact (Finset.disjoint_left.1 (h.disj p hp.1 q hq.1 hne)) (by rw [hp.2]; exact ha)
    (by rw [hq.2]; exact ha)

theorem card_filter_ne_one {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L) :
    (L.filter fun l => f l ≠ ∅).card ≠ 1 := by
  intro hcard
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hcard
  have hlmem : l ∈ L.filter fun l => f l ≠ ∅ := by rw [hl]; exact Finset.mem_singleton_self l
  rw [Finset.mem_filter] at hlmem
  have hcov := h.biUnion_eq_univ hlmem.1 hlmem.2
  rw [← biUnion_filter_ne_empty f L, hl, Finset.singleton_biUnion] at hcov
  exact h.notUniv l hlmem.1 hcov

theorem retire_iff_side {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L)
    {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    f p ∪ f q = Finset.univ ↔
      (f p ≠ ∅ ∧ f q ≠ ∅ ∧ (L.filter fun l => f l ≠ ∅).card = 2) := by
  constructor
  · intro hu
    have hfp : f p ≠ ∅ := fun h0 =>
      h.notUniv q hq (by rw [← hu, h0, Finset.empty_union])
    have hfq : f q ≠ ∅ := fun h0 =>
      h.notUniv p hp (by rw [← hu, h0, Finset.union_empty])
    have hset : (L.filter fun l => f l ≠ ∅) = {p, q} := by
      refine Finset.Subset.antisymm (fun r hr => ?_) (fun r hr => ?_)
      · rw [Finset.mem_filter] at hr
        by_contra hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem
        push Not at hmem
        have hd : Disjoint (f r) (f p ∪ f q) :=
          Finset.disjoint_union_right.2 ⟨h.disj r hr.1 p hp hmem.1, h.disj r hr.1 q hq hmem.2⟩
        rw [hu] at hd
        exact hr.2 (Finset.eq_empty_iff_forall_notMem.2 fun a ha =>
          (Finset.disjoint_left.1 hd) ha (Finset.mem_univ a))
      · rw [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact Finset.mem_filter.2 ⟨hp, hfp⟩
        · exact Finset.mem_filter.2 ⟨hq, hfq⟩
    exact ⟨hfp, hfq, by rw [hset, Finset.card_pair hpq]⟩
  · rintro ⟨hfp, hfq, hcard⟩
    have hsub : ({p, q} : Finset (Lin n)) ⊆ L.filter fun l => f l ≠ ∅ := by
      intro r hr
      rw [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hp, hfp⟩
      · exact Finset.mem_filter.2 ⟨hq, hfq⟩
    have hset : ({p, q} : Finset (Lin n)) = L.filter fun l => f l ≠ ∅ :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hpq])
    have hcov := h.biUnion_eq_univ hp hfp
    rw [← biUnion_filter_ne_empty f L, ← hset, Finset.biUnion_insert,
      Finset.singleton_biUnion] at hcov
    exact hcov

theorem retire_iff {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    p.1 ∪ q.1 = Finset.univ ↔ (p.1 ≠ ∅ ∧ q.1 ≠ ∅ ∧ totA (proj HA HB L) = 2) := by
  rw [totA_eq]
  exact retire_iff_side hInv.sideA hp hq hpq

theorem retire_iff_B {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    p.2 ∪ q.2 = Finset.univ ↔ (p.2 ≠ ∅ ∧ q.2 ≠ ∅ ∧ totB (proj HA HB L) = 2) := by
  rw [totB_eq]
  exact retire_iff_side hInv.sideB hp hq hpq

theorem totA_ne_one {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) :
    totA (proj HA HB L) ≠ 1 := by
  rw [totA_eq]
  exact card_filter_ne_one hInv.sideA

theorem totB_ne_one {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) :
    totB (proj HA HB L) ≠ 1 := by
  rw [totB_eq]
  exact card_filter_ne_one hInv.sideB

theorem card_filter_eq_side {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L)
    {H : Finset (Fin n)} (hH : H.Nonempty) :
    (L.filter fun l => f l = H).card
      = if (L.filter fun l => tagOf H (f l) = Tag.R).card = 1
          ∧ (L.filter fun l => tagOf H (f l) = Tag.M).card = 0 then 1 else 0 := by
  have key : (∃ l ∈ L, f l = H) ↔
      ((L.filter fun l => tagOf H (f l) = Tag.R).card = 1
        ∧ (L.filter fun l => tagOf H (f l) = Tag.M).card = 0) := by
    constructor
    · rintro ⟨l, hl, hfl⟩
      have hR : (L.filter fun l' => tagOf H (f l') = Tag.R) = {l} := by
        refine Finset.Subset.antisymm (fun r hr => ?_) (fun r hr => ?_)
        · rw [Finset.mem_filter] at hr
          rw [Finset.mem_singleton]
          by_contra hne
          obtain ⟨hne', hsub⟩ := tagOf_eq_R_iff.1 hr.2
          obtain ⟨a, ha⟩ := hne'
          have hd := h.disj r hr.1 l hl hne
          rw [hfl] at hd
          exact (Finset.disjoint_left.1 hd) ha (hsub ha)
        · rw [Finset.mem_singleton] at hr
          subst hr
          exact Finset.mem_filter.2 ⟨hl, by
            rw [hfl]; exact tagOf_eq_R_iff.2 ⟨hH, Finset.Subset.refl H⟩⟩
      have hM : (L.filter fun l' => tagOf H (f l') = Tag.M) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro r hr hM'
        obtain ⟨h1, h2⟩ := tagOf_eq_M_iff.1 hM'
        by_cases hrl : r = l
        · subst hrl
          exact h1 (by rw [hfl])
        · exact h2 (by have hd := h.disj r hr l hl hrl; rwa [hfl] at hd)
      rw [hR, hM]
      exact ⟨Finset.card_singleton l, rfl⟩
    · rintro ⟨hR, hM⟩
      obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hR
      have hlmem : l ∈ L.filter fun l' => tagOf H (f l') = Tag.R := by
        rw [hl]; exact Finset.mem_singleton_self l
      rw [Finset.mem_filter] at hlmem
      obtain ⟨hne, hsub⟩ := tagOf_eq_R_iff.1 hlmem.2
      have hMempty : ∀ r ∈ L, tagOf H (f r) ≠ Tag.M := by
        intro r hr hM'
        have hmem : r ∈ L.filter fun l' => tagOf H (f l') = Tag.M :=
          Finset.mem_filter.2 ⟨hr, hM'⟩
        rw [Finset.card_eq_zero.1 hM] at hmem
        exact Finset.notMem_empty r hmem
      refine ⟨l, hlmem.1, Finset.Subset.antisymm hsub fun a ha => ?_⟩
      have hcov := h.biUnion_eq_univ hlmem.1 (Finset.nonempty_iff_ne_empty.1 hne)
      have hau : a ∈ L.biUnion f := by rw [hcov]; exact Finset.mem_univ a
      rw [Finset.mem_biUnion] at hau
      obtain ⟨l', hl', hal'⟩ := hau
      have htag : tagOf H (f l') = Tag.R := by
        cases hcase : tagOf H (f l') with
        | N =>
            exact absurd hal' (by rw [tagOf_eq_N_iff.1 hcase]; exact Finset.notMem_empty a)
        | R => rfl
        | BLU =>
            exact ((Finset.disjoint_left.1 (tagOf_eq_BLU_iff.1 hcase).2) hal' ha).elim
        | M => exact absurd hcase (hMempty l' hl')
      have hll : l' = l := by
        have hmem : l' ∈ L.filter fun z => tagOf H (f z) = Tag.R :=
          Finset.mem_filter.2 ⟨hl', htag⟩
        rw [hl, Finset.mem_singleton] at hmem
        exact hmem
      rw [← hll]
      exact hal'
  by_cases hex : ∃ l ∈ L, f l = H
  · rw [ite_eq_left (key.1 hex)]
    obtain ⟨l, hl, hfl⟩ := hex
    exact le_antisymm (h.card_le_one hH)
      (Finset.card_pos.2 ⟨l, Finset.mem_filter.2 ⟨hl, hfl⟩⟩)
  · rw [ite_eq_right fun hc => hex (key.2 hc), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun {l} hl hfl => hex ⟨l, hl, hfl⟩

theorem card_filter_eq_compl_side {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)}
    (h : InvSide f L) {H : Finset (Fin n)} (hHc : Hᶜ.Nonempty) :
    (L.filter fun l => f l = Hᶜ).card
      = if (L.filter fun l => tagOf H (f l) = Tag.BLU).card = 1
          ∧ (L.filter fun l => tagOf H (f l) = Tag.M).card = 0 then 1 else 0 := by
  have hstep := card_filter_eq_side h (H := Hᶜ) hHc
  simpa only [tagOf_compl, swapTag_eq_R_iff, swapTag_eq_M_iff] using hstep

theorem card_split_side {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L)
    {H : Finset (Fin n)} (hH : H.Nonempty) (hHc : Hᶜ.Nonempty) :
    (L.filter fun l => f l = H ∨ f l = Hᶜ).card
      = (if (L.filter fun l => tagOf H (f l) = Tag.R).card = 1
            ∧ (L.filter fun l => tagOf H (f l) = Tag.M).card = 0 then 1 else 0)
        + (if (L.filter fun l => tagOf H (f l) = Tag.BLU).card = 1
            ∧ (L.filter fun l => tagOf H (f l) = Tag.M).card = 0 then 1 else 0) := by
  have hne : H ≠ Hᶜ := by
    intro he
    obtain ⟨a, ha⟩ := hH
    exact (Finset.mem_compl.1 (he ▸ ha)) ha
  have hdisj : Disjoint (L.filter fun l => f l = H) (L.filter fun l => f l = Hᶜ) := by
    refine Finset.disjoint_left.2 fun r hr1 hr2 => ?_
    rw [Finset.mem_filter] at hr1 hr2
    exact hne (hr1.2.symm.trans hr2.2)
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj, card_filter_eq_side h hH,
    card_filter_eq_compl_side h hHc]

def rACount (H : Finset (Fin n)) (L : Finset (Lin n)) : ℕ :=
  (L.filter fun p => p.1 ∈ ({H, Hᶜ} : Finset (Finset (Fin n)))).card

theorem rACount_eq_of_proj {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (hA : HA.Nonempty) (hAc : HAᶜ.Nonempty) :
    rACount HA L
      = (if countA Tag.R (proj HA HB L) = 1 ∧ countA Tag.M (proj HA HB L) = 0 then 1 else 0)
        + (if countA Tag.BLU (proj HA HB L) = 1 ∧ countA Tag.M (proj HA HB L) = 0
            then 1 else 0) := by
  rw [countA_eq, countA_eq, countA_eq, ← card_split_side hInv.sideA hA hAc, rACount]
  exact congrArg Finset.card (Finset.filter_congr fun l _ => by simp)

def rBCount (H : Finset (Fin n)) (L : Finset (Lin n)) : ℕ :=
  (L.filter fun p => p.2 ∈ ({H, Hᶜ} : Finset (Finset (Fin n)))).card

theorem rBCount_eq_of_proj {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (hB : HB.Nonempty) (hBc : HBᶜ.Nonempty) :
    rBCount HB L
      = (if countB Tag.R (proj HA HB L) = 1 ∧ countB Tag.M (proj HA HB L) = 0 then 1 else 0)
        + (if countB Tag.BLU (proj HA HB L) = 1 ∧ countB Tag.M (proj HA HB L) = 0
            then 1 else 0) := by
  rw [countB_eq, countB_eq, countB_eq, ← card_split_side hInv.sideB hB hBc, rBCount]
  exact congrArg Finset.card (Finset.filter_congr fun l _ => by simp)

theorem rA_eq_rACount {KA KB : ℕ} (H : Finset (Fin n)) (t : TypedAncestralChain.TS n KA KB) :
    BranchLengthMoments.rA (BranchLengthMoments.splitFam H) t = (rACount H t.st.1 : ℝ) := by
  simp only [BranchLengthMoments.rA, BranchLengthMoments.splitFam, rACount]
  exact congrArg (fun m : ℕ => (m : ℝ)) (congrArg Finset.card
    (Finset.filter_congr fun _ _ => Iff.rfl))

theorem rA_eq_of_proj {KA KB : ℕ} {HA HB : Finset (Fin n)} (t : TypedAncestralChain.TS n KA KB)
    (hInv : Inv t.st.1) (hA : HA.Nonempty) (hAc : HAᶜ.Nonempty) :
    BranchLengthMoments.rA (BranchLengthMoments.splitFam HA) t
      = ((if countA Tag.R (proj HA HB t.st.1) = 1 ∧ countA Tag.M (proj HA HB t.st.1) = 0
            then 1 else 0)
        + (if countA Tag.BLU (proj HA HB t.st.1) = 1 ∧ countA Tag.M (proj HA HB t.st.1) = 0
            then 1 else 0) : ℕ) := by
  rw [rA_eq_rACount, rACount_eq_of_proj (HB := HB) hInv hA hAc]

theorem proj_congr_rA {KA KB : ℕ} {HA HB : Finset (Fin n)} (t t' : TypedAncestralChain.TS n KA KB)
    (hInv : Inv t.st.1) (hInv' : Inv t'.st.1) (hA : HA.Nonempty) (hAc : HAᶜ.Nonempty)
    (hproj : proj HA HB t.st.1 = proj HA HB t'.st.1) :
    BranchLengthMoments.rA (BranchLengthMoments.splitFam HA) t = BranchLengthMoments.rA
        (BranchLengthMoments.splitFam HA) t' := by
  rw [rA_eq_of_proj (HB := HB) t hInv hA hAc, rA_eq_of_proj (HB := HB) t' hInv' hA hAc, hproj]

def coalNew (p q : Lin n) : Lin n := trimLin (p.1 ∪ q.1, p.2 ∪ q.2)

theorem image_trimLin_eq_self {M : Finset (Lin n)} (h : ∀ l ∈ M, trimLin l = l) :
    M.image trimLin = M := by
  refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Finset.mem_image] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    rw [h l hl]
    exact hl
  · exact Finset.mem_image.2 ⟨x, hx, h x hx⟩

theorem trim_eq_self {M : Finset (Lin n)} (h1 : ∀ l ∈ M, trimLin l = l)
    (h2 : ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ∉ M) : trim M = M := by
  rw [trim, image_trimLin_eq_self h1, Finset.erase_eq_of_notMem h2]

theorem trim_insert {M : Finset (Lin n)} {m : Lin n} (h1 : ∀ l ∈ M, trimLin l = l)
    (h2 : ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ∉ M) :
    trim (insert m M) = if trimLin m = (∅, ∅) then M else insert (trimLin m) M := by
  rw [trim, Finset.image_insert, image_trimLin_eq_self h1]
  split_ifs with h
  · rw [h, Finset.erase_insert h2]
  · rw [Finset.erase_insert_of_ne h, Finset.erase_eq_of_notMem h2]

theorem empty_notMem_of_wf {L : Finset (Lin n)} (hw : WF L) :
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ∉ L := by
  intro hm
  rcases hw.carries _ hm with hc | hc <;> simp at hc

theorem coalT_eq {L : Finset (Lin n)} (hInv : Inv L) (p q : Lin n) :
    coalT L p q = if coalNew p q = (∅, ∅) then (L.erase p).erase q
      else insert (coalNew p q) ((L.erase p).erase q) := by
  have hfix : ∀ l ∈ (L.erase p).erase q, trimLin l = l := by
    intro l hl
    have hlL : l ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl)
    exact trimLin_of_ne (hInv.trimA l hlL) (hInv.trimB l hlL)
  have hne : ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ∉ (L.erase p).erase q := fun hm =>
    empty_notMem_of_wf hInv.wf (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
  rw [coalT, coalL, trim_insert hfix hne]
  rfl

theorem recT_eq_recL {L : Finset (Lin n)} (hInv : Inv L) {p : Lin n} (hp : p ∈ L)
    (h1 : p.1 ≠ ∅) (h2 : p.2 ≠ ∅) : recT L p = recL L p := by
  refine trim_eq_self (fun l hl => ?_) (fun hm => ?_)
  · rw [recL, Finset.mem_insert, Finset.mem_insert] at hl
    rcases hl with rfl | rfl | hl
    · rw [trimLin, ite_eq_right (hInv.trimA p hp)]
      simp only [Prod.mk.injEq, true_and]
      split_ifs <;> rfl
    · rw [trimLin, ite_eq_right (hInv.trimB p hp)]
      simp only [Prod.mk.injEq, and_true]
      split_ifs <;> rfl
    · have hlL : l ∈ L := Finset.mem_of_mem_erase hl
      exact trimLin_of_ne (hInv.trimA l hlL) (hInv.trimB l hlL)
  · rw [recL, Finset.mem_insert, Finset.mem_insert] at hm
    rcases hm with hm | hm | hm
    · exact h1 (congrArg Prod.fst hm).symm
    · exact h2 (congrArg Prod.snd hm).symm
    · exact empty_notMem_of_wf hInv.wf (Finset.mem_of_mem_erase hm)

theorem coalNew_notMem {L : Finset (Lin n)} (hw : WF L) {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) :
    coalNew p q ∉ (L.erase p).erase q := by
  intro hm
  have hmL : coalNew p q ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)
  have hmp : coalNew p q ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hm)
  have hmq : coalNew p q ≠ q := Finset.ne_of_mem_erase hm
  have hA : (coalNew p q).1 = ∅ := by
    have halt : (coalNew p q).1 = ∅ ∨ (coalNew p q).1 = p.1 ∪ q.1 := by
      rw [coalNew, trimLin]
      by_cases h : p.1 ∪ q.1 = Finset.univ
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    rcases halt with h | h
    · exact h
    · have hd : Disjoint (coalNew p q).1 (p.1 ∪ q.1) := Finset.disjoint_union_right.2
        ⟨hw.disjA _ hmL p hp hmp, hw.disjA _ hmL q hq hmq⟩
      rw [← h] at hd
      simpa using disjoint_self.1 hd
  have hB : (coalNew p q).2 = ∅ := by
    have halt : (coalNew p q).2 = ∅ ∨ (coalNew p q).2 = p.2 ∪ q.2 := by
      rw [coalNew, trimLin]
      by_cases h : p.2 ∪ q.2 = Finset.univ
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    rcases halt with h | h
    · exact h
    · have hd : Disjoint (coalNew p q).2 (p.2 ∪ q.2) := Finset.disjoint_union_right.2
        ⟨hw.disjB _ hmL p hp hmp, hw.disjB _ hmL q hq hmq⟩
      rw [← h] at hd
      simpa using disjoint_self.1 hd
  rcases hw.carries _ hmL with hc | hc
  · exact (Finset.nonempty_iff_ne_empty.1 hc) hA
  · exact (Finset.nonempty_iff_ne_empty.1 hc) hB

theorem comboOf_eq_NN_iff {HA HB : Finset (Fin n)} {l : Lin n} :
    comboOf HA HB l = (Tag.N, Tag.N) ↔ l = (∅, ∅) := by
  constructor
  · intro h
    exact Prod.ext (tagOf_eq_N_iff.1 (congrArg Prod.fst h))
      (tagOf_eq_N_iff.1 (congrArg Prod.snd h))
  · rintro rfl
    rw [comboOf, tagOf_empty, tagOf_empty]

theorem tagOf_trim_union {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (h : InvSide f L)
    {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) (H : Finset (Fin n)) :
    tagOf H (if f p ∪ f q = Finset.univ then ∅ else f p ∪ f q)
      = if tagOf H (f p) ≠ Tag.N ∧ tagOf H (f q) ≠ Tag.N
            ∧ (L.filter fun l => f l ≠ ∅).card = 2 then Tag.N
        else mergeTag (tagOf H (f p)) (tagOf H (f q)) := by
  have hiff : (f p ∪ f q = Finset.univ) ↔
      (tagOf H (f p) ≠ Tag.N ∧ tagOf H (f q) ≠ Tag.N
        ∧ (L.filter fun l => f l ≠ ∅).card = 2) := by
    rw [retire_iff_side h hp hq hpq]
    simp only [ne_eq, tagOf_eq_N_iff]
  by_cases hu : f p ∪ f q = Finset.univ
  · rw [ite_eq_left hu, ite_eq_left (hiff.1 hu), tagOf_empty]
  · rw [ite_eq_right hu, ite_eq_right fun hc => hu (hiff.2 hc), tagOf_union]

theorem comboOf_coalNew {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    comboOf HA HB (coalNew p q)
      = coalCombo (proj HA HB L) (comboOf HA HB p) (comboOf HA HB q) := by
  have hA := tagOf_trim_union hInv.sideA hp hq hpq HA
  have hB := tagOf_trim_union hInv.sideB hp hq hpq HB
  rw [← totA_eq HA HB L] at hA
  rw [← totB_eq HA HB L] at hB
  exact Prod.ext hA hB

theorem proj_insert {HA HB : Finset (Fin n)} {x : Lin n} {S : Finset (Lin n)} (hx : x ∉ S)
    (c : Tag × Tag) :
    proj HA HB (insert x S) c = indC (comboOf HA HB x) c + proj HA HB S c := by
  simp only [proj, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem fun hm => hx (Finset.mem_of_mem_filter _ hm), indC,
      ite_eq_left h]
    omega
  · rw [indC, ite_eq_right h]
    omega

theorem proj_pair_decomp {HA HB : Finset (Fin n)} {L : Finset (Lin n)} {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) (c : Tag × Tag) :
    proj HA HB L c = indC (comboOf HA HB p) c
      + (indC (comboOf HA HB q) c + proj HA HB ((L.erase p).erase q) c) := by
  have h1 : q ∈ L.erase p := Finset.mem_erase.2 ⟨fun h => hpq h.symm, hq⟩
  have h2 : q ∉ (L.erase p).erase q := Finset.notMem_erase q _
  have h3 : p ∉ insert q ((L.erase p).erase q) := by
    rw [Finset.mem_insert]
    push Not
    exact ⟨hpq, fun hm => (Finset.notMem_erase p L) (Finset.mem_of_mem_erase hm)⟩
  have hL : insert p (insert q ((L.erase p).erase q)) = L := by
    rw [Finset.insert_erase h1, Finset.insert_erase hp]
  conv_lhs => rw [← hL]
  rw [proj_insert h3, proj_insert h2]

theorem proj_coalT_add {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) (c : Tag × Tag) :
    proj HA HB (coalT L p q) c + indC (comboOf HA HB p) c + indC (comboOf HA HB q) c
      = proj HA HB L c
        + insC (coalCombo (proj HA HB L) (comboOf HA HB p) (comboOf HA HB q)) c := by
  have hnew := comboOf_coalNew (HA := HA) (HB := HB) hInv hp hq hpq
  have hdec := proj_pair_decomp (HA := HA) (HB := HB) hp hq hpq c
  rw [coalT_eq hInv p q]
  by_cases hm : coalNew p q = (∅, ∅)
  · have hNN : coalCombo (proj HA HB L) (comboOf HA HB p) (comboOf HA HB q)
        = (Tag.N, Tag.N) := by
      rw [← hnew]
      exact comboOf_eq_NN_iff.2 hm
    rw [ite_eq_left hm, insC, ite_eq_left hNN]
    omega
  · have hNN : coalCombo (proj HA HB L) (comboOf HA HB p) (comboOf HA HB q)
        ≠ (Tag.N, Tag.N) := by
      rw [← hnew]
      exact fun hc => hm (comboOf_eq_NN_iff.1 hc)
    rw [ite_eq_right hm, proj_insert (coalNew_notMem hInv.wf hp hq), insC, ite_eq_right hNN, hnew]
    omega

theorem proj_coalT {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    proj HA HB (coalT L p q)
      = coalC (proj HA HB L) (comboOf HA HB p) (comboOf HA HB q) := by
  funext c
  have h := proj_coalT_add (HA := HA) (HB := HB) hInv hp hq hpq c
  simp only [coalC]
  omega

theorem proj_recT_add {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) {p : Lin n}
    (hp : p ∈ L) (h1 : p.1 ≠ ∅) (h2 : p.2 ≠ ∅) (c : Tag × Tag) :
    proj HA HB (recT L p) c + indC (comboOf HA HB p) c
      = proj HA HB L c + indC ((comboOf HA HB p).1, Tag.N) c
        + indC (Tag.N, (comboOf HA HB p).2) c := by
  have h1' : p.1.Nonempty := Finset.nonempty_iff_ne_empty.2 h1
  have h2' : p.2.Nonempty := Finset.nonempty_iff_ne_empty.2 h2
  have hne1 : (p.1, (∅ : Finset (Fin n))) ∉ insert ((∅ : Finset (Fin n)), p.2) (L.erase p) := by
    rw [Finset.mem_insert]
    push Not
    exact ⟨fun hc => h1 (congrArg Prod.fst hc), mutB_not_mem hInv.wf hp h1'⟩
  have hne2 : ((∅ : Finset (Fin n)), p.2) ∉ L.erase p := mutA_not_mem hInv.wf hp h2'
  have hpL : p ∉ L.erase p := Finset.notMem_erase p L
  have hdec : proj HA HB L c = indC (comboOf HA HB p) c + proj HA HB (L.erase p) c := by
    conv_lhs => rw [← Finset.insert_erase hp]
    exact proj_insert hpL c
  rw [recT_eq_recL hInv hp h1 h2, recL, proj_insert hne1, proj_insert hne2]
  simp only [comboOf, tagOf_empty] at hdec ⊢
  omega

theorem proj_recT {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L) {p : Lin n}
    (hp : p ∈ L) (h1 : p.1 ≠ ∅) (h2 : p.2 ≠ ∅) :
    proj HA HB (recT L p) = recC (proj HA HB L) (comboOf HA HB p) := by
  funext c
  have h := proj_recT_add (HA := HA) (HB := HB) hInv hp h1 h2 c
  simp only [recC]
  omega

def recLins (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.1 ≠ ∅ ∧ p.2 ≠ ∅

def mOrd (C : Tag × Tag → ℕ) (i j : Tag × Tag) : ℕ :=
  if i = j then C i * C i - C i else C i * C j

variable {K : Type*}

noncomputable def qOff [Field K] (ρ : K) (L M : Finset (Lin n)) : K :=
  (((L.offDiag.filter fun pq => coalT L pq.1 pq.2 = M).card : ℕ) : K) / 2
    + ρ / 2 * ((((recLins L).filter fun p => recT L p = M).card : ℕ) : K)

noncomputable def qbarOff [Field K] (ρ : K) (C C' : Tag × Tag → ℕ) : K :=
  ((∑ ij ∈ Finset.univ.filter fun ij : (Tag × Tag) × (Tag × Tag) => coalC C ij.1 ij.2 = C',
      mOrd C ij.1 ij.2 : ℕ) : K) / 2
    + ρ / 2 * ((∑ k ∈ Finset.univ.filter fun k : Tag × Tag =>
        recC C k = C' ∧ k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N, C k : ℕ) : K)

theorem card_offDiag_fibre (HA HB : Finset (Fin n)) (L : Finset (Lin n))
    (ij : (Tag × Tag) × (Tag × Tag)) :
    (L.offDiag.filter fun pq => (comboOf HA HB pq.1, comboOf HA HB pq.2) = ij).card
      = mOrd (proj HA HB L) ij.1 ij.2 := by
  obtain ⟨i, j⟩ := ij
  by_cases hij : i = j
  · subst hij
    have hset : (L.offDiag.filter fun pq => (comboOf HA HB pq.1, comboOf HA HB pq.2) = (i, i))
        = (L.filter fun l => comboOf HA HB l = i).offDiag := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_offDiag, Prod.mk.injEq]
      tauto
    rw [hset, mOrd, ite_eq_left rfl, Finset.offDiag_card]
    rfl
  · have hset : (L.offDiag.filter fun pq => (comboOf HA HB pq.1, comboOf HA HB pq.2) = (i, j))
        = (L.filter fun l => comboOf HA HB l = i) ×ˢ (L.filter fun l => comboOf HA HB l = j) := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1, h2, _⟩, h3, h4⟩
        exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩
        exact ⟨⟨h1, h2, fun he => hij (by rw [← h3, he, h4])⟩, h3, h4⟩
    rw [hset, mOrd, ite_eq_right hij, Finset.card_product]
    rfl

theorem card_coal_fibre {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (C' : Tag × Tag → ℕ) :
    (L.offDiag.filter fun pq => proj HA HB (coalT L pq.1 pq.2) = C').card
      = ∑ ij ∈ Finset.univ.filter fun ij : (Tag × Tag) × (Tag × Tag) =>
          coalC (proj HA HB L) ij.1 ij.2 = C', mOrd (proj HA HB L) ij.1 ij.2 := by
  have hstep : (L.offDiag.filter fun pq => proj HA HB (coalT L pq.1 pq.2) = C')
      = L.offDiag.filter fun pq =>
          (comboOf HA HB pq.1, comboOf HA HB pq.2)
            ∈ Finset.univ.filter fun ij : (Tag × Tag) × (Tag × Tag) =>
                coalC (proj HA HB L) ij.1 ij.2 = C' := by
    refine Finset.filter_congr fun pq hpq => ?_
    rw [Finset.mem_offDiag] at hpq
    rw [proj_coalT hInv hpq.1 hpq.2.1 hpq.2.2]
    simp
  rw [hstep, ← Finset.sum_card_fiberwise_eq_card_filter L.offDiag _
    fun pq => (comboOf HA HB pq.1, comboOf HA HB pq.2)]
  exact Finset.sum_congr rfl fun ij _ => card_offDiag_fibre HA HB L ij

theorem card_recLins_fibre (HA HB : Finset (Fin n)) (L : Finset (Lin n)) (k : Tag × Tag) :
    ((recLins L).filter fun p => comboOf HA HB p = k).card
      = if k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N then proj HA HB L k else 0 := by
  have hkey : ∀ p : Lin n, comboOf HA HB p = k →
      ((p.1 ≠ ∅ ∧ p.2 ≠ ∅) ↔ (k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N)) := by
    intro p hc
    have h1 : tagOf HA p.1 = k.1 := congrArg Prod.fst hc
    have h2 : tagOf HB p.2 = k.2 := congrArg Prod.snd hc
    rw [← h1, ← h2, tagOf_ne_N_iff, tagOf_ne_N_iff]
  by_cases hk : k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N
  · rw [ite_eq_left hk]
    have hset : ((recLins L).filter fun p => comboOf HA HB p = k)
        = L.filter fun p => comboOf HA HB p = k := by
      ext p
      simp only [recLins, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, -⟩, hc⟩
        exact ⟨hp, hc⟩
      · rintro ⟨hp, hc⟩
        exact ⟨⟨hp, (hkey p hc).2 hk⟩, hc⟩
    rw [hset]
    rfl
  · rw [ite_eq_right hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp hc
    simp only [recLins, Finset.mem_filter] at hp
    exact hk ((hkey p hc).1 hp.2)

theorem card_rec_fibre {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (C' : Tag × Tag → ℕ) :
    ((recLins L).filter fun p => proj HA HB (recT L p) = C').card
      = ∑ k ∈ Finset.univ.filter fun k : Tag × Tag =>
          recC (proj HA HB L) k = C' ∧ k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N, proj HA HB L k := by
  have hstep : ((recLins L).filter fun p => proj HA HB (recT L p) = C')
      = (recLins L).filter fun p => comboOf HA HB p
          ∈ Finset.univ.filter fun k : Tag × Tag => recC (proj HA HB L) k = C' := by
    refine Finset.filter_congr fun p hp => ?_
    simp only [recLins, Finset.mem_filter] at hp
    rw [proj_recT hInv hp.1 hp.2.1 hp.2.2]
    simp
  rw [hstep, ← Finset.sum_card_fiberwise_eq_card_filter (recLins L) _ (comboOf HA HB),
    Finset.sum_congr rfl fun k _ => card_recLins_fibre HA HB L k, ← Finset.sum_filter,
    Finset.filter_filter]

theorem lump_rate_eq [Field K] {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (ρ : K) (C' : Tag × Tag → ℕ) :
    ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C', qOff ρ L M
      = qbarOff ρ (proj HA HB L) C' := by
  have hcoal : ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C',
        (L.offDiag.filter fun pq => coalT L pq.1 pq.2 = M).card
      = ∑ ij ∈ Finset.univ.filter fun ij : (Tag × Tag) × (Tag × Tag) =>
          coalC (proj HA HB L) ij.1 ij.2 = C', mOrd (proj HA HB L) ij.1 ij.2 := by
    rw [Finset.sum_card_fiberwise_eq_card_filter L.offDiag _ fun pq => coalT L pq.1 pq.2,
      ← card_coal_fibre hInv C']
    exact congrArg Finset.card (Finset.filter_congr fun pq _ => by simp)
  have hrec : ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C',
        ((recLins L).filter fun p => recT L p = M).card
      = ∑ k ∈ Finset.univ.filter fun k : Tag × Tag =>
          recC (proj HA HB L) k = C' ∧ k.1 ≠ Tag.N ∧ k.2 ≠ Tag.N, proj HA HB L k := by
    rw [Finset.sum_card_fiberwise_eq_card_filter (recLins L) _ fun p => recT L p,
      ← card_rec_fibre hInv C']
    exact congrArg Finset.card (Finset.filter_congr fun p _ => by simp)
  simp only [qOff, qbarOff]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum,
    ← Nat.cast_sum, hcoal, hrec]

theorem lump_rate [Field K] {HA HB : Finset (Fin n)} {L L' : Finset (Lin n)} (hInv : Inv L)
    (hInv' : Inv L') (hproj : proj HA HB L = proj HA HB L') (ρ : K) (C' : Tag × Tag → ℕ) :
    ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C', qOff ρ L M
      = ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C', qOff ρ L' M := by
  rw [lump_rate_eq hInv, lump_rate_eq hInv', hproj]

theorem biUnion_pair_decomp (f : Lin n → Finset (Fin n)) {L : Finset (Lin n)} {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    L.biUnion f = (f p ∪ f q) ∪ ((L.erase p).erase q).biUnion f := by
  have h1 : q ∈ L.erase p := Finset.mem_erase.2 ⟨fun h => hpq h.symm, hq⟩
  have hL : insert p (insert q ((L.erase p).erase q)) = L := by
    rw [Finset.insert_erase h1, Finset.insert_erase hp]
  conv_lhs => rw [← hL]
  rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]

theorem mem_coalT {L : Finset (Lin n)} (hInv : Inv L) (p q : Lin n) {l : Lin n}
    (hl : l ∈ coalT L p q) :
    (l = coalNew p q ∧ coalNew p q ≠ (∅, ∅)) ∨ l ∈ (L.erase p).erase q := by
  rw [coalT_eq hInv p q] at hl
  split_ifs at hl with hz
  · exact Or.inr hl
  · rcases Finset.mem_insert.1 hl with rfl | hl
    · exact Or.inl ⟨rfl, hz⟩
    · exact Or.inr hl

theorem invSide_coalT {f : Lin n → Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (h : InvSide f L) {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q)
    (hne : (∅ : Finset (Fin n)) ≠ Finset.univ)
    (hf0 : f ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) = ∅)
    (hfm : f (coalNew p q) = if f p ∪ f q = Finset.univ then ∅ else f p ∪ f q) :
    InvSide f (coalT L p q) := by
  have hSL : ∀ l ∈ (L.erase p).erase q, l ∈ L := fun l hl =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl)
  have hSp : ∀ l ∈ (L.erase p).erase q, l ≠ p := fun l hl =>
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
  have hSq : ∀ l ∈ (L.erase p).erase q, l ≠ q := fun l hl => Finset.ne_of_mem_erase hl
  have hdpq : ∀ l ∈ (L.erase p).erase q, Disjoint (f l) (f p ∪ f q) := fun l hl =>
    Finset.disjoint_union_right.2
      ⟨h.disj l (hSL l hl) p hp (hSp l hl), h.disj l (hSL l hl) q hq (hSq l hl)⟩
  have hdm : ∀ l ∈ (L.erase p).erase q, Disjoint (f l) (f (coalNew p q)) := by
    intro l hl
    rw [hfm]
    split_ifs with hu
    · exact Finset.disjoint_empty_right _
    · exact hdpq l hl
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hl' hll'
    rcases mem_coalT hInv p q hl with ⟨rfl, -⟩ | hlS
    · rcases mem_coalT hInv p q hl' with ⟨rfl, -⟩ | hl'S
      · exact absurd rfl hll'
      · exact (hdm l' hl'S).symm
    · rcases mem_coalT hInv p q hl' with ⟨rfl, -⟩ | hl'S
      · exact hdm l hlS
      · exact h.disj l (hSL l hlS) l' (hSL l' hl'S) hll'
  · intro l hl
    rcases mem_coalT hInv p q hl with ⟨rfl, -⟩ | hlS
    · rw [hfm]
      split_ifs with hu
      · exact hne
      · exact hu
    · exact h.notUniv l (hSL l hlS)
  · by_cases hu : f p ∪ f q = Finset.univ
    · refine Or.inl fun l hl => ?_
      rcases mem_coalT hInv p q hl with ⟨rfl, -⟩ | hlS
      · rw [hfm, ite_eq_left hu]
      · have hd := hdpq l hlS
        rw [hu] at hd
        exact Finset.eq_empty_iff_forall_notMem.2 fun a ha =>
          (Finset.disjoint_left.1 hd) ha (Finset.mem_univ a)
    · rcases h.part with hall | hcov
      · refine Or.inl fun l hl => ?_
        rcases mem_coalT hInv p q hl with ⟨rfl, -⟩ | hlS
        · rw [hfm, ite_eq_right hu, hall p hp, hall q hq, Finset.union_self]
        · exact hall l (hSL l hlS)
      · refine Or.inr ?_
        have hdec := biUnion_pair_decomp f hp hq hpq
        rw [hdec] at hcov
        rw [coalT_eq hInv p q]
        split_ifs with hz
        · have hz0 : f p ∪ f q = ∅ := by
            have := hfm
            rw [hz, hf0, ite_eq_right hu] at this
            exact this.symm
          rwa [hz0, Finset.empty_union] at hcov
        · rw [Finset.biUnion_insert, hfm, ite_eq_right hu]
          exact hcov

theorem inv_coalT {L : Finset (Lin n)} (hInv : Inv L) {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L)
    (hpq : p ≠ q) : Inv (coalT L p q) := by
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    have hex : ∃ a : Fin n, a ∈ (Finset.univ : Finset (Fin n)) := by
      rcases hInv.wf.carries p hp with hc | hc
      · obtain ⟨a, -⟩ := hc
        exact ⟨a, Finset.mem_univ a⟩
      · obtain ⟨a, -⟩ := hc
        exact ⟨a, Finset.mem_univ a⟩
    obtain ⟨a, ha⟩ := hex
    intro he
    exact Finset.notMem_empty a (by rw [he]; exact ha)
  have hA : InvSide Prod.fst (coalT L p q) :=
    invSide_coalT hInv hInv.sideA hp hq hpq hne rfl rfl
  have hB : InvSide Prod.snd (coalT L p q) :=
    invSide_coalT hInv hInv.sideB hp hq hpq hne rfl rfl
  have hcar : ∀ l ∈ coalT L p q, l.1.Nonempty ∨ l.2.Nonempty := by
    intro l hl
    rcases mem_coalT hInv p q hl with ⟨rfl, hz⟩ | hlS
    · by_contra hc
      push Not at hc
      exact hz (Prod.ext hc.1 hc.2)
    · exact hInv.wf.carries l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hlS))
  exact ⟨⟨hcar, hA.disj, hB.disj⟩, hA.notUniv, hB.notUniv, hA.part, hB.part⟩

theorem inv_recT {L : Finset (Lin n)} (hInv : Inv L) {p : Lin n} (hp : p ∈ L) (h1 : p.1 ≠ ∅)
    (h2 : p.2 ≠ ∅) : Inv (recT L p) := by
  have h1' : p.1.Nonempty := Finset.nonempty_iff_ne_empty.2 h1
  have h2' : p.2.Nonempty := Finset.nonempty_iff_ne_empty.2 h2
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    obtain ⟨a, -⟩ := h1'
    intro he
    exact Finset.notMem_empty a (by rw [he]; exact Finset.mem_univ a)
  have hbA : (recL L p).biUnion Prod.fst = L.biUnion Prod.fst := by
    ext a
    simp only [Finset.mem_biUnion, recL, Finset.mem_insert]
    constructor
    · rintro ⟨l, hl, hal⟩
      rcases hl with rfl | rfl | hl
      · exact ⟨p, hp, hal⟩
      · exact absurd hal (Finset.notMem_empty a)
      · exact ⟨l, Finset.mem_of_mem_erase hl, hal⟩
    · rintro ⟨l, hl, hal⟩
      by_cases hlp : l = p
      · subst hlp
        exact ⟨(l.1, ∅), Or.inl rfl, hal⟩
      · exact ⟨l, Or.inr (Or.inr (Finset.mem_erase.2 ⟨hlp, hl⟩)), hal⟩
  have hbB : (recL L p).biUnion Prod.snd = L.biUnion Prod.snd := by
    ext a
    simp only [Finset.mem_biUnion, recL, Finset.mem_insert]
    constructor
    · rintro ⟨l, hl, hal⟩
      rcases hl with rfl | rfl | hl
      · exact absurd hal (Finset.notMem_empty a)
      · exact ⟨p, hp, hal⟩
      · exact ⟨l, Finset.mem_of_mem_erase hl, hal⟩
    · rintro ⟨l, hl, hal⟩
      by_cases hlp : l = p
      · subst hlp
        exact ⟨(∅, l.2), Or.inr (Or.inl rfl), hal⟩
      · exact ⟨l, Or.inr (Or.inr (Finset.mem_erase.2 ⟨hlp, hl⟩)), hal⟩
  rw [recT_eq_recL hInv hp h1 h2]
  refine ⟨WF.recomb hInv.wf hp h1' h2', ?_, ?_, ?_, ?_⟩
  · intro l hl
    rw [recL, Finset.mem_insert, Finset.mem_insert] at hl
    rcases hl with rfl | rfl | hl
    · exact hInv.trimA p hp
    · exact hne
    · exact hInv.trimA l (Finset.mem_of_mem_erase hl)
  · intro l hl
    rw [recL, Finset.mem_insert, Finset.mem_insert] at hl
    rcases hl with rfl | rfl | hl
    · exact hne
    · exact hInv.trimB p hp
    · exact hInv.trimB l (Finset.mem_of_mem_erase hl)
  · rcases hInv.partA with hall | hcov
    · exact absurd (hall p hp) h1
    · exact Or.inr (by rw [hbA]; exact hcov)
  · rcases hInv.partB with hall | hcov
    · exact absurd (hall p hp) h2
    · exact Or.inr (by rw [hbB]; exact hcov)

def x0 (n : ℕ) : Finset (Lin n) := Finset.univ.image fun i : Fin n => ({i}, {i})

theorem mem_x0 {l : Lin n} : l ∈ x0 n ↔ ∃ i : Fin n, ({i}, {i}) = l := by
  simp [x0]

theorem inv_x0 (hn : 2 ≤ n) : Inv (x0 n) := by
  have hsing : ∀ i : Fin n, ({i} : Finset (Fin n)) ≠ Finset.univ := by
    intro i he
    have h1 : (Finset.univ : Finset (Fin n)).card = 1 := by
      rw [← he]
      exact Finset.card_singleton i
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hdisj : ∀ p ∈ x0 n, ∀ q ∈ x0 n, p ≠ q → Disjoint p.1 q.1 ∧ Disjoint p.2 q.2 := by
    intro p hp q hq hpq
    obtain ⟨i, rfl⟩ := mem_x0.1 hp
    obtain ⟨j, rfl⟩ := mem_x0.1 hq
    have hij : i ≠ j := fun h => hpq (by rw [h])
    exact ⟨by simpa using hij, by simpa using hij⟩
  have hcov : ∀ f : Lin n → Finset (Fin n), (∀ i : Fin n, i ∈ f ({i}, {i})) →
      (x0 n).biUnion f = Finset.univ := by
    intro f hf
    refine Finset.eq_univ_of_forall fun a => ?_
    rw [Finset.mem_biUnion]
    exact ⟨({a}, {a}), mem_x0.2 ⟨a, rfl⟩, hf a⟩
  refine ⟨⟨fun p hp => ?_, fun p hp q hq hpq => (hdisj p hp q hq hpq).1,
    fun p hp q hq hpq => (hdisj p hp q hq hpq).2⟩, fun l hl => ?_, fun l hl => ?_,
    Or.inr (hcov _ fun i => Finset.mem_singleton_self i),
    Or.inr (hcov _ fun i => Finset.mem_singleton_self i)⟩
  · obtain ⟨i, rfl⟩ := mem_x0.1 hp
    exact Or.inl (Finset.singleton_nonempty i)
  · obtain ⟨i, rfl⟩ := mem_x0.1 hl
    exact hsing i
  · obtain ⟨i, rfl⟩ := mem_x0.1 hl
    exact hsing i

theorem tagOf_singleton (H : Finset (Fin n)) (i : Fin n) :
    tagOf H {i} = if i ∈ H then Tag.R else Tag.BLU := by
  by_cases h : i ∈ H
  · rw [ite_eq_left h]
    exact tagOf_eq_R_iff.2 ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.2 h⟩
  · rw [ite_eq_right h]
    exact tagOf_eq_BLU_iff.2 ⟨Finset.singleton_nonempty i,
      Finset.disjoint_singleton_left.2 h⟩

theorem proj_x0 (HA HB : Finset (Fin n)) (c : Tag × Tag) :
    proj HA HB (x0 n) c
      = (Finset.univ.filter fun i : Fin n =>
          ((if i ∈ HA then Tag.R else Tag.BLU), (if i ∈ HB then Tag.R else Tag.BLU)) = c).card := by
  rw [proj, x0, Finset.filter_image, Finset.card_image_of_injective]
  · exact congrArg Finset.card (Finset.filter_congr fun i _ => by
      simp only [comboOf, tagOf_singleton])
  · intro i j hij
    exact Finset.singleton_injective (congrArg Prod.fst hij)

theorem proj_x0_RR (HA HB : Finset (Fin n)) :
    proj HA HB (x0 n) (Tag.R, Tag.R) = (HA ∩ HB).card := by
  rw [proj_x0]
  congr 1
  ext i
  simp [Prod.ext_iff]

theorem proj_x0_RBLU (HA HB : Finset (Fin n)) :
    proj HA HB (x0 n) (Tag.R, Tag.BLU) = (HA ∩ HBᶜ).card := by
  rw [proj_x0]
  congr 1
  ext i
  simp [Prod.ext_iff]

theorem proj_x0_BLUR (HA HB : Finset (Fin n)) :
    proj HA HB (x0 n) (Tag.BLU, Tag.R) = (HAᶜ ∩ HB).card := by
  rw [proj_x0]
  congr 1
  ext i
  simp [Prod.ext_iff]

theorem proj_x0_BLUBLU (HA HB : Finset (Fin n)) :
    proj HA HB (x0 n) (Tag.BLU, Tag.BLU) = (HAᶜ ∩ HBᶜ).card := by
  rw [proj_x0]
  congr 1
  ext i
  simp [Prod.ext_iff]

abbrev Sts (n : ℕ) : Type := {L : Finset (Lin n) // Inv L}

noncomputable instance instFintypeSts : Fintype (Sts n) := Fintype.ofFinite _

abbrev Cls (HA HB : Finset (Fin n)) : Type :=
  {C : Tag × Tag → ℕ // C ∈ (Finset.univ : Finset (Finset (Lin n))).image (proj HA HB)}

def projCls (HA HB : Finset (Fin n)) (L : Sts n) : Cls HA HB :=
  ⟨proj HA HB L.1, Finset.mem_image.2 ⟨L.1, Finset.mem_univ _, rfl⟩⟩

theorem mem_fibre_projCls {HA HB : Finset (Fin n)} {C : Cls HA HB} {z : Sts n} :
    z ∈ MarkovChain.ArgLumping.fibre (projCls HA HB) C ↔ proj HA HB z.1 = C.1 := by
  rw [MarkovChain.ArgLumping.mem_fibre, projCls, Subtype.ext_iff]

variable {K : Type*}

theorem qOff_eq_zero_of_not_inv [Field K] {L M : Finset (Lin n)} (hInv : Inv L) (hM : ¬ Inv M)
    (ρ : K) : qOff ρ L M = 0 := by
  have h1 : (L.offDiag.filter fun pq => coalT L pq.1 pq.2 = M) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro pq hpq hc
    rw [Finset.mem_offDiag] at hpq
    exact hM (hc ▸ inv_coalT hInv hpq.1 hpq.2.1 hpq.2.2)
  have h2 : ((recLins L).filter fun p => recT L p = M) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hc
    simp only [recLins, Finset.mem_filter] at hp
    exact hM (hc ▸ inv_recT hInv hp.1 hp.2.1 hp.2.2)
  rw [qOff, h1, h2]
  simp

theorem sum_fibre_qOff [Field K] {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hInv : Inv L)
    (ρ : K) (C : Cls HA HB) :
    ∑ z ∈ MarkovChain.ArgLumping.fibre (projCls HA HB) C, qOff ρ L z.1
      = ∑ M ∈ Finset.univ.filter fun M : Finset (Lin n) => proj HA HB M = C.1, qOff ρ L M := by
  have himg : ∀ x ∈ MarkovChain.ArgLumping.fibre (projCls HA HB) C, ∀ y ∈
      MarkovChain.ArgLumping.fibre (projCls HA HB) C,
      (x : Finset (Lin n)) = y → x = y := fun x _ y _ h => Subtype.ext h
  rw [← Finset.sum_image himg]
  refine Finset.sum_subset (fun M hM => ?_) (fun M hM hMn => ?_)
  · rw [Finset.mem_image] at hM
    obtain ⟨z, hz, rfl⟩ := hM
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_fibre_projCls.1 hz⟩
  · refine qOff_eq_zero_of_not_inv hInv (fun hInvM => hMn ?_) ρ
    rw [Finset.mem_filter] at hM
    exact Finset.mem_image.2 ⟨⟨M, hInvM⟩, mem_fibre_projCls.2 hM.2, rfl⟩

noncomputable def Qlit [Field K] (ρ : K) : Matrix (Sts n) (Sts n) K := fun x z =>
  if x = z then -∑ z' ∈ Finset.univ.erase x, qOff ρ x.1 z'.1 else qOff ρ x.1 z.1

noncomputable def Qlump [Field K] (HA HB : Finset (Fin n)) (ρ : K) :
    Matrix (Cls HA HB) (Cls HA HB) K := fun C D =>
  if C = D then -∑ D' ∈ Finset.univ.erase C, qbarOff ρ C.1 D'.1 else qbarOff ρ C.1 D.1

theorem sum_row_Qlit [Field K] (ρ : K) (x : Sts n) : ∑ z, Qlit ρ x z = 0 := by
  have h := Finset.add_sum_erase Finset.univ (fun z => Qlit (n := n) ρ x z) (Finset.mem_univ x)
  have hdiag : Qlit ρ x x = -∑ z' ∈ Finset.univ.erase x, qOff ρ x.1 z'.1 := by
    simp only [Qlit, ite_eq_left]
  have hoff : ∀ z ∈ Finset.univ.erase x, Qlit ρ x z = qOff ρ x.1 z.1 := by
    intro z hz
    simp only [Qlit]
    rw [ite_eq_right fun he => (Finset.ne_of_mem_erase hz) he.symm]
  rw [← h, hdiag, Finset.sum_congr rfl hoff, neg_add_cancel]

theorem sum_row_Qlump [Field K] (HA HB : Finset (Fin n)) (ρ : K) (C : Cls HA HB) :
    ∑ D, Qlump HA HB ρ C D = 0 := by
  have h := Finset.add_sum_erase Finset.univ (fun D => Qlump HA HB ρ C D) (Finset.mem_univ C)
  have hdiag : Qlump HA HB ρ C C = -∑ D' ∈ Finset.univ.erase C, qbarOff ρ C.1 D'.1 := by
    simp only [Qlump, ite_eq_left]
  have hoff : ∀ D ∈ Finset.univ.erase C, Qlump HA HB ρ C D = qbarOff ρ C.1 D.1 := by
    intro D hD
    simp only [Qlump]
    rw [ite_eq_right fun he => (Finset.ne_of_mem_erase hD) he.symm]
  rw [← h, hdiag, Finset.sum_congr rfl hoff, neg_add_cancel]

theorem isStrongLumping_projCls [Field K] (HA HB : Finset (Fin n)) (ρ : K) :
    MarkovChain.ArgLumping.IsStrongLumping (Qlit ρ) (projCls HA HB) (Qlump HA HB ρ) := by
  refine MarkovChain.ArgLumping.isStrongLumping_of_offDiag (fun x C hC => ?_) (sum_row_Qlit ρ)
      (sum_row_Qlump HA HB ρ)
  have hx : ∀ z ∈ MarkovChain.ArgLumping.fibre (projCls HA HB) C, Qlit ρ x z = qOff ρ x.1 z.1 := by
    intro z hz
    simp only [Qlit]
    refine ite_eq_right fun he => hC ?_
    rw [← he] at hz
    exact (MarkovChain.ArgLumping.mem_fibre.1 hz).symm
  rw [Finset.sum_congr rfl hx, sum_fibre_qOff x.2 ρ C, lump_rate_eq x.2 ρ C.1]
  simp only [Qlump]
  rw [ite_eq_right fun he => hC he.symm]
  rfl

theorem lump_matrix_projCls [Field K] (HA HB : Finset (Fin n)) (ρ : K) :
    Qlit ρ * (MarkovChain.ArgLumping.fib (projCls HA HB) : Matrix (Sts n) (Cls HA HB) K)
      = (MarkovChain.ArgLumping.fib (projCls HA HB) : Matrix (Sts n) (Cls HA HB) K) * Qlump HA HB
          ρ :=
  MarkovChain.ArgLumping.lump_matrix (isStrongLumping_projCls HA HB ρ)

def rAbar (HA HB : Finset (Fin n)) (C : Cls HA HB) : ℕ :=
  (if countA Tag.R C.1 = 1 ∧ countA Tag.M C.1 = 0 then 1 else 0)
    + (if countA Tag.BLU C.1 = 1 ∧ countA Tag.M C.1 = 0 then 1 else 0)

theorem rACount_comp [Field K] (HA HB : Finset (Fin n)) (hA : HA.Nonempty) (hAc : HAᶜ.Nonempty) :
    (fun L : Sts n => ((rACount HA L.1 : ℕ) : K))
      = (fun C : Cls HA HB => ((rAbar HA HB C : ℕ) : K)) ∘ projCls HA HB := by
  funext L
  simp only [Function.comp_apply]
  exact congrArg (fun m : ℕ => (m : K)) (rACount_eq_of_proj (HB := HB) L.2 hA hAc)

theorem pullback_u [Field K] (HA HB : Finset (Fin n)) (ρ : K)
    (hQ : Function.Injective (Qlit (n := n) (K := K) ρ).mulVec) {rbar ubar : Cls HA HB → K}
    (hu : (Qlump HA HB ρ).mulVec ubar = -rbar) {u : Sts n → K}
    (hu' : (Qlit ρ).mulVec u = -(rbar ∘ projCls HA HB)) : u = ubar ∘ projCls HA HB :=
  MarkovChain.ArgLumping.pullback_of_lump (isStrongLumping_projCls HA HB ρ) hQ hu hu'

theorem pullback_w_arg [Field K] (HA HB : Finset (Fin n)) {rA rB uA uB : Sts n → K}
    {rAb rBb uAb uBb : Cls HA HB → K} (hrA : rA = rAb ∘ projCls HA HB)
    (hrB : rB = rBb ∘ projCls HA HB) (huA : uA = uAb ∘ projCls HA HB)
    (huB : uB = uBb ∘ projCls HA HB) :
    (fun x => rA x * uB x + rB x * uA x)
      = (fun C => rAb C * uBb C + rBb C * uAb C) ∘ projCls HA HB :=
  MarkovChain.ArgLumping.pullback_w hrA hrB huA huB

end Rhone.Coalescent.ArgLumping
