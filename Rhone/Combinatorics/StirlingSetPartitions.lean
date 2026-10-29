/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Combinatorics.StirlingSecond
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Card

/-! # Stirling numbers count set partitions -/

@[expose] public section

namespace Rhone.Combinatorics

open Finset

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

def IsSetPartition (s : Finset α) (ζ : Finset (Finset α)) : Prop :=
  ∅ ∉ ζ ∧ (∀ B ∈ ζ, B ⊆ s) ∧ (∀ B ∈ ζ, ∀ C ∈ ζ, B ≠ C → Disjoint B C) ∧
    ∀ x ∈ s, ∃ B ∈ ζ, x ∈ B

open scoped Classical in
noncomputable def allSetPartitions (s : Finset α) : Finset (Finset (Finset α)) :=
  s.powerset.powerset.filter (IsSetPartition s)

noncomputable def setPartitions (s : Finset α) (k : ℕ) : Finset (Finset (Finset α)) :=
  (allSetPartitions s).filter (fun ζ => ζ.card = k)

theorem mem_allSetPartitions {s : Finset α} {ζ : Finset (Finset α)} :
    ζ ∈ allSetPartitions s ↔ IsSetPartition s ζ := by
  classical
  unfold allSetPartitions
  rw [mem_filter, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨fun B hB => ?_, h⟩⟩
  rw [mem_powerset]
  exact h.2.1 B hB

theorem mem_setPartitions {s : Finset α} {k : ℕ} {ζ : Finset (Finset α)} :
    ζ ∈ setPartitions s k ↔ IsSetPartition s ζ ∧ ζ.card = k := by
  unfold setPartitions
  rw [mem_filter, mem_allSetPartitions]

def addElem (a : α) (ζ : Finset (Finset α)) : Option (Finset α) → Finset (Finset α)
  | none => insert {a} ζ
  | some B => insert (insert a B) (ζ.erase B)

theorem image_erase_of_forall {t : Finset (Finset α)} {a : α} (h : ∀ B ∈ t, a ∉ B) :
    t.image (fun B => B.erase a) = t := by
  ext C
  simp only [mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    rw [erase_eq_of_notMem (h B hB)]
    exact hB
  · intro hC
    exact ⟨C, hC, erase_eq_of_notMem (h C hC)⟩

def dropElem (a : α) (η : Finset (Finset α)) : Finset (Finset α) :=
  (η.image (fun B => B.erase a)).erase ∅

section Basic

variable {s : Finset α} {ζ : Finset (Finset α)} {a : α}

theorem IsSetPartition.notMem_of_mem (hζ : IsSetPartition s ζ) (ha : a ∉ s) {B : Finset α}
    (hB : B ∈ ζ) : a ∉ B := fun h => ha (hζ.2.1 B hB h)

theorem IsSetPartition.nonempty_of_mem (hζ : IsSetPartition s ζ) {B : Finset α}
    (hB : B ∈ ζ) : B.Nonempty := by
  rcases B.eq_empty_or_nonempty with h | h
  · exact absurd (h ▸ hB) hζ.1
  · exact h

theorem isSetPartition_addElem (hζ : IsSetPartition s ζ) (ha : a ∉ s) {o : Option (Finset α)}
    (ho : o ∈ insertNone ζ) : IsSetPartition (insert a s) (addElem a ζ o) := by
  obtain ⟨h0, hsub, hdis, hcov⟩ := hζ
  have hnot : ∀ B ∈ ζ, a ∉ B := fun B hB h => ha (hsub B hB h)
  cases o with
  | none =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [addElem, mem_insert, not_or]
      exact ⟨fun h => by simpa using congrArg (a ∈ ·) h, h0⟩
    · intro B hB
      simp only [addElem, mem_insert] at hB
      rcases hB with rfl | hB
      · simp
      · exact (hsub B hB).trans (subset_insert _ _)
    · intro B hB C hC hne
      simp only [addElem, mem_insert] at hB hC
      rcases hB with rfl | hB <;> rcases hC with rfl | hC
      · exact absurd rfl hne
      · exact disjoint_singleton_left.2 (hnot C hC)
      · exact disjoint_singleton_right.2 (hnot B hB)
      · exact hdis B hB C hC hne
    · intro x hx
      by_cases hxa : x = a
      · exact ⟨{a}, by simp [addElem], by simp [hxa]⟩
      · have hxs : x ∈ s := by simpa [hxa] using hx
        obtain ⟨B, hB, hxB⟩ := hcov x hxs
        exact ⟨B, by simp [addElem, hB], hxB⟩
  | some B =>
    have hB : B ∈ ζ := by simpa using ho
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [addElem, mem_insert, not_or]
      refine ⟨fun h => by simpa using congrArg (a ∈ ·) h, fun h => h0 (mem_of_mem_erase h)⟩
    · intro C hC
      simp only [addElem, mem_insert] at hC
      rcases hC with rfl | hC
      · exact insert_subset_insert a (hsub B hB)
      · exact (hsub C (mem_of_mem_erase hC)).trans (subset_insert _ _)
    · intro C hC D hD hne
      simp only [addElem, mem_insert] at hC hD
      rcases hC with rfl | hC <;> rcases hD with rfl | hD
      · exact absurd rfl hne
      · exact disjoint_insert_left.2 ⟨hnot D (mem_of_mem_erase hD),
          hdis B hB D (mem_of_mem_erase hD) (Ne.symm (ne_of_mem_erase hD))⟩
      · exact (disjoint_insert_left.2 ⟨hnot C (mem_of_mem_erase hC),
          hdis B hB C (mem_of_mem_erase hC) (Ne.symm (ne_of_mem_erase hC))⟩).symm
      · exact hdis C (mem_of_mem_erase hC) D (mem_of_mem_erase hD) hne
    · intro x hx
      by_cases hxa : x = a
      · exact ⟨insert a B, by simp [addElem], by simp [hxa]⟩
      · have hxs : x ∈ s := by simpa [hxa] using hx
        obtain ⟨C, hC, hxC⟩ := hcov x hxs
        by_cases hCB : C = B
        · exact ⟨insert a B, by simp [addElem], by simp [← hCB, hxC]⟩
        · exact ⟨C, by simp [addElem, hC, hCB], hxC⟩

theorem card_addElem (hζ : IsSetPartition s ζ) (ha : a ∉ s) {o : Option (Finset α)}
    (ho : o ∈ insertNone ζ) :
    (addElem a ζ o).card = if o = none then ζ.card + 1 else ζ.card := by
  cases o with
  | none =>
    have : {a} ∉ ζ := fun h => ha (hζ.2.1 _ h (mem_singleton_self a))
    simp [addElem, card_insert_of_notMem this]
  | some B =>
    have hB : B ∈ ζ := by simpa using ho
    have hnot : insert a B ∉ ζ.erase B := fun h =>
      ha (hζ.2.1 _ (mem_of_mem_erase h) (mem_insert_self a B))
    rw [addElem, card_insert_of_notMem hnot, card_erase_of_mem hB]
    have := card_pos.2 ⟨B, hB⟩
    simp
    omega

theorem dropElem_addElem (hζ : IsSetPartition s ζ) (ha : a ∉ s) {o : Option (Finset α)}
    (ho : o ∈ insertNone ζ) : dropElem a (addElem a ζ o) = ζ := by
  have hid : ζ.image (fun B => B.erase a) = ζ :=
    image_erase_of_forall (fun B hB => hζ.notMem_of_mem ha hB)
  cases o with
  | none =>
    unfold dropElem addElem
    rw [image_insert, hid]
    simp only [erase_singleton]
    rw [erase_insert hζ.1]
  | some B =>
    have hB : B ∈ ζ := by simpa using ho
    have hBa : a ∉ B := hζ.notMem_of_mem ha hB
    unfold dropElem addElem
    rw [image_insert, erase_insert_of_ne, erase_insert hBa]
    · have : (ζ.erase B).image (fun B => B.erase a) = ζ.erase B :=
        image_erase_of_forall (fun C hC => hζ.notMem_of_mem ha (mem_of_mem_erase hC))
      rw [this, erase_eq_of_notMem (fun h => hζ.1 (mem_of_mem_erase h)), insert_erase hB]
    · intro h
      have := (hζ.nonempty_of_mem hB)
      rw [erase_insert hBa] at h
      exact this.ne_empty h

theorem addElem_inj {ζ' : Finset (Finset α)} (hζ : IsSetPartition s ζ)
    (hζ' : IsSetPartition s ζ') (ha : a ∉ s) {o o' : Option (Finset α)}
    (ho : o ∈ insertNone ζ) (ho' : o' ∈ insertNone ζ')
    (h : addElem a ζ o = addElem a ζ' o') : ζ = ζ' ∧ o = o' := by
  have hz : ζ = ζ' := by
    rw [← dropElem_addElem hζ ha ho, ← dropElem_addElem hζ' ha ho', h]
  subst hz
  refine ⟨rfl, ?_⟩
  have hne : ∀ {B : Finset α}, B ∈ ζ → ¬ (insert a B = {a}) := by
    intro B hB hh
    have hBa : B ⊆ {a} := fun x hx => hh ▸ mem_insert_of_mem hx
    obtain ⟨x, hx⟩ := hζ.nonempty_of_mem hB
    have : x = a := mem_singleton.1 (hBa hx)
    exact ha (this ▸ hζ.2.1 B hB hx)
  have hsing : {a} ∉ ζ := fun hh => ha (hζ.2.1 _ hh (mem_singleton_self a))
  have hins : ∀ {B : Finset α}, B ∈ ζ → insert a B ∉ ζ := fun {B} hB hh =>
    ha (hζ.2.1 _ hh (mem_insert_self a B))
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some B' =>
      have hB' : B' ∈ ζ := by simpa using ho'
      have : {a} ∈ addElem a ζ (some B') := h ▸ (by simp [addElem])
      simp only [addElem, mem_insert] at this
      rcases this with h1 | h1
      · exact absurd h1.symm (hne hB')
      · exact absurd (mem_of_mem_erase h1) hsing
  | some B =>
    have hB : B ∈ ζ := by simpa using ho
    cases o' with
    | none =>
      have : {a} ∈ addElem a ζ (some B) := h ▸ (by simp [addElem])
      simp only [addElem, mem_insert] at this
      rcases this with h1 | h1
      · exact absurd h1.symm (hne hB)
      · exact absurd (mem_of_mem_erase h1) hsing
    | some B' =>
      have hB' : B' ∈ ζ := by simpa using ho'
      have : insert a B ∈ addElem a ζ (some B') := h ▸ (by simp [addElem])
      simp only [addElem, mem_insert] at this
      rcases this with h1 | h1
      · have hBa := hζ.notMem_of_mem ha hB
        have hBa' := hζ.notMem_of_mem ha hB'
        have := congrArg (fun C => C.erase a) h1
        simp only [erase_insert hBa, erase_insert hBa'] at this
        rw [this]
      · exact absurd (mem_of_mem_erase h1) (hins hB)

theorem exists_addElem {η : Finset (Finset α)} (hη : IsSetPartition (insert a s) η)
    (ha : a ∉ s) :
    ∃ ζ, IsSetPartition s ζ ∧ ∃ o ∈ insertNone ζ, addElem a ζ o = η := by
  obtain ⟨h0, hsub, hdis, hcov⟩ := hη
  obtain ⟨C, hC, haC⟩ := hcov a (mem_insert_self a s)
  have huniq : ∀ D ∈ η, a ∈ D → D = C := by
    intro D hD haD
    by_contra hne
    exact (disjoint_left.1 (hdis D hD C hC hne)) haD haC
  have hCne : C.Nonempty := ⟨a, haC⟩
  by_cases hCa : C = {a}
  · subst hCa
    refine ⟨η.erase {a}, ⟨?_, ?_, ?_, ?_⟩, none, by simp, ?_⟩
    · exact fun h => h0 (mem_of_mem_erase h)
    · intro D hD
      have hDa : a ∉ D := fun h => (ne_of_mem_erase hD) (huniq D (mem_of_mem_erase hD) h)
      intro x hx
      have := hsub D (mem_of_mem_erase hD) hx
      rcases mem_insert.1 this with rfl | h
      · exact absurd hx hDa
      · exact h
    · intro D hD E hE hne
      exact hdis D (mem_of_mem_erase hD) E (mem_of_mem_erase hE) hne
    · intro x hx
      obtain ⟨D, hD, hxD⟩ := hcov x (mem_insert_of_mem hx)
      refine ⟨D, mem_erase.2 ⟨?_, hD⟩, hxD⟩
      rintro rfl
      exact ha ((mem_singleton.1 hxD) ▸ hx)
    · simp [addElem, insert_erase hC]
  · set B := C.erase a with hB
    have hBne : B.Nonempty := by
      by_contra hh
      rw [not_nonempty_iff_eq_empty, hB, erase_eq_empty_iff] at hh
      rcases hh with h | h
      · exact hCne.ne_empty h
      · exact hCa h
    have haB : a ∉ B := notMem_erase a C
    have hCB : insert a B = C := insert_erase haC
    have hBC : B ⊆ C := erase_subset a C
    have hBs : B ⊆ s := by
      intro x hx
      have := hsub C hC (hBC hx)
      rcases mem_insert.1 this with rfl | h
      · exact absurd hx haB
      · exact h
    have hBnot : B ∉ η.erase C := by
      intro h
      have hBη := mem_of_mem_erase h
      obtain ⟨x, hx⟩ := hBne
      by_cases hBeq : B = C
      · exact haB (hBeq ▸ haC)
      · exact (disjoint_left.1 (hdis B hBη C hC hBeq)) hx (hBC hx)
    refine ⟨insert B (η.erase C), ⟨?_, ?_, ?_, ?_⟩, some B, by simp, ?_⟩
    · simp only [mem_insert, not_or]
      exact ⟨hBne.ne_empty.symm, fun h => h0 (mem_of_mem_erase h)⟩
    · intro D hD
      rcases mem_insert.1 hD with rfl | hD
      · exact hBs
      · have hDa : a ∉ D := fun h => (ne_of_mem_erase hD) (huniq D (mem_of_mem_erase hD) h)
        intro x hx
        have := hsub D (mem_of_mem_erase hD) hx
        rcases mem_insert.1 this with rfl | h
        · exact absurd hx hDa
        · exact h
    · intro D hD E hE hne
      have hD' : ∀ D', D' ∈ η.erase C → Disjoint B D' := fun D' hD' =>
        (hdis C hC D' (mem_of_mem_erase hD') (Ne.symm (ne_of_mem_erase hD'))).mono_left hBC
      rcases mem_insert.1 hD with rfl | hD <;> rcases mem_insert.1 hE with rfl | hE
      · exact absurd rfl hne
      · exact hD' E hE
      · exact (hD' D hD).symm
      · exact hdis D (mem_of_mem_erase hD) E (mem_of_mem_erase hE) hne
    · intro x hx
      obtain ⟨D, hD, hxD⟩ := hcov x (mem_insert_of_mem hx)
      by_cases hDC : D = C
      · subst hDC
        refine ⟨B, mem_insert_self _ _, mem_erase.2 ⟨?_, hxD⟩⟩
        rintro rfl
        exact ha hx
      · exact ⟨D, mem_insert_of_mem (mem_erase.2 ⟨hDC, hD⟩), hxD⟩
    · simp only [addElem, hCB]
      rw [erase_insert hBnot]
      exact insert_erase hC

end Basic

theorem setPartitions_empty_zero : setPartitions (∅ : Finset α) 0 = {∅} := by
  ext ζ
  rw [mem_setPartitions, mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact card_eq_zero.1 h
  · rintro rfl
    refine ⟨⟨by simp, by simp, by simp, by simp⟩, by simp⟩

theorem setPartitions_empty_succ (k : ℕ) : setPartitions (∅ : Finset α) (k + 1) = ∅ := by
  ext ζ
  simp only [mem_setPartitions, notMem_empty, iff_false, not_and]
  intro ⟨h0, hsub, _, _⟩ hc
  obtain ⟨B, hB⟩ := card_pos.1 (by omega : 0 < ζ.card)
  have := hsub B hB
  rw [subset_empty] at this
  exact h0 (this ▸ hB)

theorem setPartitions_insert_zero {s : Finset α} {a : α} :
    setPartitions (insert a s) 0 = ∅ := by
  ext ζ
  simp only [mem_setPartitions, notMem_empty, iff_false, not_and]
  intro ⟨_, _, _, hcov⟩ hc
  obtain ⟨B, hB, _⟩ := hcov a (mem_insert_self a s)
  have := card_pos.2 ⟨B, hB⟩
  omega

theorem card_setPartitions_insert_succ {s : Finset α} {a : α} (ha : a ∉ s) (k : ℕ) :
    (setPartitions (insert a s) (k + 1)).card =
      (k + 1) * (setPartitions s (k + 1)).card + (setPartitions s k).card := by
  classical
  let A : Finset (Finset (Finset α)) := (setPartitions s k).image (fun ζ => addElem a ζ none)
  let Bs : Finset (Σ _ : Finset (Finset α), Finset α) :=
    (setPartitions s (k + 1)).sigma (fun ζ => ζ)
  let F : (Σ _ : Finset (Finset α), Finset α) → Finset (Finset α) :=
    fun p => addElem a p.1 (some p.2)
  have hsplit : setPartitions (insert a s) (k + 1) = A ∪ Bs.image F := by
    ext η
    simp only [mem_setPartitions, mem_union, A, Bs, F, mem_image, mem_sigma]
    constructor
    · rintro ⟨hη, hc⟩
      obtain ⟨ζ, hζ, o, ho, rfl⟩ := exists_addElem hη ha
      rw [card_addElem hζ ha ho] at hc
      cases o with
      | none =>
        left
        refine ⟨ζ, ⟨hζ, ?_⟩, rfl⟩
        simpa using hc
      | some B =>
        right
        refine ⟨⟨ζ, B⟩, ⟨⟨hζ, ?_⟩, by simpa using ho⟩, rfl⟩
        simpa using hc
    · rintro (⟨ζ, ⟨hζ, hc⟩, rfl⟩ | ⟨⟨ζ, B⟩, ⟨⟨hζ, hc⟩, hB⟩, rfl⟩)
      · refine ⟨isSetPartition_addElem hζ ha (by simp), ?_⟩
        rw [card_addElem hζ ha (by simp)]
        simp [hc]
      · simp only at hB hc
        refine ⟨isSetPartition_addElem hζ ha (by simpa using hB), ?_⟩
        rw [card_addElem hζ ha (by simpa using hB)]
        simp [hc]
  have hdisj : Disjoint A (Bs.image F) := by
    rw [disjoint_left]
    intro η hηA hηB
    simp only [A, Bs, F, mem_image, mem_sigma, mem_setPartitions] at hηA hηB
    obtain ⟨ζ, ⟨hζ, _⟩, rfl⟩ := hηA
    obtain ⟨⟨ζ', B⟩, ⟨⟨hζ', _⟩, hB⟩, h⟩ := hηB
    have := addElem_inj hζ hζ' ha (by simp) (by simpa using hB) h.symm
    simp at this
  have hA : A.card = (setPartitions s k).card := by
    apply card_image_of_injOn
    intro ζ hζ ζ' hζ' h
    exact (addElem_inj (mem_setPartitions.1 hζ).1 (mem_setPartitions.1 hζ').1 ha
      (by simp) (by simp) h).1
  have hB : (Bs.image F).card = (k + 1) * (setPartitions s (k + 1)).card := by
    rw [card_image_of_injOn]
    · rw [card_sigma]
      rw [sum_congr rfl (fun ζ hζ => by rw [(mem_setPartitions.1 hζ).2])]
      simp [mul_comm]
    · rintro ⟨ζ, B⟩ hp ⟨ζ', B'⟩ hp' h
      simp only [Bs, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_setPartitions] at hp hp'
      have := addElem_inj hp.1.1 hp'.1.1 ha (by simpa using hp.2) (by simpa using hp'.2) h
      obtain ⟨rfl, h2⟩ := this
      simp only [Option.some.injEq] at h2
      subst h2
      rfl
  rw [hsplit, card_union_of_disjoint hdisj, hA, hB]
  ring

theorem card_setPartitions (s : Finset α) (k : ℕ) :
    (setPartitions s k).card = Nat.stirlingSecond s.card k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [setPartitions_empty_zero]
    | succ k => simp [setPartitions_empty_succ]
  | insert a s ha ih =>
    rw [card_insert_of_notMem ha]
    cases k with
    | zero => simp [setPartitions_insert_zero]
    | succ k =>
      rw [card_setPartitions_insert_succ ha, ih, ih, Nat.stirlingSecond_succ_succ]

theorem isSetPartition_parts {s : Finset α} (P : Finpartition s) : IsSetPartition s P.parts := by
  refine ⟨fun h => P.bot_notMem (by simp at h), fun B hB => P.le hB, ?_, ?_⟩
  · intro B hB C hC hne
    exact P.disjoint hB hC hne
  · intro x hx
    rw [← P.sup_parts, mem_sup] at hx
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨B, hB, hxB⟩

def finpartitionOfSetPartition {s : Finset α} {ζ : Finset (Finset α)} (h : IsSetPartition s ζ) :
    Finpartition s where
  parts := ζ
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro B hB C hC hne
    exact h.2.2.1 B hB C hC hne
  sup_parts := by
    apply le_antisymm
    · exact Finset.sup_le (fun B hB => h.2.1 B hB)
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := h.2.2.2 x hx
      exact mem_sup.2 ⟨B, hB, hxB⟩
  bot_notMem := by simpa using h.1

theorem card_finpartition_eq_stirlingSecond (n k : ℕ) :
    Fintype.card {P : Finpartition (Finset.univ : Finset (Fin n)) // P.parts.card = k} =
      Nat.stirlingSecond n k := by
  have hn : Nat.stirlingSecond n k = Nat.stirlingSecond (Finset.univ : Finset (Fin n)).card k := by
    simp
  rw [Fintype.card_subtype, hn, ← card_setPartitions]
  refine card_bij (fun P _ => P.parts) ?_ ?_ ?_
  · intro P hP
    exact mem_setPartitions.2 ⟨isSetPartition_parts P, (mem_filter.1 hP).2⟩
  · intro P _ Q _ h
    exact Finpartition.ext h
  · intro ζ hζ
    obtain ⟨hs, hc⟩ := mem_setPartitions.1 hζ
    exact ⟨finpartitionOfSetPartition hs, mem_filter.2 ⟨mem_univ _, hc⟩, rfl⟩

end Rhone.Combinatorics
