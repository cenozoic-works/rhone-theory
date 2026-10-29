/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Kernel
public import Rhone.Coalescent.TwoLocusGenealogy.Total

/-! # The type-carrying ancestral chain: states and their invariant -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n KA KB : ℕ}

abbrev TSt (n KA KB : ℕ) : Type :=
  Finset (Lin n) × (Fin n → Option (Fin KA)) × (Fin n → Option (Fin KB))

def setT {K : ℕ} (τ : Fin n → Option (Fin K)) (S : Finset (Fin n)) (i : Fin K) :
    Fin n → Option (Fin K) := fun k => if k ∈ S then some i else τ k

@[simp] theorem setT_of_mem {K : ℕ} {τ : Fin n → Option (Fin K)} {S : Finset (Fin n)} {i : Fin K}
    {k : Fin n} (h : k ∈ S) : setT τ S i k = some i := by simp [setT, h]

@[simp] theorem setT_of_not_mem {K : ℕ} {τ : Fin n → Option (Fin K)} {S : Finset (Fin n)}
    {i : Fin K} {k : Fin n} (h : k ∉ S) : setT τ S i k = τ k := by simp [setT, h]

def coverA (L : Finset (Lin n)) : Finset (Fin n) := L.biUnion Prod.fst

def coverB (L : Finset (Lin n)) : Finset (Fin n) := L.biUnion Prod.snd

theorem mem_coverA {L : Finset (Lin n)} {k : Fin n} : k ∈ coverA L ↔ ∃ p ∈ L, k ∈ p.1 := by
  simp [coverA]

theorem mem_coverB {L : Finset (Lin n)} {k : Fin n} : k ∈ coverB L ↔ ∃ p ∈ L, k ∈ p.2 := by
  simp [coverB]

@[simp] theorem coverA_empty : coverA (∅ : Finset (Lin n)) = ∅ := rfl

@[simp] theorem coverB_empty : coverB (∅ : Finset (Lin n)) = ∅ := rfl

theorem coverA_coal {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    coverA (coalL L p q) = coverA L := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  ext k
  simp only [mem_coverA, coalL, Finset.mem_insert]
  constructor
  · rintro ⟨r, hr | hr, hk⟩
    · subst hr
      rcases Finset.mem_union.1 hk with h | h
      · exact ⟨p, hp, h⟩
      · exact ⟨q, hqL, h⟩
    · exact ⟨r, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr), hk⟩
  · rintro ⟨r, hrL, hk⟩
    by_cases hrp : r = p
    · exact ⟨_, Or.inl rfl, by subst hrp; exact Finset.mem_union_left _ hk⟩
    · by_cases hrq : r = q
      · exact ⟨_, Or.inl rfl, by subst hrq; exact Finset.mem_union_right _ hk⟩
      · exact ⟨r, Or.inr (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hrL⟩⟩), hk⟩

theorem coverB_coal {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    coverB (coalL L p q) = coverB L := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  ext k
  simp only [mem_coverB, coalL, Finset.mem_insert]
  constructor
  · rintro ⟨r, hr | hr, hk⟩
    · subst hr
      rcases Finset.mem_union.1 hk with h | h
      · exact ⟨p, hp, h⟩
      · exact ⟨q, hqL, h⟩
    · exact ⟨r, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr), hk⟩
  · rintro ⟨r, hrL, hk⟩
    by_cases hrp : r = p
    · exact ⟨_, Or.inl rfl, by subst hrp; exact Finset.mem_union_left _ hk⟩
    · by_cases hrq : r = q
      · exact ⟨_, Or.inl rfl, by subst hrq; exact Finset.mem_union_right _ hk⟩
      · exact ⟨r, Or.inr (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hrL⟩⟩), hk⟩

theorem coverA_erase_of_mem {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverA (L.erase p) = coverA L \ p.1 := by
  ext k
  simp only [mem_coverA, Finset.mem_sdiff]
  constructor
  · rintro ⟨r, hr, hk⟩
    have hrL : r ∈ L := Finset.mem_of_mem_erase hr
    have hrp : r ≠ p := Finset.ne_of_mem_erase hr
    exact ⟨⟨r, hrL, hk⟩, fun hc => (Finset.disjoint_left.1 (hw.disjA r hrL p hp hrp)) hk hc⟩
  · rintro ⟨⟨r, hrL, hk⟩, hkp⟩
    exact ⟨r, Finset.mem_erase.2 ⟨fun hc => hkp (hc ▸ hk), hrL⟩, hk⟩

theorem coverB_erase_of_mem {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverB (L.erase p) = coverB L \ p.2 := by
  ext k
  simp only [mem_coverB, Finset.mem_sdiff]
  constructor
  · rintro ⟨r, hr, hk⟩
    have hrL : r ∈ L := Finset.mem_of_mem_erase hr
    have hrp : r ≠ p := Finset.ne_of_mem_erase hr
    exact ⟨⟨r, hrL, hk⟩, fun hc => (Finset.disjoint_left.1 (hw.disjB r hrL p hp hrp)) hk hc⟩
  · rintro ⟨⟨r, hrL, hk⟩, hkp⟩
    exact ⟨r, Finset.mem_erase.2 ⟨fun hc => hkp (hc ▸ hk), hrL⟩, hk⟩

theorem coverA_insert (L : Finset (Lin n)) (p : Lin n) :
    coverA (insert p L) = p.1 ∪ coverA L := by
  ext k
  simp only [mem_coverA, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨r, hr | hr, hk⟩
    · exact Or.inl (hr ▸ hk)
    · exact Or.inr ⟨r, hr, hk⟩
  · rintro (hk | ⟨r, hr, hk⟩)
    · exact ⟨p, Or.inl rfl, hk⟩
    · exact ⟨r, Or.inr hr, hk⟩

theorem coverB_insert (L : Finset (Lin n)) (p : Lin n) :
    coverB (insert p L) = p.2 ∪ coverB L := by
  ext k
  simp only [mem_coverB, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨r, hr | hr, hk⟩
    · exact Or.inl (hr ▸ hk)
    · exact Or.inr ⟨r, hr, hk⟩
  · rintro (hk | ⟨r, hr, hk⟩)
    · exact ⟨p, Or.inl rfl, hk⟩
    · exact ⟨r, Or.inr hr, hk⟩

theorem coverA_mutA {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverA (mutAL L p) = coverA L \ p.1 := by
  unfold mutAL
  split_ifs with h
  · exact coverA_erase_of_mem hw hp
  · rw [coverA_insert, coverA_erase_of_mem hw hp]
    simp

theorem coverB_mutA {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverB (mutAL L p) = coverB L := by
  unfold mutAL
  split_ifs with h
  · rw [coverB_erase_of_mem hw hp, h]
    simp
  · rw [coverB_insert, coverB_erase_of_mem hw hp]
    exact Finset.union_sdiff_of_subset (fun k hk => mem_coverB.2 ⟨p, hp, hk⟩)

theorem coverB_mutB {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverB (mutBL L p) = coverB L \ p.2 := by
  unfold mutBL
  split_ifs with h
  · exact coverB_erase_of_mem hw hp
  · rw [coverB_insert, coverB_erase_of_mem hw hp]
    simp

theorem coverA_mutB {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverA (mutBL L p) = coverA L := by
  unfold mutBL
  split_ifs with h
  · rw [coverA_erase_of_mem hw hp, h]
    simp
  · rw [coverA_insert, coverA_erase_of_mem hw hp]
    exact Finset.union_sdiff_of_subset (fun k hk => mem_coverA.2 ⟨p, hp, hk⟩)

theorem coverA_rec {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverA (recL L p) = coverA L := by
  rw [recL, coverA_insert, coverA_insert, coverA_erase_of_mem hw hp]
  simp only [Finset.empty_union]
  exact Finset.union_sdiff_of_subset (fun k hk => mem_coverA.2 ⟨p, hp, hk⟩)

theorem coverB_rec {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ L) :
    coverB (recL L p) = coverB L := by
  rw [recL, coverB_insert, coverB_insert, coverB_erase_of_mem hw hp]
  simp only [Finset.empty_union]
  exact Finset.union_sdiff_of_subset (fun k hk => mem_coverB.2 ⟨p, hp, hk⟩)

structure WFT (s : TSt n KA KB) : Prop where
  wf : WF s.1
  resA : ∀ k, s.2.1 k = none ↔ k ∈ coverA s.1
  resB : ∀ k, s.2.2 k = none ↔ k ∈ coverB s.1

theorem WFT.coal {s : TSt n KA KB} (hs : WFT s) {p q : Lin n} (hp : p ∈ s.1)
    (hq : q ∈ s.1.erase p) : WFT (coalL s.1 p q, s.2.1, s.2.2) := by
  refine ⟨hs.wf.coal hp (Finset.mem_of_mem_erase hq), fun k => ?_, fun k => ?_⟩
  · rw [show coverA (coalL s.1 p q) = coverA s.1 from coverA_coal hp hq]
    exact hs.resA k
  · rw [show coverB (coalL s.1 p q) = coverB s.1 from coverB_coal hp hq]
    exact hs.resB k

theorem WFT.mutA {s : TSt n KA KB} (hs : WFT s) {p : Lin n} (hp : p ∈ s.1) (i : Fin KA) :
    WFT (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2) := by
  refine ⟨hs.wf.mutA hp, fun k => ?_, fun k => ?_⟩
  · rw [show coverA (mutAL s.1 p) = coverA s.1 \ p.1 from coverA_mutA hs.wf hp,
      Finset.mem_sdiff]
    by_cases hk : k ∈ p.1
    · simp [hk, mem_coverA.2 ⟨p, hp, hk⟩]
    · have h1 : (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2).2.1 k = s.2.1 k := setT_of_not_mem hk
      rw [h1, hs.resA k]
      simp [hk]
  · rw [show coverB (mutAL s.1 p) = coverB s.1 from coverB_mutA hs.wf hp]
    exact hs.resB k

theorem WFT.mutB {s : TSt n KA KB} (hs : WFT s) {p : Lin n} (hp : p ∈ s.1) (j : Fin KB) :
    WFT (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j) := by
  refine ⟨hs.wf.mutB hp, fun k => ?_, fun k => ?_⟩
  · rw [show coverA (mutBL s.1 p) = coverA s.1 from coverA_mutB hs.wf hp]
    exact hs.resA k
  · rw [show coverB (mutBL s.1 p) = coverB s.1 \ p.2 from coverB_mutB hs.wf hp,
      Finset.mem_sdiff]
    by_cases hk : k ∈ p.2
    · simp [hk, mem_coverB.2 ⟨p, hp, hk⟩]
    · have h1 : (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j).2.2 k = s.2.2 k := setT_of_not_mem hk
      rw [h1, hs.resB k]
      simp [hk]

theorem WFT.recomb {s : TSt n KA KB} (hs : WFT s) {p : Lin n} (hp : p ∈ s.1)
    (h1 : p.1.Nonempty) (h2 : p.2.Nonempty) : WFT (recL s.1 p, s.2.1, s.2.2) := by
  refine ⟨hs.wf.recomb hp h1 h2, fun k => ?_, fun k => ?_⟩
  · rw [show coverA (recL s.1 p) = coverA s.1 from coverA_rec hs.wf hp]
    exact hs.resA k
  · rw [show coverB (recL s.1 p) = coverB s.1 from coverB_rec hs.wf hp]
    exact hs.resB k

def FitsT {K : ℕ} (σ : Fin n → Fin K) (τ : Fin n → Option (Fin K)) : Prop :=
  ∀ k i, τ k = some i → σ k = i

def Fits (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (s : TSt n KA KB) : Prop :=
  FitsT σA s.2.1 ∧ FitsT σB s.2.2

instance {K : ℕ} (σ : Fin n → Fin K) (τ : Fin n → Option (Fin K)) : Decidable (FitsT σ τ) := by
  unfold FitsT; infer_instance

instance (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (s : TSt n KA KB) :
    Decidable (Fits σA σB s) := by unfold Fits; infer_instance

theorem fitsT_none {K : ℕ} (σ : Fin n → Fin K) : FitsT σ (fun _ => none) := by
  intro k i h
  exact absurd h (by simp)

theorem fitsT_setT {K : ℕ} {σ : Fin n → Fin K} {τ : Fin n → Option (Fin K)}
    {S : Finset (Fin n)} {i : Fin K} (h : FitsT σ τ) :
    FitsT σ (setT τ S i) ↔ ∀ k ∈ S, σ k = i := by
  constructor
  · intro hf k hk
    exact hf k i (setT_of_mem hk)
  · intro hc k i' hki
    by_cases hk : k ∈ S
    · rw [setT_of_mem hk] at hki
      rw [hc k hk]
      exact Option.some.inj hki
    · rw [setT_of_not_mem hk] at hki
      exact h k i' hki

theorem not_fitsT_setT {K : ℕ} {σ : Fin n → Fin K} {τ : Fin n → Option (Fin K)}
    {S : Finset (Fin n)} {i : Fin K} (hres : ∀ k ∈ S, τ k = none) (h : ¬ FitsT σ τ) :
    ¬ FitsT σ (setT τ S i) := by
  intro hf
  refine h fun k i' hki => ?_
  have hk : k ∉ S := by
    intro hc
    rw [hres k hc] at hki
    exact absurd hki (by simp)
  exact hf k i' (by rw [setT_of_not_mem hk]; exact hki)

end Rhone.Coalescent.TypedAncestralChain
