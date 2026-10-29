/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Sampling

/-! # The partition-carrying ancestral chain: states and their invariant -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ}

abbrev Blocks (n : ℕ) : Type := Finset (Finset (Fin n))

abbrev PSt (n : ℕ) : Type := Finset (Lin n) × Blocks n × Blocks n

def coalP (s : PSt n) (p q : Lin n) : PSt n := (coalL s.1 p q, s.2.1, s.2.2)

def mutAP (s : PSt n) (p : Lin n) : PSt n := (mutAL s.1 p, insert p.1 s.2.1, s.2.2)

def mutBP (s : PSt n) (p : Lin n) : PSt n := (mutBL s.1 p, s.2.1, insert p.2 s.2.2)

def recP (s : PSt n) (p : Lin n) : PSt n := (recL s.1 p, s.2.1, s.2.2)

structure WFP (s : PSt n) : Prop where
  wf : WF s.1
  neA : ∀ β ∈ s.2.1, β.Nonempty
  neB : ∀ γ ∈ s.2.2, γ.Nonempty
  pdA : ∀ β ∈ s.2.1, ∀ β' ∈ s.2.1, β ≠ β' → Disjoint β β'
  pdB : ∀ γ ∈ s.2.2, ∀ γ' ∈ s.2.2, γ ≠ γ' → Disjoint γ γ'
  freshA : Disjoint (coverA s.1) (s.2.1.biUnion id)
  freshB : Disjoint (coverB s.1) (s.2.2.biUnion id)

def spanA (s : PSt n) : Finset (Fin n) := coverA s.1 ∪ s.2.1.biUnion id

def spanB (s : PSt n) : Finset (Fin n) := coverB s.1 ∪ s.2.2.biUnion id

theorem subset_coverA {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) : p.1 ⊆ coverA L :=
  fun _ hk => mem_coverA.2 ⟨p, hp, hk⟩

theorem subset_coverB {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) : p.2 ⊆ coverB L :=
  fun _ hk => mem_coverB.2 ⟨p, hp, hk⟩

theorem subset_biUnion {ζ : Blocks n} {β : Finset (Fin n)} (h : β ∈ ζ) : β ⊆ ζ.biUnion id :=
  fun _ hk => Finset.mem_biUnion.2 ⟨β, h, hk⟩

theorem disjoint_emittedA {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ s.1)
    {β : Finset (Fin n)} (hβ : β ∈ s.2.1) : Disjoint p.1 β :=
  hs.freshA.mono (subset_coverA hp) (subset_biUnion hβ)

theorem disjoint_emittedB {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ s.1)
    {γ : Finset (Fin n)} (hγ : γ ∈ s.2.2) : Disjoint p.2 γ :=
  hs.freshB.mono (subset_coverB hp) (subset_biUnion hγ)

theorem notMem_emittedA {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ carA s.1) :
    p.1 ∉ s.2.1 := by
  obtain ⟨hpL, hne⟩ := mem_carA.1 hp
  intro hc
  have hd : Disjoint p.1 p.1 := disjoint_emittedA hs hpL hc
  rw [disjoint_self] at hd
  exact absurd hd (Finset.nonempty_iff_ne_empty.1 hne)

theorem notMem_emittedB {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ carB s.1) :
    p.2 ∉ s.2.2 := by
  obtain ⟨hpL, hne⟩ := mem_carB.1 hp
  intro hc
  have hd : Disjoint p.2 p.2 := disjoint_emittedB hs hpL hc
  rw [disjoint_self] at hd
  exact absurd hd (Finset.nonempty_iff_ne_empty.1 hne)

theorem biUnion_insert (ζ : Blocks n) (β : Finset (Fin n)) :
    (insert β ζ).biUnion id = β ∪ ζ.biUnion id := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union, id]
  constructor
  · rintro ⟨γ, hγ | hγ, hk⟩
    · exact Or.inl (hγ ▸ hk)
    · exact Or.inr ⟨γ, hγ, hk⟩
  · rintro (hk | ⟨γ, hγ, hk⟩)
    · exact ⟨β, Or.inl rfl, hk⟩
    · exact ⟨γ, Or.inr hγ, hk⟩

theorem WFP.coal {s : PSt n} (hs : WFP s) {p q : Lin n} (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) :
    WFP (coalP s p q) := by
  refine ⟨hs.wf.coal hp (Finset.mem_of_mem_erase hq), hs.neA, hs.neB, hs.pdA, hs.pdB, ?_, ?_⟩
  · change Disjoint (coverA (coalL s.1 p q)) (s.2.1.biUnion id)
    rw [coverA_coal hp hq]
    exact hs.freshA
  · change Disjoint (coverB (coalL s.1 p q)) (s.2.2.biUnion id)
    rw [coverB_coal hp hq]
    exact hs.freshB

theorem WFP.recomb {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ s.1) (h1 : p.1.Nonempty)
    (h2 : p.2.Nonempty) : WFP (recP s p) := by
  refine ⟨hs.wf.recomb hp h1 h2, hs.neA, hs.neB, hs.pdA, hs.pdB, ?_, ?_⟩
  · change Disjoint (coverA (recL s.1 p)) (s.2.1.biUnion id)
    rw [coverA_rec hs.wf hp]
    exact hs.freshA
  · change Disjoint (coverB (recL s.1 p)) (s.2.2.biUnion id)
    rw [coverB_rec hs.wf hp]
    exact hs.freshB

theorem WFP.mutA {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ carA s.1) :
    WFP (mutAP s p) := by
  obtain ⟨hpL, hne⟩ := mem_carA.1 hp
  have hcovA : coverA (mutAL s.1 p) = coverA s.1 \ p.1 := coverA_mutA hs.wf hpL
  have hdisj : ∀ β ∈ s.2.1, Disjoint p.1 β := fun β hβ => disjoint_emittedA hs hpL hβ
  refine ⟨hs.wf.mutA hpL, ?_, hs.neB, ?_, hs.pdB, ?_, ?_⟩
  · intro β hβ
    rcases Finset.mem_insert.1 hβ with rfl | hβ
    · exact hne
    · exact hs.neA β hβ
  · intro β hβ β' hβ' hne'
    rcases Finset.mem_insert.1 hβ with rfl | hβ <;>
      rcases Finset.mem_insert.1 hβ' with rfl | hβ'
    · exact absurd rfl hne'
    · exact hdisj β' hβ'
    · exact (hdisj β hβ).symm
    · exact hs.pdA β hβ β' hβ' hne'
  · change Disjoint (coverA (mutAL s.1 p)) ((insert p.1 s.2.1).biUnion id)
    rw [hcovA, biUnion_insert]
    exact Finset.disjoint_union_right.2 ⟨Finset.sdiff_disjoint,
      hs.freshA.mono_left Finset.sdiff_subset⟩
  · change Disjoint (coverB (mutAL s.1 p)) (s.2.2.biUnion id)
    rw [coverB_mutA hs.wf hpL]
    exact hs.freshB

theorem WFP.mutB {s : PSt n} (hs : WFP s) {p : Lin n} (hp : p ∈ carB s.1) :
    WFP (mutBP s p) := by
  obtain ⟨hpL, hne⟩ := mem_carB.1 hp
  have hcovB : coverB (mutBL s.1 p) = coverB s.1 \ p.2 := coverB_mutB hs.wf hpL
  have hdisj : ∀ γ ∈ s.2.2, Disjoint p.2 γ := fun γ hγ => disjoint_emittedB hs hpL hγ
  refine ⟨hs.wf.mutB hpL, hs.neA, ?_, hs.pdA, ?_, ?_, ?_⟩
  · intro γ hγ
    rcases Finset.mem_insert.1 hγ with rfl | hγ
    · exact hne
    · exact hs.neB γ hγ
  · intro γ hγ γ' hγ' hne'
    rcases Finset.mem_insert.1 hγ with rfl | hγ <;>
      rcases Finset.mem_insert.1 hγ' with rfl | hγ'
    · exact absurd rfl hne'
    · exact hdisj γ' hγ'
    · exact (hdisj γ hγ).symm
    · exact hs.pdB γ hγ γ' hγ' hne'
  · change Disjoint (coverA (mutBL s.1 p)) (s.2.1.biUnion id)
    rw [coverA_mutB hs.wf hpL]
    exact hs.freshA
  · change Disjoint (coverB (mutBL s.1 p)) ((insert p.2 s.2.2).biUnion id)
    rw [hcovB, biUnion_insert]
    exact Finset.disjoint_union_right.2 ⟨Finset.sdiff_disjoint,
      hs.freshB.mono_left Finset.sdiff_subset⟩

theorem spanA_coal {s : PSt n} {p q : Lin n} (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) :
    spanA (coalP s p q) = spanA s := by
  change coverA (coalL s.1 p q) ∪ s.2.1.biUnion id = spanA s
  rw [coverA_coal hp hq]
  rfl

theorem spanB_coal {s : PSt n} {p q : Lin n} (hp : p ∈ s.1) (hq : q ∈ s.1.erase p) :
    spanB (coalP s p q) = spanB s := by
  change coverB (coalL s.1 p q) ∪ s.2.2.biUnion id = spanB s
  rw [coverB_coal hp hq]
  rfl

theorem spanA_rec {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanA (recP s p) = spanA s := by
  change coverA (recL s.1 p) ∪ s.2.1.biUnion id = spanA s
  rw [coverA_rec hw hp]
  rfl

theorem spanB_rec {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanB (recP s p) = spanB s := by
  change coverB (recL s.1 p) ∪ s.2.2.biUnion id = spanB s
  rw [coverB_rec hw hp]
  rfl

theorem spanA_mutA {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanA (mutAP s p) = spanA s := by
  have hsub : p.1 ⊆ coverA s.1 := subset_coverA hp
  change coverA (mutAL s.1 p) ∪ (insert p.1 s.2.1).biUnion id = spanA s
  rw [coverA_mutA hw hp, biUnion_insert, ← Finset.union_assoc,
    Finset.sdiff_union_of_subset hsub]
  rfl

theorem spanB_mutA {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanB (mutAP s p) = spanB s := by
  change coverB (mutAL s.1 p) ∪ s.2.2.biUnion id = spanB s
  rw [coverB_mutA hw hp]
  rfl

theorem spanB_mutB {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanB (mutBP s p) = spanB s := by
  have hsub : p.2 ⊆ coverB s.1 := subset_coverB hp
  change coverB (mutBL s.1 p) ∪ (insert p.2 s.2.2).biUnion id = spanB s
  rw [coverB_mutB hw hp, biUnion_insert, ← Finset.union_assoc,
    Finset.sdiff_union_of_subset hsub]
  rfl

theorem spanA_mutB {s : PSt n} (hw : WF s.1) {p : Lin n} (hp : p ∈ s.1) :
    spanA (mutBP s p) = spanA s := by
  change coverA (mutBL s.1 p) ∪ s.2.1.biUnion id = spanA s
  rw [coverA_mutB hw hp]
  rfl

structure IsPartOf (S : Finset (Fin n)) (ζ : Blocks n) : Prop where
  ne : ∀ β ∈ ζ, β.Nonempty
  pd : ∀ β ∈ ζ, ∀ β' ∈ ζ, β ≠ β' → Disjoint β β'
  cover : ζ.biUnion id = S

theorem isPartOf_of_absorbed {s : PSt n} (hs : WFP s) (h : s.1 = ∅) :
    IsPartOf (spanA s) s.2.1 ∧ IsPartOf (spanB s) s.2.2 := by
  refine ⟨⟨hs.neA, hs.pdA, ?_⟩, ⟨hs.neB, hs.pdB, ?_⟩⟩
  · simp [spanA, h]
  · simp [spanB, h]

end Rhone.Coalescent.EsfPair
