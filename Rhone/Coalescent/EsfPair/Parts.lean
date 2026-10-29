/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Inject

/-! # Set partitions of a finite set, and the Chinese-restaurant recursion -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy

variable {n : ℕ}

instance (S : Finset (Fin n)) (ζ : Blocks n) : Decidable (IsPartOf S ζ) :=
  decidable_of_iff ((∀ β ∈ ζ, β.Nonempty) ∧ (∀ β ∈ ζ, ∀ β' ∈ ζ, β ≠ β' → Disjoint β β')
      ∧ ζ.biUnion id = S)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.ne, h.pd, h.cover⟩⟩

def partsOf (S : Finset (Fin n)) : Finset (Blocks n) := Finset.univ.filter (IsPartOf S)

@[simp] theorem mem_partsOf {S : Finset (Fin n)} {ζ : Blocks n} :
    ζ ∈ partsOf S ↔ IsPartOf S ζ := by simp [partsOf]

theorem IsPartOf.empty_notMem {S : Finset (Fin n)} {ζ : Blocks n} (h : IsPartOf S ζ) :
    (∅ : Finset (Fin n)) ∉ ζ := fun hc => by simpa using h.ne ∅ hc

theorem IsPartOf.block_subset {S : Finset (Fin n)} {ζ : Blocks n} (h : IsPartOf S ζ)
    {β : Finset (Fin n)} (hβ : β ∈ ζ) : β ⊆ S := by
  rw [← h.cover]
  exact subset_biUnion hβ

theorem biUnion_erase_union {ζ : Blocks n} {β : Finset (Fin n)} (hβ : β ∈ ζ) :
    β ∪ (ζ.erase β).biUnion id = ζ.biUnion id := by
  conv_rhs => rw [← Finset.insert_erase hβ]
  rw [biUnion_insert]

theorem partsOf_empty : partsOf (∅ : Finset (Fin n)) = {∅} := by
  ext ζ
  simp only [mem_partsOf, Finset.mem_singleton]
  exact ⟨eq_empty_of_isPartOf_empty, fun h => by
    subst h
    exact ⟨fun β hβ => absurd hβ (Finset.notMem_empty β), fun β hβ => absurd hβ
      (Finset.notMem_empty β), rfl⟩⟩

def extend (a : Fin n) (ζ : Blocks n) (β : Finset (Fin n)) : Blocks n :=
  insert (insert a β) (ζ.erase β)

section Extend

variable {a : Fin n} {S : Finset (Fin n)} {ζ : Blocks n} {β : Finset (Fin n)}

theorem block_subset_of_mem_insert (hζ : IsPartOf S ζ)
    (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) : β ⊆ S := by
  rcases Finset.mem_insert.1 hβ with rfl | h
  · exact Finset.empty_subset S
  · exact hζ.block_subset h

theorem union_erase_of_mem_insert (hζ : IsPartOf S ζ)
    (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) : β ∪ (ζ.erase β).biUnion id = S := by
  rcases Finset.mem_insert.1 hβ with rfl | h
  · rw [Finset.erase_eq_of_notMem hζ.empty_notMem, Finset.empty_union, hζ.cover]
  · rw [biUnion_erase_union h, hζ.cover]

theorem disjoint_erase_of_mem_insert (hζ : IsPartOf S ζ)
    (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) : ∀ γ ∈ ζ.erase β, Disjoint β γ := by
  rcases Finset.mem_insert.1 hβ with rfl | h
  · exact fun γ _ => Finset.disjoint_empty_left γ
  · exact fun γ hγ => hζ.pd β h γ (Finset.mem_of_mem_erase hγ)
      fun hc => (Finset.ne_of_mem_erase hγ) hc.symm

theorem extend_notMem (ha : a ∉ S) (hζ : IsPartOf S ζ) : insert a β ∉ ζ.erase β := by
  intro hc
  exact ha (hζ.block_subset (Finset.mem_of_mem_erase hc) (Finset.mem_insert_self a β))

theorem extend_isPartOf (ha : a ∉ S) (hζ : IsPartOf S ζ)
    (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) : IsPartOf (insert a S) (extend a ζ β) := by
  have hsub := block_subset_of_mem_insert hζ hβ
  have hcov := union_erase_of_mem_insert hζ hβ
  have hdis := disjoint_erase_of_mem_insert hζ hβ
  have hnew : ∀ γ ∈ ζ.erase β, Disjoint (insert a β) γ := by
    intro γ hγ
    refine Finset.disjoint_insert_left.2 ⟨fun hc => ha ?_, hdis γ hγ⟩
    exact hζ.block_subset (Finset.mem_of_mem_erase hγ) hc
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ
    rcases Finset.mem_insert.1 hγ with rfl | hγ
    · exact ⟨a, Finset.mem_insert_self a β⟩
    · exact hζ.ne γ (Finset.mem_of_mem_erase hγ)
  · intro γ hγ γ' hγ' hne
    rcases Finset.mem_insert.1 hγ with rfl | hγ <;>
      rcases Finset.mem_insert.1 hγ' with rfl | hγ'
    · exact absurd rfl hne
    · exact hnew γ' hγ'
    · exact (hnew γ hγ).symm
    · exact hζ.pd γ (Finset.mem_of_mem_erase hγ) γ' (Finset.mem_of_mem_erase hγ') hne
  · rw [extend, biUnion_insert, Finset.insert_union, hcov]

theorem eq_erase_insert (hζ : IsPartOf S ζ) (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) :
    ζ = (insert β (ζ.erase β)).erase ∅ := by
  rcases Finset.mem_insert.1 hβ with rfl | h
  · rw [Finset.erase_eq_of_notMem hζ.empty_notMem, Finset.erase_insert hζ.empty_notMem]
  · rw [Finset.insert_erase h, Finset.erase_eq_of_notMem hζ.empty_notMem]

end Extend

theorem sum_partsOf_insert {M : Type*} [AddCommMonoid M] (F : Blocks n → M) {a : Fin n}
    {S : Finset (Fin n)} (ha : a ∉ S) :
    (∑ ζ ∈ partsOf (insert a S), F ζ)
      = ∑ ζ' ∈ partsOf S, ∑ β ∈ insert (∅ : Finset (Fin n)) ζ', F (extend a ζ' β) := by
  rw [Finset.sum_sigma' (partsOf S) (fun ζ' => insert (∅ : Finset (Fin n)) ζ')
    (fun ζ' β => F (extend a ζ' β))]
  refine (Finset.sum_bij (fun x _ => extend a x.1 x.2) ?_ ?_ ?_ ?_).symm
  · rintro ⟨ζ', β⟩ hx
    rw [Finset.mem_sigma] at hx
    exact mem_partsOf.2 (extend_isPartOf ha (mem_partsOf.1 hx.1) hx.2)
  · rintro ⟨ζ₁, β₁⟩ hx₁ ⟨ζ₂, β₂⟩ hx₂ heq
    rw [Finset.mem_sigma] at hx₁ hx₂
    have hp₁ : IsPartOf S ζ₁ := mem_partsOf.1 hx₁.1
    have hp₂ : IsPartOf S ζ₂ := mem_partsOf.1 hx₂.1
    have hs₁ : β₁ ⊆ S := block_subset_of_mem_insert hp₁ hx₁.2
    have hs₂ : β₂ ⊆ S := block_subset_of_mem_insert hp₂ hx₂.2
    have hnew₁ : insert a β₁ ∉ ζ₁.erase β₁ := extend_notMem ha hp₁
    have hnew₂ : insert a β₂ ∉ ζ₂.erase β₂ := extend_notMem ha hp₂
    have hmem : insert a β₂ ∈ extend a ζ₁ β₁ := by
      rw [heq, extend]
      exact Finset.mem_insert_self _ _
    have hab : insert a β₁ = insert a β₂ := by
      rcases Finset.mem_insert.1 hmem with h | h
      · exact h.symm
      · exact absurd (ha (hp₁.block_subset (Finset.mem_of_mem_erase h)
          (Finset.mem_insert_self a β₂))) not_false
    have hβ : β₁ = β₂ := by
      have h1 : a ∉ β₁ := fun hc => ha (hs₁ hc)
      have h2 : a ∉ β₂ := fun hc => ha (hs₂ hc)
      rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, hab]
    subst hβ
    have herase : ζ₁.erase β₁ = ζ₂.erase β₁ := by
      have := congrArg (fun X => X.erase (insert a β₁)) heq
      simpa only [extend, Finset.erase_insert hnew₁, Finset.erase_insert hnew₂] using this
    have : ζ₁ = ζ₂ := by
      rw [eq_erase_insert hp₁ hx₁.2, eq_erase_insert hp₂ hx₂.2, herase]
    subst this
    rfl
  · intro ζ hζ
    have hp : IsPartOf (insert a S) ζ := mem_partsOf.1 hζ
    have haS : a ∈ insert a S := Finset.mem_insert_self a S
    have hBmem : blockOf ζ a ∈ ζ := blockOf_mem hp haS
    have haB : a ∈ blockOf ζ a := mem_blockOf hp haS
    have hRne : ∀ γ ∈ ζ.erase (blockOf ζ a), γ.Nonempty :=
      fun γ hγ => hp.ne γ (Finset.mem_of_mem_erase hγ)
    have hRdisjB : ∀ γ ∈ ζ.erase (blockOf ζ a), Disjoint (blockOf ζ a) γ :=
      fun γ hγ => hp.pd _ hBmem γ (Finset.mem_of_mem_erase hγ)
        fun hc => (Finset.ne_of_mem_erase hγ) hc.symm
    have hRpd : ∀ γ ∈ ζ.erase (blockOf ζ a), ∀ γ' ∈ ζ.erase (blockOf ζ a),
        γ ≠ γ' → Disjoint γ γ' :=
      fun γ hγ γ' hγ' hne => hp.pd γ (Finset.mem_of_mem_erase hγ) γ'
        (Finset.mem_of_mem_erase hγ') hne
    have hRcov : (ζ.erase (blockOf ζ a)).biUnion id = S \ (blockOf ζ a).erase a := by
      apply Finset.Subset.antisymm
      · intro k hk
        obtain ⟨γ, hγ, hkγ⟩ := Finset.mem_biUnion.1 hk
        have hkB : k ∉ blockOf ζ a :=
          fun hc => (Finset.disjoint_left.1 (hRdisjB γ hγ)) hc hkγ
        have hkS : k ∈ insert a S := hp.block_subset (Finset.mem_of_mem_erase hγ) hkγ
        refine Finset.mem_sdiff.2 ⟨?_, fun hc => hkB (Finset.mem_of_mem_erase hc)⟩
        rcases Finset.mem_insert.1 hkS with rfl | h
        · exact absurd haB hkB
        · exact h
      · intro k hk
        obtain ⟨hkS, hkβ⟩ := Finset.mem_sdiff.1 hk
        have hka : k ≠ a := fun hc => ha (hc ▸ hkS)
        have hkB : k ∉ blockOf ζ a := fun hc => hkβ (Finset.mem_erase.2 ⟨hka, hc⟩)
        obtain ⟨γ, hγ, hkγ⟩ := hp.exists_block (Finset.mem_insert_of_mem hkS)
        exact Finset.mem_biUnion.2 ⟨γ, Finset.mem_erase.2 ⟨fun hc => hkB (hc ▸ hkγ), hγ⟩, hkγ⟩
    have hβsub : (blockOf ζ a).erase a ⊆ S := by
      intro k hk
      have hkS : k ∈ insert a S := hp.block_subset hBmem (Finset.mem_of_mem_erase hk)
      rcases Finset.mem_insert.1 hkS with rfl | h
      · exact absurd rfl (Finset.ne_of_mem_erase hk)
      · exact h
    by_cases hβe : (blockOf ζ a).erase a = ∅
    · refine ⟨⟨ζ.erase (blockOf ζ a), ∅⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        refine ⟨mem_partsOf.2 ⟨hRne, hRpd, ?_⟩, Finset.mem_insert_self _ _⟩
        rw [hRcov, hβe, Finset.sdiff_empty]
      · have hB : insert a ((blockOf ζ a).erase a) = blockOf ζ a := Finset.insert_erase haB
        have hnotMem : (∅ : Finset (Fin n)) ∉ ζ.erase (blockOf ζ a) :=
          fun hc => by simpa using hRne ∅ hc
        change extend a (ζ.erase (blockOf ζ a)) ∅ = ζ
        rw [extend, Finset.erase_eq_of_notMem hnotMem, ← hβe, hB, Finset.insert_erase hBmem]
    · have hβne : ((blockOf ζ a).erase a).Nonempty := Finset.nonempty_iff_ne_empty.2 hβe
      have hβnotMem : (blockOf ζ a).erase a ∉ ζ.erase (blockOf ζ a) := by
        intro hc
        obtain ⟨k, hk⟩ := hβne
        exact (Finset.disjoint_left.1 (hRdisjB _ hc)) (Finset.mem_of_mem_erase hk) hk
      refine ⟨⟨insert ((blockOf ζ a).erase a) (ζ.erase (blockOf ζ a)),
        (blockOf ζ a).erase a⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        refine ⟨mem_partsOf.2 ⟨?_, ?_, ?_⟩, Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _)⟩
        · intro γ hγ
          rcases Finset.mem_insert.1 hγ with rfl | hγ
          · exact hβne
          · exact hRne γ hγ
        · intro γ hγ γ' hγ' hne
          rcases Finset.mem_insert.1 hγ with rfl | hγ <;>
            rcases Finset.mem_insert.1 hγ' with rfl | hγ'
          · exact absurd rfl hne
          · exact (hRdisjB γ' hγ').mono_left (Finset.erase_subset _ _)
          · exact ((hRdisjB γ hγ).mono_left (Finset.erase_subset _ _)).symm
          · exact hRpd γ hγ γ' hγ' hne
        · rw [biUnion_insert, hRcov, Finset.union_sdiff_of_subset hβsub]
      · change extend a (insert ((blockOf ζ a).erase a) (ζ.erase (blockOf ζ a)))
          ((blockOf ζ a).erase a) = ζ
        rw [extend, Finset.erase_insert hβnotMem, Finset.insert_erase haB,
          Finset.insert_erase hBmem]
  · rintro ⟨ζ', β⟩ _
    rfl

end Rhone.Coalescent.EsfPair
