/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Final

/-! # Refinement of set partitions and the block count -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset EsfPair

variable {n : ℕ} {ζ η : Blocks n} {γ : Finset (Fin n)}

theorem sum_card_of_isPartOf (h : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    ∑ β ∈ ζ, β.card = n := by
  have hcard := Finset.card_biUnion (s := ζ) (t := (id : Finset (Fin n) → Finset (Fin n)))
    fun β hβ β' hβ' hne => h.pd β hβ β' hβ' hne
  rw [h.cover, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

theorem card_le_of_isPartOf (h : IsPartOf (Finset.univ : Finset (Fin n)) ζ) : ζ.card ≤ n :=
  calc ζ.card = ∑ _β ∈ ζ, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ β ∈ ζ, β.card :=
        Finset.sum_le_sum fun β hβ => Finset.card_pos.2 (h.ne β hβ)
    _ = n := sum_card_of_isPartOf h

def fiber (η : Blocks n) (γ : Finset (Fin n)) : Blocks n := η.filter fun β => β ⊆ γ

theorem mem_fiber {β : Finset (Fin n)} : β ∈ fiber η γ ↔ β ∈ η ∧ β ⊆ γ := by
  simp [fiber]

theorem biUnion_fiber (h : Refines η ζ) : ζ.biUnion (fiber η) = η := by
  ext β
  simp only [Finset.mem_biUnion, mem_fiber]
  constructor
  · rintro ⟨_, _, hβ, _⟩
    exact hβ
  · intro hβ
    obtain ⟨γ', hγ', hsub⟩ := h β hβ
    exact ⟨γ', hγ', hβ, hsub⟩

theorem fiber_disjoint (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    ∀ γ ∈ ζ, ∀ γ' ∈ ζ, γ ≠ γ' → Disjoint (fiber η γ) (fiber η γ') := by
  intro γ hγ γ' hγ' hne
  refine Finset.disjoint_left.2 fun β hβ hβ' => ?_
  obtain ⟨hβη, hsub⟩ := mem_fiber.1 hβ
  obtain ⟨-, hsub'⟩ := mem_fiber.1 hβ'
  obtain ⟨k, hk⟩ := hη.ne β hβη
  exact hne (hζ.unique_block hγ hγ' (hsub hk) (hsub' hk))

theorem fiber_nonempty (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (h : Refines η ζ) (hγ : γ ∈ ζ) :
    (fiber η γ).Nonempty := by
  obtain ⟨k, hk⟩ := hζ.ne γ hγ
  have hβη : blockOf η k ∈ η := blockOf_mem hη (Finset.mem_univ k)
  have hkβ : k ∈ blockOf η k := mem_blockOf hη (Finset.mem_univ k)
  obtain ⟨γ', hγ', hsub⟩ := h _ hβη
  have : γ' = γ := hζ.unique_block hγ' hγ (hsub hkβ) hk
  exact ⟨blockOf η k, mem_fiber.2 ⟨hβη, this ▸ hsub⟩⟩

theorem card_eq_sum_fiber (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (h : Refines η ζ) :
    η.card = ∑ γ ∈ ζ, (fiber η γ).card := by
  rw [← biUnion_fiber h, Finset.card_biUnion (fiber_disjoint hη hζ)]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [biUnion_fiber h]

theorem card_le_card_of_refines (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (h : Refines η ζ) : ζ.card ≤ η.card := by
  rw [card_eq_sum_fiber hη hζ h]
  calc ζ.card = ∑ _γ ∈ ζ, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ γ ∈ ζ, (fiber η γ).card :=
        Finset.sum_le_sum fun γ hγ =>
          Finset.card_pos.2 (fiber_nonempty hη hζ h hγ)

theorem eq_of_refines_of_card_eq (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (h : Refines η ζ)
    (hc : η.card = ζ.card) : η = ζ := by
  have hsum : ∑ γ ∈ ζ, (fiber η γ).card = ∑ _γ ∈ ζ, 1 := by
    rw [← card_eq_sum_fiber hη hζ h, hc, Finset.sum_const, smul_eq_mul, mul_one]
  have hone : ∀ γ ∈ ζ, (fiber η γ).card = 1 := by
    have hle : ∀ γ ∈ ζ, 1 ≤ (fiber η γ).card :=
      fun γ hγ => Finset.card_pos.2 (fiber_nonempty hη hζ h hγ)
    exact fun γ hγ =>
      ((Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm γ hγ).symm
  have hsub : ζ ⊆ η := by
    intro γ hγ
    obtain ⟨β, hβ⟩ := Finset.card_eq_one.1 (hone γ hγ)
    have hβmem : β ∈ fiber η γ := by rw [hβ]; exact Finset.mem_singleton_self β
    obtain ⟨hβη, hβγ⟩ := mem_fiber.1 hβmem
    have hγβ : γ ⊆ β := by
      intro k hk
      have hbη : blockOf η k ∈ η := blockOf_mem hη (Finset.mem_univ k)
      have hkb : k ∈ blockOf η k := mem_blockOf hη (Finset.mem_univ k)
      obtain ⟨γ', hγ', hsub'⟩ := h _ hbη
      have hγ'γ : γ' = γ := hζ.unique_block hγ' hγ (hsub' hkb) hk
      have : blockOf η k ∈ fiber η γ := mem_fiber.2 ⟨hbη, hγ'γ ▸ hsub'⟩
      rw [hβ, Finset.mem_singleton] at this
      exact this ▸ hkb
    have : γ = β := Finset.Subset.antisymm hγβ hβγ
    exact this ▸ hβη
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq hc)).symm

end Rhone.Coalescent.InfiniteAllelesLimit
