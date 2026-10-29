/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Swap

/-! # The painting transform is injective -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ}

def blockOf (η : Blocks n) (k : Fin n) : Finset (Fin n) := (η.filter fun β => k ∈ β).biUnion id

theorem IsPartOf.unique_block {S : Finset (Fin n)} {η : Blocks n} (h : IsPartOf S η)
    {β β' : Finset (Fin n)} (hβ : β ∈ η) (hβ' : β' ∈ η) {k : Fin n} (hk : k ∈ β)
    (hk' : k ∈ β') : β = β' := by
  by_contra hc
  exact (Finset.disjoint_left.1 (h.pd β hβ β' hβ' hc)) hk hk'

theorem IsPartOf.exists_block {S : Finset (Fin n)} {η : Blocks n} (h : IsPartOf S η) {k : Fin n}
    (hk : k ∈ S) : ∃ β ∈ η, k ∈ β := by
  rw [← h.cover] at hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.1 hk
  exact ⟨β, hβ, hkβ⟩

theorem blockOf_eq {S : Finset (Fin n)} {η : Blocks n} (h : IsPartOf S η) {β : Finset (Fin n)}
    (hβ : β ∈ η) {k : Fin n} (hk : k ∈ β) : blockOf η k = β := by
  have hfil : (η.filter fun γ => k ∈ γ) = {β} := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hg => h.unique_block hg.1 hβ hg.2 hk, fun hg => ⟨hg ▸ hβ, hg ▸ hk⟩⟩
  rw [blockOf, hfil, Finset.singleton_biUnion, id]

theorem blockOf_mem {S : Finset (Fin n)} {η : Blocks n} (h : IsPartOf S η) {k : Fin n}
    (hk : k ∈ S) : blockOf η k ∈ η := by
  obtain ⟨β, hβ, hkβ⟩ := h.exists_block hk
  rw [blockOf_eq h hβ hkβ]
  exact hβ

theorem mem_blockOf {S : Finset (Fin n)} {η : Blocks n} (h : IsPartOf S η) {k : Fin n}
    (hk : k ∈ S) : k ∈ blockOf η k := by
  obtain ⟨β, hβ, hkβ⟩ := h.exists_block hk
  rw [blockOf_eq h hβ hkβ]
  exact hkβ

def Refines (ζ η : Blocks n) : Prop := ∀ β ∈ ζ, ∃ H ∈ η, β ⊆ H

instance (ζ η : Blocks n) : Decidable (Refines ζ η) := by
  unfold Refines
  infer_instance

def relOf (ζ : Blocks n) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun kl => ∃ β ∈ ζ, kl.1 ∈ β ∧ kl.2 ∈ β

theorem mem_relOf {ζ : Blocks n} {k l : Fin n} :
    (k, l) ∈ relOf ζ ↔ ∃ β ∈ ζ, k ∈ β ∧ l ∈ β := by
  simp [relOf]

theorem relOf_subset_of_refines {ζ η : Blocks n} (h : Refines ζ η) : relOf ζ ⊆ relOf η := by
  intro kl hkl
  obtain ⟨k, l⟩ := kl
  obtain ⟨β, hβ, hk, hl⟩ := mem_relOf.1 hkl
  obtain ⟨H, hH, hsub⟩ := h β hβ
  exact mem_relOf.2 ⟨H, hH, hsub hk, hsub hl⟩

theorem eq_of_relOf_eq {S : Finset (Fin n)} {ζ η : Blocks n} (hζ : IsPartOf S ζ)
    (hη : IsPartOf S η) (h : relOf ζ = relOf η) : ζ = η := by
  have key : ∀ {ζ' η' : Blocks n}, IsPartOf S ζ' → IsPartOf S η' →
      relOf ζ' = relOf η' → ζ' ⊆ η' := by
    intro ζ' η' hζ' hη' heq β hβ
    obtain ⟨k, hk⟩ := hζ'.ne β hβ
    have hkS : k ∈ S := by
      rw [← hζ'.cover]
      exact Finset.mem_biUnion.2 ⟨β, hβ, hk⟩
    have hH : blockOf η' k ∈ η' := blockOf_mem hη' hkS
    have hkH : k ∈ blockOf η' k := mem_blockOf hη' hkS
    have hβH : β = blockOf η' k := by
      ext l
      constructor
      · intro hl
        have hmem : (k, l) ∈ relOf η' := by
          rw [← heq]
          exact mem_relOf.2 ⟨β, hβ, hk, hl⟩
        obtain ⟨γ, hγ, hkγ, hlγ⟩ := mem_relOf.1 hmem
        rw [← blockOf_eq hη' hγ hkγ] at hlγ
        exact hlγ
      · intro hl
        have hmem : (k, l) ∈ relOf ζ' := by
          rw [heq]
          exact mem_relOf.2 ⟨blockOf η' k, hH, hkH, hl⟩
        obtain ⟨γ, hγ, hkγ, hlγ⟩ := mem_relOf.1 hmem
        rw [← blockOf_eq hζ' hγ hkγ, blockOf_eq hζ' hβ hk] at hlγ
        exact hlγ
    rw [hβH]
    exact hH
  exact Finset.Subset.antisymm (key hζ hη h) (key hη hζ h.symm)

abbrev numCols (n : ℕ) : ℕ := Fintype.card (Finset (Fin n))

theorem numCols_pos : 0 < numCols n := Fintype.card_pos

noncomputable def colourOf (η : Blocks n) (k : Fin n) : Fin (numCols n) :=
  Fintype.equivFin (Finset (Fin n)) (blockOf η k)

noncomputable def unifPi (n : ℕ) : Fin (numCols n) → ℝ := fun _ => 1 / (numCols n : ℝ)

theorem unifPi_nonneg (i : Fin (numCols n)) : 0 ≤ unifPi n i := by
  simp only [unifPi]
  positivity

theorem unifPi_sum : (∑ i, unifPi n i) = 1 := by
  have h : (0 : ℝ) < (numCols n : ℝ) := by exact_mod_cast numCols_pos
  simp only [unifPi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem unifPi_ne_zero (i : Fin (numCols n)) : unifPi n i ≠ 0 := by
  have h : (0 : ℝ) < (numCols n : ℝ) := by exact_mod_cast numCols_pos
  simp only [unifPi]
  positivity

theorem matchA_colourOf_of_subset {η : Blocks n} {β H : Finset (Fin n)} (hne : β.Nonempty)
    (hsub : β ⊆ H) (hH : H ∈ η) (hpart : IsPartOf (Finset.univ : Finset (Fin n)) η) :
    matchA (colourOf η) (unifPi n) β = unifPi n (Fintype.equivFin (Finset (Fin n)) H) := by
  refine matchA_eq hne fun k hk => ?_
  rw [colourOf, blockOf_eq hpart hH (hsub hk)]

theorem matchA_colourOf_of_not_subset {η : Blocks n} {β : Finset (Fin n)}
    (hpart : IsPartOf (Finset.univ : Finset (Fin n)) η) (hne : β.Nonempty)
    (h : ¬ ∃ H ∈ η, β ⊆ H) : matchA (colourOf η) (unifPi n) β = 0 := by
  obtain ⟨k, hk⟩ := hne
  have hH : blockOf η k ∈ η := blockOf_mem hpart (Finset.mem_univ k)
  have hnsub : ¬ β ⊆ blockOf η k := fun hc => h ⟨blockOf η k, hH, hc⟩
  obtain ⟨l, hl, hlnot⟩ := Finset.not_subset.1 hnsub
  refine matchA_eq_zero fun hmono => ?_
  have hkl : colourOf η k = colourOf η l := hmono k hk l hl
  have : blockOf η k = blockOf η l := (Fintype.equivFin (Finset (Fin n))).injective hkl
  exact hlnot (this ▸ mem_blockOf hpart (Finset.mem_univ l))

theorem wA_colourOf {η ζ : Blocks n} (hη : IsPartOf (Finset.univ : Finset (Fin n)) η)
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    wA (colourOf η) (unifPi n) ζ
      = if Refines ζ η then (1 / (numCols n : ℝ)) ^ ζ.card else 0 := by
  by_cases h : Refines ζ η
  · have hval : ∀ β ∈ ζ, matchA (colourOf η) (unifPi n) β = 1 / (numCols n : ℝ) := by
      intro β hβ
      obtain ⟨H, hH, hsub⟩ := h β hβ
      rw [matchA_colourOf_of_subset (hζ.ne β hβ) hsub hH hη]
      rfl
    rw [ite_eq_left h, wA, Finset.prod_congr rfl hval, Finset.prod_const]
  · rw [ite_eq_right h, wA]
    have h' : ∃ β ∈ ζ, ¬ ∃ H ∈ η, β ⊆ H := by
      by_contra hc
      refine h fun β hβ => ?_
      by_contra hd
      exact hc ⟨β, hβ, hd⟩
    obtain ⟨β, hβ, hnot⟩ := h'
    exact Finset.prod_eq_zero hβ (matchA_colourOf_of_not_subset hη (hζ.ne β hβ) hnot)

theorem eq_of_transform_eq {f g : Blocks n → ℝ}
    (hf : ∀ ζ, ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζ → f ζ = 0)
    (hg : ∀ ζ, ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζ → g ζ = 0)
    (h : ∀ (K : ℕ) (π : Fin K → ℝ), (∀ i, 0 ≤ π i) → (∑ i, π i = 1) →
      ∀ σ : Fin n → Fin K, (∑ ζ : Blocks n, f ζ * wA σ π ζ)
        = ∑ ζ : Blocks n, g ζ * wA σ π ζ) :
    ∀ ζ, f ζ = g ζ := by
  set d : Blocks n → ℝ := fun ζ => f ζ - g ζ with hd
  have hdz : ∀ ζ, ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζ → d ζ = 0 := by
    intro ζ hζ
    rw [hd]
    simp only [hf ζ hζ, hg ζ hζ, sub_zero]
  have hsum : ∀ (K : ℕ) (π : Fin K → ℝ), (∀ i, 0 ≤ π i) → (∑ i, π i = 1) →
      ∀ σ : Fin n → Fin K, (∑ ζ : Blocks n, d ζ * wA σ π ζ) = 0 := by
    intro K π hπ hsπ σ
    have := h K π hπ hsπ σ
    rw [hd]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, this, sub_self]
  have key : ∀ m : ℕ, ∀ η : Blocks n, IsPartOf (Finset.univ : Finset (Fin n)) η →
      (relOf η).card ≤ m → d η = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro η hη hcard
      have hz := hsum (numCols n) (unifPi n) unifPi_nonneg unifPi_sum (colourOf η)
      have hterm : ∀ ζ ∈ (Finset.univ : Finset (Blocks n)),
          d ζ * wA (colourOf η) (unifPi n) ζ
            = if ζ = η then d η * (1 / (numCols n : ℝ)) ^ η.card else 0 := by
        intro ζ _
        by_cases hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ
        · rw [wA_colourOf hη hζ]
          by_cases hr : Refines ζ η
          · rw [ite_eq_left hr]
            by_cases he : ζ = η
            · rw [ite_eq_left he, he]
            · rw [ite_eq_right he]
              have hss : relOf ζ ⊂ relOf η := by
                refine ⟨relOf_subset_of_refines hr, fun hc => he ?_⟩
                exact eq_of_relOf_eq hζ hη
                  (Finset.Subset.antisymm (relOf_subset_of_refines hr) hc)
              have hlt : (relOf ζ).card < (relOf η).card := Finset.card_lt_card hss
              rw [ih ((relOf η).card - 1) (by omega) ζ hζ (by omega), zero_mul]
          · have hne2 : ζ ≠ η := by
              intro hc
              refine hr ?_
              rw [← hc]
              exact fun β hβ => ⟨β, hβ, le_refl β⟩
            rw [ite_eq_right hr, mul_zero, ite_eq_right hne2]
        · rw [hdz ζ hζ, zero_mul, ite_eq_right]
          intro hc
          exact hζ (hc ▸ hη)
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ η
        (fun _ => d η * (1 / (numCols n : ℝ)) ^ η.card), ite_eq_left (Finset.mem_univ η)] at hz
      have hne : ((1 : ℝ) / (numCols n : ℝ)) ^ η.card ≠ 0 := by
        have h0 : (0 : ℝ) < (numCols n : ℝ) := by exact_mod_cast numCols_pos
        positivity
      exact (mul_eq_zero.1 hz).resolve_right hne
  intro ζ
  by_cases hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ
  · have := key (relOf ζ).card ζ hζ (le_refl _)
    rw [hd] at this
    linarith [this]
  · rw [hf ζ hζ, hg ζ hζ]

end Rhone.Coalescent.EsfPair
