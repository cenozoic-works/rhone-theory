/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZero.Window

/-! # The maximal unblocked `k`-chains, counted -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open RhoZero

def Unblocked (γ : ℕ) (U : Finset ℕ) : Prop := ¬(γ ∈ U ∧ γ + 1 ∈ U)

def IsMaxUnblocked (γ : ℕ) (K U : Finset ℕ) : Prop :=
  U ⊆ K ∧ Unblocked γ U ∧ ∀ V ⊆ K, Unblocked γ V → U ⊆ V → V = U

theorem unblocked_mono {γ : ℕ} {U V : Finset ℕ} (h : U ⊆ V) (hV : Unblocked γ V) :
    Unblocked γ U := fun hU => hV ⟨h hU.1, h hU.2⟩

theorem isMaxUnblocked_erase_left {γ : ℕ} {K : Finset ℕ} (hγ1 : γ + 1 ∈ K) :
    IsMaxUnblocked γ K (K.erase γ) := by
  refine ⟨Finset.erase_subset _ _, fun h => (Finset.notMem_erase γ K) h.1, ?_⟩
  intro V hVK hV hsub
  have hmem : γ + 1 ∈ V := hsub (Finset.mem_erase.mpr ⟨by omega, hγ1⟩)
  have hnot : γ ∉ V := fun h => hV ⟨h, hmem⟩
  exact Finset.Subset.antisymm (fun a ha => Finset.mem_erase.mpr
    ⟨fun hh => hnot (hh ▸ ha), hVK ha⟩) hsub

theorem isMaxUnblocked_erase_right {γ : ℕ} {K : Finset ℕ} (hγ : γ ∈ K) :
    IsMaxUnblocked γ K (K.erase (γ + 1)) := by
  refine ⟨Finset.erase_subset _ _, fun h => (Finset.notMem_erase (γ + 1) K) h.2, ?_⟩
  intro V hVK hV hsub
  have hmem : γ ∈ V := hsub (Finset.mem_erase.mpr ⟨by omega, hγ⟩)
  have hnot : γ + 1 ∉ V := fun h => hV ⟨hmem, h⟩
  exact Finset.Subset.antisymm (fun a ha => Finset.mem_erase.mpr
    ⟨fun hh => hnot (hh ▸ ha), hVK ha⟩) hsub

theorem isMaxUnblocked_iff_of_blocked {γ : ℕ} {K : Finset ℕ} (hγ : γ ∈ K) (hγ1 : γ + 1 ∈ K)
    (U : Finset ℕ) :
    IsMaxUnblocked γ K U ↔ (U = K.erase γ ∨ U = K.erase (γ + 1)) := by
  constructor
  · rintro ⟨hUK, hU, hmax⟩
    by_cases hmem : γ ∈ U
    · have hnot : γ + 1 ∉ U := fun h => hU ⟨hmem, h⟩
      refine Or.inr (hmax (K.erase (γ + 1)) (Finset.erase_subset _ _) ?_ ?_).symm
      · exact fun h => (Finset.notMem_erase (γ + 1) K) h.2
      · exact fun a ha => Finset.mem_erase.mpr ⟨fun hh => hnot (hh ▸ ha), hUK ha⟩
    · refine Or.inl (hmax (K.erase γ) (Finset.erase_subset _ _) ?_ ?_).symm
      · exact fun h => (Finset.notMem_erase γ K) h.1
      · exact fun a ha => Finset.mem_erase.mpr ⟨fun hh => hmem (hh ▸ ha), hUK ha⟩
  · rintro (rfl | rfl)
    · exact isMaxUnblocked_erase_left hγ1
    · exact isMaxUnblocked_erase_right hγ

theorem two_maxUnblocked {γ : ℕ} {K : Finset ℕ} (hγ : γ ∈ K) (hγ1 : γ + 1 ∈ K) :
    K.erase γ ≠ K.erase (γ + 1) ∧ (K.erase γ).card + 1 = K.card
      ∧ (K.erase (γ + 1)).card + 1 = K.card := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 : γ + 1 ∈ K.erase γ := Finset.mem_erase.mpr ⟨by omega, hγ1⟩
    rw [h] at h1
    exact (Finset.notMem_erase (γ + 1) K) h1
  · rw [Finset.card_erase_of_mem hγ]
    have := Finset.card_pos.mpr ⟨γ, hγ⟩
    omega
  · rw [Finset.card_erase_of_mem hγ1]
    have := Finset.card_pos.mpr ⟨γ + 1, hγ1⟩
    omega

theorem isMaxUnblocked_iff_of_unblocked {γ : ℕ} {K : Finset ℕ} (h : ¬(γ ∈ K ∧ γ + 1 ∈ K))
    (U : Finset ℕ) : IsMaxUnblocked γ K U ↔ U = K := by
  constructor
  · rintro ⟨hUK, -, hmax⟩
    exact (hmax K (subset_refl K) h hUK).symm
  · intro hUK
    subst hUK
    exact ⟨subset_refl _, h, fun V hVK _ hKV => Finset.Subset.antisymm hVK hKV⟩

theorem card_eq_three_dichotomy {γ : ℕ} {K : Finset ℕ} (hK : K.card = 3) :
    (¬(γ ∈ K ∧ γ + 1 ∈ K) → ∀ U, IsMaxUnblocked γ K U ↔ (U = K ∧ U.card = 3))
      ∧ (γ ∈ K → γ + 1 ∈ K → ∀ U, IsMaxUnblocked γ K U
          ↔ ((U = K.erase γ ∨ U = K.erase (γ + 1)) ∧ U.card = 2)) := by
  constructor
  · intro h U
    rw [isMaxUnblocked_iff_of_unblocked h U]
    constructor
    · rintro rfl; exact ⟨rfl, hK⟩
    · exact fun hh => hh.1
  · intro hγ hγ1 U
    rw [isMaxUnblocked_iff_of_blocked hγ hγ1 U]
    obtain ⟨-, hc1, hc2⟩ := two_maxUnblocked hγ hγ1
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, by omega⟩
      · exact ⟨Or.inr rfl, by omega⟩
    · exact fun hh => hh.1

theorem blocked_pair_mem_Kwin (L : Prim) (hα : L.α = 1) (hβ : L.β = 1) (h3 : 3 ≤ L.γ) {n : ℕ}
    (hn : L.γ + 1 ≤ n) : L.γ ∈ Kwin L n ∧ L.γ + 1 ∈ Kwin L n :=
  ⟨(partner_mem_Kwin_iff L hα hβ (by omega)).mpr h3,
    (fullyTyped_mem_Kwin_iff L hα hβ n).mpr hn⟩

theorem maxUnblocked_Kwin (L : Prim) (hα : L.α = 1) (hβ : L.β = 1) (h3 : 3 ≤ L.γ) {n : ℕ}
    (hn : L.γ + 1 ≤ n) :
    (∀ U, IsMaxUnblocked L.γ (Kwin L n) U
        ↔ (U = (Kwin L n).erase L.γ ∨ U = (Kwin L n).erase (L.γ + 1)))
      ∧ (Kwin L n).erase L.γ ≠ (Kwin L n).erase (L.γ + 1)
      ∧ ((Kwin L n).erase L.γ).card + 1 = (Kwin L n).card
      ∧ ((Kwin L n).erase (L.γ + 1)).card + 1 = (Kwin L n).card := by
  obtain ⟨hγ, hγ1⟩ := blocked_pair_mem_Kwin L hα hβ h3 hn
  obtain ⟨hne, hc1, hc2⟩ := two_maxUnblocked hγ hγ1
  exact ⟨fun U => isMaxUnblocked_iff_of_blocked hγ hγ1 U, hne, hc1, hc2⟩

end Rhone.Algebra.RhoZeroCancellation
