/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.GeneralAlphabet.CentredClosedForm

/-! # `Ξ` is onto at a general alphabet, at every configuration -/

@[expose] public section

universe u v

namespace Rhone.Probability.GeneralAlphabet

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open LinearAlgebra.SlotDeletion SlotDeletion

variable {KA KB : ℕ}

section Slots

variable (ξ : Config KA KB)

abbrev CSlotC : Type := Σ p : Fin KA × Fin KB, Fin (ξ.c p.1 p.2)

abbrev CSlotA : Type := (Σ i : Fin KA, Fin (ξ.a i)) ⊕ CSlotC ξ

abbrev CSlotB : Type := (Σ j : Fin KB, Fin (ξ.b j)) ⊕ CSlotC ξ

def cAlpha : CSlotA ξ → Fin KA := Sum.elim (fun z => z.1) (fun z => z.1.1)

def cBeta : CSlotB ξ → Fin KB := Sum.elim (fun z => z.1) (fun z => z.1.2)

def cMatch : Finset (CSlotA ξ × CSlotB ξ) :=
  univ.image fun z : CSlotC ξ => (Sum.inr z, Sum.inr z)

variable {ξ}

theorem mem_cMatch {r : CSlotA ξ × CSlotB ξ} :
    r ∈ cMatch ξ ↔ ∃ z : CSlotC ξ, r = (Sum.inr z, Sum.inr z) := by
  simp only [cMatch, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem isMatching_cMatch : IsMatching (cMatch ξ) where
  fst r hr r' hr' h := by
    obtain ⟨z, rfl⟩ := mem_cMatch.mp hr
    obtain ⟨z', rfl⟩ := mem_cMatch.mp hr'
    have hz : z = z' := Sum.inr_injective h
    rw [hz]
  snd r hr r' hr' h := by
    obtain ⟨z, rfl⟩ := mem_cMatch.mp hr
    obtain ⟨z', rfl⟩ := mem_cMatch.mp hr'
    have hz : z = z' := Sum.inr_injective h
    rw [hz]

theorem mem_freeA_cMatch {t : CSlotA ξ} :
    t ∈ freeA (cMatch ξ) ↔ ∃ w : Σ i : Fin KA, Fin (ξ.a i), t = Sum.inl w := by
  rw [mem_freeA]
  constructor
  · intro h
    cases t with
    | inl w => exact ⟨w, rfl⟩
    | inr z => exact absurd (mem_cMatch.mpr ⟨z, rfl⟩) (h (Sum.inr z))
  · rintro ⟨w, rfl⟩ v hv
    obtain ⟨z, hz⟩ := mem_cMatch.mp hv
    exact Sum.inl_ne_inr (congrArg Prod.fst hz)

theorem mem_freeB_cMatch {t : CSlotB ξ} :
    t ∈ freeB (cMatch ξ) ↔ ∃ w : Σ j : Fin KB, Fin (ξ.b j), t = Sum.inl w := by
  rw [mem_freeB]
  constructor
  · intro h
    cases t with
    | inl w => exact ⟨w, rfl⟩
    | inr z => exact absurd (mem_cMatch.mpr ⟨z, rfl⟩) (h (Sum.inr z))
  · rintro ⟨w, rfl⟩ t' ht'
    obtain ⟨z, hz⟩ := mem_cMatch.mp ht'
    exact Sum.inl_ne_inr (congrArg Prod.snd hz)

theorem card_filter_freeA_cMatch (i : Fin KA) :
    ((freeA (cMatch ξ)).filter fun t => cAlpha ξ t = i).card = ξ.a i := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.a i))))
    (t := (freeA (cMatch ξ)).filter fun t => cAlpha ξ t = i)
    (fun k _ => (Sum.inl ⟨i, k⟩ : CSlotA ξ)) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_freeA_cMatch.mpr ⟨⟨i, k⟩, rfl⟩, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (⟨i, k⟩ : Σ i : Fin KA, Fin (ξ.a i)) = ⟨i, k'⟩ := Sum.inl_injective hkk
    exact eq_of_heq (Sigma.mk.inj h1).2
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨w, rfl⟩ := mem_freeA_cMatch.mp ht.1
    obtain ⟨i', k⟩ := w
    have hi' : i' = i := ht.2
    subst hi'
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem card_filter_freeB_cMatch (j : Fin KB) :
    ((freeB (cMatch ξ)).filter fun t => cBeta ξ t = j).card = ξ.b j := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.b j))))
    (t := (freeB (cMatch ξ)).filter fun t => cBeta ξ t = j)
    (fun k _ => (Sum.inl ⟨j, k⟩ : CSlotB ξ)) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_freeB_cMatch.mpr ⟨⟨j, k⟩, rfl⟩, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (⟨j, k⟩ : Σ j : Fin KB, Fin (ξ.b j)) = ⟨j, k'⟩ := Sum.inl_injective hkk
    exact eq_of_heq (Sigma.mk.inj h1).2
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨w, rfl⟩ := mem_freeB_cMatch.mp ht.1
    obtain ⟨j', k⟩ := w
    have hj' : j' = j := ht.2
    subst hj'
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem card_filter_cMatch (i : Fin KA) (j : Fin KB) :
    ((cMatch ξ).filter fun r => cAlpha ξ r.1 = i ∧ cBeta ξ r.2 = j).card = ξ.c i j := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.c i j))))
    (t := (cMatch ξ).filter fun r => cAlpha ξ r.1 = i ∧ cBeta ξ r.2 = j)
    (fun k _ => ((Sum.inr ⟨(i, j), k⟩ : CSlotA ξ), (Sum.inr ⟨(i, j), k⟩ : CSlotB ξ))) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_cMatch.mpr ⟨⟨(i, j), k⟩, rfl⟩, rfl, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (Sum.inr ⟨(i, j), k⟩ : CSlotA ξ) = Sum.inr ⟨(i, j), k'⟩ := congrArg Prod.fst hkk
    have h2 : (⟨(i, j), k⟩ : CSlotC ξ) = ⟨(i, j), k'⟩ := Sum.inr_injective h1
    exact eq_of_heq (Sigma.mk.inj h2).2
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨z, rfl⟩ := mem_cMatch.mp hr.1
    obtain ⟨p, k⟩ := z
    have hp : p = (i, j) := Prod.ext hr.2.1 hr.2.2
    subst hp
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem cxi_eq : xi (cMatch ξ) (cAlpha ξ) (cBeta ξ) = ξ :=
  Config.ext (funext fun i => card_filter_freeA_cMatch i)
    (funext fun j => card_filter_freeB_cMatch j)
    (funext fun i => funext fun j => card_filter_cMatch i j)

theorem card_CSlotA : Fintype.card (CSlotA ξ) = ξ.nA := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Config.nA, Config.sumA, Config.t, Fintype.sum_prod_type]

theorem card_CSlotB : Fintype.card (CSlotB ξ) = ξ.nB := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Config.nB, Config.sumB, Config.t, Fintype.sum_prod_type]

end Slots

section AtConfig

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem exists_q_sub_qHat_eq_UA_mul_config (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    {i₀ : Fin KA} (hκ : UA πA i₀ i₀ ≠ 0) (ξ : Config KA KB) (hnA : ξ.nA = 2) :
    ∃ (u₁ u₂ : CSlotA ξ) (G : F), u₁ ≠ u₂ ∧
      q ξ - qHat θA θB πA πB ξ = UA πA (cAlpha ξ u₁) (cAlpha ξ u₂) * G ∧
      ∀ α : CSlotA ξ → Fin KA,
        q (xi (cMatch ξ) α (cBeta ξ)) - qHat θA θB πA πB (xi (cMatch ξ) α (cBeta ξ))
          = UA πA (α u₁) (α u₂) * G := by
  have hcard : Fintype.card (CSlotA ξ) = 2 := by rw [card_CSlotA, hnA]
  have hnt : Nontrivial (CSlotA ξ) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u₁, u₂, hne⟩ := exists_pair_ne (CSlotA ξ)
  obtain ⟨G, hG⟩ := exists_q_sub_qHat_eq_UA_mul hθA hθB hρ hq hπA hπB hcard hne hκ
    (cMatch ξ) isMatching_cMatch (cBeta ξ)
  refine ⟨u₁, u₂, G, hne, ?_, hG⟩
  have h := hG (cAlpha ξ)
  rwa [cxi_eq] at h

end AtConfig

end Rhone.Probability.GeneralAlphabet
