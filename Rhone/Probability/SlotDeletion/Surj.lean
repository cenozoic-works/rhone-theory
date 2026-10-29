/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.BiallelicDenominator

/-! # `Ξ` is onto, and DL‑3 at every configuration -/

@[expose] public section

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section Slots

variable (ξ : Config 2 2)

abbrev SlotC : Type := Σ p : Fin 2 × Fin 2, Fin (ξ.c p.1 p.2)

abbrev SlotA : Type := (Σ i : Fin 2, Fin (ξ.a i)) ⊕ SlotC ξ

abbrev SlotB : Type := (Σ j : Fin 2, Fin (ξ.b j)) ⊕ SlotC ξ

def alphaOf : SlotA ξ → Fin 2 := Sum.elim (fun z => z.1) (fun z => z.1.1)

def betaOf : SlotB ξ → Fin 2 := Sum.elim (fun z => z.1) (fun z => z.1.2)

def matchOf : Finset (SlotA ξ × SlotB ξ) :=
  univ.image fun z : SlotC ξ => (Sum.inr z, Sum.inr z)

variable {ξ}

theorem mem_matchOf {r : SlotA ξ × SlotB ξ} :
    r ∈ matchOf ξ ↔ ∃ z : SlotC ξ, r = (Sum.inr z, Sum.inr z) := by
  simp only [matchOf, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem isMatching_matchOf : IsMatching (matchOf ξ) where
  fst r hr r' hr' h := by
    obtain ⟨z, rfl⟩ := mem_matchOf.mp hr
    obtain ⟨z', rfl⟩ := mem_matchOf.mp hr'
    have : z = z' := Sum.inr_injective h
    rw [this]
  snd r hr r' hr' h := by
    obtain ⟨z, rfl⟩ := mem_matchOf.mp hr
    obtain ⟨z', rfl⟩ := mem_matchOf.mp hr'
    have : z = z' := Sum.inr_injective h
    rw [this]

theorem mem_freeA_matchOf {u : SlotA ξ} :
    u ∈ freeA (matchOf ξ) ↔ ∃ w : Σ i : Fin 2, Fin (ξ.a i), u = Sum.inl w := by
  rw [mem_freeA]
  constructor
  · intro h
    cases u with
    | inl w => exact ⟨w, rfl⟩
    | inr z => exact absurd (mem_matchOf.mpr ⟨z, rfl⟩) (h (Sum.inr z))
  · rintro ⟨w, rfl⟩ v hv
    obtain ⟨z, hz⟩ := mem_matchOf.mp hv
    exact Sum.inl_ne_inr (congrArg Prod.fst hz)

theorem mem_freeB_matchOf {v : SlotB ξ} :
    v ∈ freeB (matchOf ξ) ↔ ∃ w : Σ j : Fin 2, Fin (ξ.b j), v = Sum.inl w := by
  rw [mem_freeB]
  constructor
  · intro h
    cases v with
    | inl w => exact ⟨w, rfl⟩
    | inr z => exact absurd (mem_matchOf.mpr ⟨z, rfl⟩) (h (Sum.inr z))
  · rintro ⟨w, rfl⟩ u hu
    obtain ⟨z, hz⟩ := mem_matchOf.mp hu
    exact Sum.inl_ne_inr (congrArg Prod.snd hz)

theorem card_filter_freeA_matchOf (i : Fin 2) :
    ((freeA (matchOf ξ)).filter fun u => alphaOf ξ u = i).card = ξ.a i := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.a i))))
    (t := (freeA (matchOf ξ)).filter fun u => alphaOf ξ u = i)
    (fun k _ => (Sum.inl ⟨i, k⟩ : SlotA ξ)) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_freeA_matchOf.mpr ⟨⟨i, k⟩, rfl⟩, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (⟨i, k⟩ : Σ i : Fin 2, Fin (ξ.a i)) = ⟨i, k'⟩ := Sum.inl_injective hkk
    exact eq_of_heq (Sigma.mk.inj h1).2
  · intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨w, rfl⟩ := mem_freeA_matchOf.mp hu.1
    obtain ⟨i', k⟩ := w
    have hi' : i' = i := hu.2
    subst hi'
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem card_filter_freeB_matchOf (j : Fin 2) :
    ((freeB (matchOf ξ)).filter fun v => betaOf ξ v = j).card = ξ.b j := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.b j))))
    (t := (freeB (matchOf ξ)).filter fun v => betaOf ξ v = j)
    (fun k _ => (Sum.inl ⟨j, k⟩ : SlotB ξ)) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_freeB_matchOf.mpr ⟨⟨j, k⟩, rfl⟩, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (⟨j, k⟩ : Σ j : Fin 2, Fin (ξ.b j)) = ⟨j, k'⟩ := Sum.inl_injective hkk
    exact eq_of_heq (Sigma.mk.inj h1).2
  · intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨w, rfl⟩ := mem_freeB_matchOf.mp hv.1
    obtain ⟨j', k⟩ := w
    have hj' : j' = j := hv.2
    subst hj'
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem card_filter_matchOf (i j : Fin 2) :
    ((matchOf ξ).filter fun r => alphaOf ξ r.1 = i ∧ betaOf ξ r.2 = j).card = ξ.c i j := by
  have h := (Finset.card_bij
    (s := (univ : Finset (Fin (ξ.c i j))))
    (t := (matchOf ξ).filter fun r => alphaOf ξ r.1 = i ∧ betaOf ξ r.2 = j)
    (fun k _ => ((Sum.inr ⟨(i, j), k⟩ : SlotA ξ), (Sum.inr ⟨(i, j), k⟩ : SlotB ξ))) ?_ ?_ ?_)
  · rw [← h, Finset.card_univ, Fintype.card_fin]
  · intro k _
    exact Finset.mem_filter.mpr ⟨mem_matchOf.mpr ⟨⟨(i, j), k⟩, rfl⟩, rfl, rfl⟩
  · intro k _ k' _ hkk
    have h1 : (Sum.inr ⟨(i, j), k⟩ : SlotA ξ) = Sum.inr ⟨(i, j), k'⟩ := congrArg Prod.fst hkk
    have h2 : (⟨(i, j), k⟩ : SlotC ξ) = ⟨(i, j), k'⟩ := Sum.inr_injective h1
    exact eq_of_heq (Sigma.mk.inj h2).2
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨z, rfl⟩ := mem_matchOf.mp hr.1
    obtain ⟨p, k⟩ := z
    have hp : p = (i, j) := Prod.ext hr.2.1 hr.2.2
    subst hp
    exact ⟨k, Finset.mem_univ _, rfl⟩

theorem xi_matchOf : xi (matchOf ξ) (alphaOf ξ) (betaOf ξ) = ξ :=
  Config.ext (funext fun i => card_filter_freeA_matchOf i)
    (funext fun j => card_filter_freeB_matchOf j)
    (funext fun i => funext fun j => card_filter_matchOf i j)

theorem card_SlotA : Fintype.card (SlotA ξ) = ξ.nA := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Config.nA, Config.sumA, Config.t, Fintype.sum_prod_type]

theorem card_SlotB : Fintype.card (SlotB ξ) = ξ.nB := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Config.nB, Config.sumB, Config.t, Fintype.sum_prod_type]

end Slots

section Final

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (A : Subring F)
include hθA hθB hρ hq

theorem Dfull_mul_q_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (ξ : Config 2 2) :
    LinearAlgebra.SlotDeletion.Dfull θA θB ρ ξ.nA ξ.nB * q ξ ∈ A := by
  have h := Dfull_mul_q_xi_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB
    (matchOf ξ) isMatching_matchOf (alphaOf ξ) (betaOf ξ)
  rwa [xi_matchOf, card_SlotA, card_SlotB] at h

end Final

end Rhone.Probability.SlotDeletion
