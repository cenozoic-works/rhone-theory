/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZeroCancellation.Poset

/-! # The dependency poset of a segment event set is disconnected -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open Finset

variable {F : Type*} [Field F] {E Token : Type*} [DecidableEq Token]

def Meets (supp : E → Finset Token) (f g : E) : Prop := (supp f ∩ supp g).Nonempty

theorem Meets.symm {supp : E → Finset Token} {f g : E} (h : Meets supp f g) :
    Meets supp g f := by
  obtain ⟨t, ht⟩ := h
  rw [Finset.mem_inter] at ht
  exact ⟨t, Finset.mem_inter.mpr ⟨ht.2, ht.1⟩⟩

theorem meets_self_of_nonempty {supp : E → Finset Token} {f : E} (h : (supp f).Nonempty) :
    Meets supp f f := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, Finset.mem_inter.mpr ⟨ht, ht⟩⟩

def lcClosure (supp : E → Finset Token) (S : Finset E) (eStar : E) : Finset E :=
  S.filter fun f => (supp f ∩ supp eStar).Nonempty

theorem mem_lcClosure {supp : E → Finset Token} {S : Finset E} {eStar f : E} :
    f ∈ lcClosure supp S eStar ↔ f ∈ S ∧ Meets supp f eStar := Finset.mem_filter

theorem lcClosure_subset (supp : E → Finset Token) (S : Finset E) (eStar : E) :
    lcClosure supp S eStar ⊆ S := Finset.filter_subset _ _

theorem lcClosure_card_le [DecidableEq E] (supp : E → Finset Token) (S : Finset E)
    (eStar : E) :
    (lcClosure supp S eStar).card
      ≤ (S.filter fun f => f ≠ eStar ∧ (supp f ∩ supp eStar).Nonempty).card + 1 := by
  have hsub : lcClosure supp S eStar ⊆
      insert eStar (S.filter fun f => f ≠ eStar ∧ (supp f ∩ supp eStar).Nonempty) := by
    intro f hf
    rw [mem_lcClosure] at hf
    rw [Finset.mem_insert]
    by_cases hfe : f = eStar
    · exact Or.inl hfe
    · exact Or.inr (Finset.mem_filter.mpr ⟨hf.1, hfe, hf.2⟩)
  calc (lcClosure supp S eStar).card
      ≤ (insert eStar (S.filter fun f => f ≠ eStar ∧ (supp f ∩ supp eStar).Nonempty)).card :=
        Finset.card_le_card hsub
    _ ≤ (S.filter fun f => f ≠ eStar ∧ (supp f ∩ supp eStar).Nonempty).card + 1 :=
        Finset.card_insert_le _ _

structure IsSegmentEvents (supp : E → Finset Token) (IsLC : E → Prop) (S : Finset E)
    (eStar : E) : Prop where
  mem : eStar ∈ S
  supp_nonempty : (supp eStar).Nonempty
  unique_lc : ∀ f ∈ S, IsLC f → f = eStar
  kills_supp_ne : ∀ f ∈ S, ∀ g ∈ S, f ≠ g → ¬ IsLC f → ¬ IsLC g → supp f ≠ supp g
  distinct_meet : ∀ f ∈ S, ∀ g ∈ S, supp f ≠ supp g → Meets supp f g →
    supp f = supp eStar ∨ supp g = supp eStar

namespace IsSegmentEvents

variable {supp : E → Finset Token} {IsLC : E → Prop} {S : Finset E} {eStar : E}

theorem mem_closure_self (h : IsSegmentEvents supp IsLC S eStar) :
    eStar ∈ lcClosure supp S eStar :=
  mem_lcClosure.mpr ⟨h.mem, meets_self_of_nonempty h.supp_nonempty⟩

theorem closure_nonempty (h : IsSegmentEvents supp IsLC S eStar) :
    (lcClosure supp S eStar).Nonempty := ⟨eStar, h.mem_closure_self⟩

theorem meets_closure (h : IsSegmentEvents supp IsLC S eStar) {f g : E} (hf : f ∈ S) (hg : g ∈ S)
    (hfg : f ≠ g) (hmeet : Meets supp f g) :
    f ∈ lcClosure supp S eStar ∧ g ∈ lcClosure supp S eStar := by
  have hself : ∀ p : E, supp p = supp eStar → Meets supp p eStar := by
    intro p hp
    change (supp p ∩ supp eStar).Nonempty
    rw [hp, Finset.inter_self]
    exact h.supp_nonempty
  have htrans : ∀ p q : E, supp q = supp eStar → Meets supp p q → Meets supp p eStar := by
    intro p q hq hpq
    change (supp p ∩ supp eStar).Nonempty
    rw [← hq]
    exact hpq
  rcases eq_or_ne (supp f) (supp g) with hsupp | hsupp
  · have hone : supp f = supp eStar ∨ supp g = supp eStar := by
      by_cases hlcf : IsLC f
      · exact Or.inl (by rw [h.unique_lc f hf hlcf])
      · by_cases hlcg : IsLC g
        · exact Or.inr (by rw [h.unique_lc g hg hlcg])
        · exact absurd hsupp (h.kills_supp_ne f hf g hg hfg hlcf hlcg)
    rcases hone with hfe | hge
    · exact ⟨mem_lcClosure.mpr ⟨hf, hself f hfe⟩,
        mem_lcClosure.mpr ⟨hg, hself g (hsupp ▸ hfe)⟩⟩
    · exact ⟨mem_lcClosure.mpr ⟨hf, hself f (hsupp.trans hge)⟩,
        mem_lcClosure.mpr ⟨hg, hself g hge⟩⟩
  · rcases h.distinct_meet f hf g hg hsupp hmeet with hfe | hge
    · exact ⟨mem_lcClosure.mpr ⟨hf, hself f hfe⟩,
        mem_lcClosure.mpr ⟨hg, htrans g f hfe hmeet.symm⟩⟩
    · exact ⟨mem_lcClosure.mpr ⟨hf, htrans f g hge hmeet⟩,
        mem_lcClosure.mpr ⟨hg, hself g hge⟩⟩

theorem isolated (h : IsSegmentEvents supp IsLC S eStar) {R : E → E → Prop}
    (hR : ∀ f g, R f g → f ≠ g ∧ Meets supp f g) {a : E} (ha : a ∈ S)
    (hac : a ∉ lcClosure supp S eStar) {b : E} (hb : b ∈ S) : ¬ R a b ∧ ¬ R b a := by
  constructor
  · intro hab
    exact hac (h.meets_closure ha hb (hR a b hab).1 (hR a b hab).2).1
  · intro hba
    exact hac (h.meets_closure hb ha (hR b a hba).1 (hR b a hba).2).2

theorem Fsum_eq_zero (h : IsSegmentEvents supp IsLC S eStar) {R : E → E → Prop}
    (hR : ∀ f g, R f g → f ≠ g ∧ Meets supp f g) (hirr : ∀ f, ¬ R f f) (x : E → F)
    (hcard : (lcClosure supp S eStar).card < S.card) (htot : ∑ e ∈ S, x e = 0)
    (hproper : ∀ U ⊆ S, U.Nonempty → U ≠ S → ∑ e ∈ U, x e ≠ 0) :
    Fsum R x S = 0 := by
  classical
  have hsub : lcClosure supp S eStar ⊆ S := lcClosure_subset supp S eStar
  have hiso : (S \ lcClosure supp S eStar).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    omega
  have hcompl : S \ (S \ lcClosure supp S eStar) = lcClosure supp S eStar := by
    rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hsub]
  refine Fsum_eq_zero_of_disconnected hirr x Finset.sdiff_subset hiso ?_ ?_ htot hproper
  · rw [hcompl]
    exact h.closure_nonempty
  · intro a ha b hb
    rw [Finset.mem_sdiff] at ha
    rw [hcompl] at hb
    exact h.isolated hR ha.1 ha.2 (hsub hb)

end IsSegmentEvents

end Rhone.Algebra.RhoZeroCancellation
