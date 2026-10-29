/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZeroCancellation.Events
public import Rhone.Algebra.RhoZeroCancellation.Segment

/-! # The blocked row vanishes at the row level, in the abstract event-set model -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open Finset RhoZero

scoped instance : DecidableEq MoveClass := fun a b => by
  cases a <;> cases b <;>
    first
      | exact isTrue rfl
      | exact isFalse (by intro h; cases h)

variable {F : Type*} [Field F] {E Token : Type*}

def mult (cls : E → MoveClass) (U : Finset E) (m : MoveClass) : ℕ :=
  (U.filter fun e => cls e = m).card

theorem mult_mono (cls : E → MoveClass) {U S : Finset E} (h : U ⊆ S) (m : MoveClass) :
    mult cls U m ≤ mult cls S m :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem mult_insert [DecidableEq E] (cls : E → MoveClass) {a : E} {U : Finset E} (ha : a ∉ U)
    (m : MoveClass) :
    mult cls (insert a U) m = mult cls U m + (if cls a = m then 1 else 0) := by
  rw [mult, mult, Finset.filter_insert]
  by_cases h : cls a = m
  · rw [ite_eq_left h, ite_eq_left h,
      Finset.card_insert_of_notMem fun hh => ha (Finset.mem_filter.mp hh).1]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

theorem sum_mult (cls : E → MoveClass) (U : Finset E) :
    mult cls U .M1 + mult cls U .M2 + mult cls U .M3 + mult cls U .M4 + mult cls U .M5
      + mult cls U .M6 = U.card := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [mult]
  | insert a U ha IH =>
    rw [Finset.card_insert_of_notMem ha]
    simp only [mult_insert cls ha]
    cases cls a <;> simp <;> omega

theorem sum_delta_eq_deltaSum (θA θB : F) (k : ℕ) (cls : E → MoveClass)
    (U : Finset E) :
    ∑ e ∈ U, delta θA θB k (cls e)
      = deltaSum θA θB k (mult cls U .M1) (mult cls U .M2) (mult cls U .M3) (mult cls U .M4)
          (mult cls U .M5) (mult cls U .M6) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [mult, deltaSum]
  | insert a U ha IH =>
    rw [Finset.sum_insert ha, IH]
    simp only [mult_insert cls ha]
    cases cls a <;> simp only [deltaSum] <;> norm_num <;> ring

theorem sum_delta_family_eq_zero (θA θB : F) (k : ℕ)
    (hu : (k : F) - 1 = -(θA + θB)) (cls : E → MoveClass) (S : Finset E)
    (hfam : IsBlockedFamily (mult cls S .M1) (mult cls S .M2) (mult cls S .M3) (mult cls S .M4)
      (mult cls S .M5) (mult cls S .M6)) :
    ∑ e ∈ S, delta θA θB k (cls e) = 0 := by
  rw [sum_delta_eq_deltaSum]
  exact deltaSum_family_eq_zero θA θB k hu hfam

theorem sum_delta_proper_ne_zero (θA θB : F) (k : ℕ)
    (hu : (k : F) - 1 = -(θA + θB))
    (hind : ∀ a b : ℤ, ¬(a = 0 ∧ b = 0) → (a : F) * ((k : F) - 1) + (b : F) * θA ≠ 0)
    (cls : E → MoveClass) (S : Finset E)
    (hfam : IsBlockedFamily (mult cls S .M1) (mult cls S .M2) (mult cls S .M3) (mult cls S .M4)
      (mult cls S .M5) (mult cls S .M6))
    (U : Finset E) (hU : U ⊆ S) (hUne : U.Nonempty) (hUS : U ≠ S) :
    ∑ e ∈ U, delta θA θB k (cls e) ≠ 0 := by
  rw [sum_delta_eq_deltaSum]
  refine deltaSum_proper_ne_zero θA θB k hu hind hfam (mult_mono cls hU _) (mult_mono cls hU _)
    (mult_mono cls hU _) (mult_mono cls hU _) (mult_mono cls hU _) (mult_mono cls hU _) ?_ ?_
  · rw [sum_mult]
    exact Finset.card_pos.mpr hUne
  · rw [sum_mult, sum_mult]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU, hUS⟩)

noncomputable def eventSetTransfer {Idx : Type*} (𝒮 : Finset Idx) (w : Idx → F)
    (R : Idx → E → E → Prop) (x : Idx → E → F) (S : Idx → Finset E) : F :=
  ∑ s ∈ 𝒮, w s * Fsum (R s) (x s) (S s)

theorem eventSetTransfer_eq_zero {Idx : Type*} [DecidableEq Token] (𝒮 : Finset Idx) (w : Idx → F)
    {R : Idx → E → E → Prop} {x : Idx → E → F} {S : Idx → Finset E}
    {supp : Idx → E → Finset Token} {IsLC : Idx → E → Prop} {eStar : Idx → E}
    (hseg : ∀ s ∈ 𝒮, IsSegmentEvents (supp s) (IsLC s) (S s) (eStar s))
    (hR : ∀ s ∈ 𝒮, ∀ f g, R s f g → f ≠ g ∧ Meets (supp s) f g)
    (hirr : ∀ s ∈ 𝒮, ∀ f, ¬ R s f f)
    (hcard : ∀ s ∈ 𝒮, (lcClosure (supp s) (S s) (eStar s)).card < (S s).card)
    (htot : ∀ s ∈ 𝒮, ∑ e ∈ S s, x s e = 0)
    (hproper : ∀ s ∈ 𝒮, ∀ U ⊆ S s, U.Nonempty → U ≠ S s → ∑ e ∈ U, x s e ≠ 0) :
    eventSetTransfer 𝒮 w R x S = 0 := by
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [(hseg s hs).Fsum_eq_zero (hR s hs) (hirr s hs) (x s) (hcard s hs) (htot s hs)
    (hproper s hs), mul_zero]

theorem blocked_row_eq_zero {Target Idx : Type*} [DecidableEq Token]
    (θA θB : F) (k : ℕ) (hu : (k : F) - 1 = -(θA + θB))
    (hind : ∀ a b : ℤ, ¬(a = 0 ∧ b = 0) → (a : F) * ((k : F) - 1) + (b : F) * θA ≠ 0)
    (𝒮 : Target → Finset Idx) (w : Idx → F) {S : Idx → Finset E} {cls : Idx → E → MoveClass}
    {R : Idx → E → E → Prop} {supp : Idx → E → Finset Token} {IsLC : Idx → E → Prop}
    {eStar : Idx → E}
    (hfam : ∀ t, ∀ s ∈ 𝒮 t, IsBlockedFamily (mult (cls s) (S s) .M1) (mult (cls s) (S s) .M2)
      (mult (cls s) (S s) .M3) (mult (cls s) (S s) .M4) (mult (cls s) (S s) .M5)
      (mult (cls s) (S s) .M6))
    (hseg : ∀ t, ∀ s ∈ 𝒮 t, IsSegmentEvents (supp s) (IsLC s) (S s) (eStar s))
    (hR : ∀ t, ∀ s ∈ 𝒮 t, ∀ f g, R s f g → f ≠ g ∧ Meets (supp s) f g)
    (hirr : ∀ t, ∀ s ∈ 𝒮 t, ∀ f, ¬ R s f f)
    (hcard : ∀ t, ∀ s ∈ 𝒮 t, (lcClosure (supp s) (S s) (eStar s)).card < (S s).card) :
    ∀ t : Target,
      eventSetTransfer (𝒮 t) w R (fun s e => delta θA θB k (cls s e)) S = 0 := by
  intro t
  refine eventSetTransfer_eq_zero (𝒮 t) w (hseg t) (hR t) (hirr t) (hcard t) ?_ ?_
  · intro s hs
    exact sum_delta_family_eq_zero θA θB k hu (cls s) (S s) (hfam t s hs)
  · intro s hs U hU hUne hUS
    exact sum_delta_proper_ne_zero θA θB k hu hind (cls s) (S s) (hfam t s hs) U hU hUne hUS

theorem lcClosure_card_lt_of_neighbour_bound [DecidableEq E] [DecidableEq Token]
    (supp : E → Finset Token) (S : Finset E) (eStar : E) (b : ℕ)
    (hN : (S.filter fun f => f ≠ eStar ∧ (supp f ∩ supp eStar).Nonempty).card ≤ b)
    (hS : b + 1 < S.card) : (lcClosure supp S eStar).card < S.card :=
  lt_of_le_of_lt (le_trans (lcClosure_card_le supp S eStar) (by omega)) hS

end Rhone.Algebra.RhoZeroCancellation
