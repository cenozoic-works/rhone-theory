/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Kingman

/-! # The `A ↔ B` swap functor on backward states -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ} {ρ : ℝ} {L : Finset (Lin n)} {p q : Lin n}

def swapP (p : Lin n) : Lin n := (p.2, p.1)

@[simp] theorem swapP_fst (p : Lin n) : (swapP p).1 = p.2 := rfl

@[simp] theorem swapP_snd (p : Lin n) : (swapP p).2 = p.1 := rfl

@[simp] theorem swapP_swapP (p : Lin n) : swapP (swapP p) = p := rfl

theorem swapP_involutive : Function.Involutive (swapP (n := n)) := swapP_swapP

theorem swapP_injective : Function.Injective (swapP (n := n)) := swapP_involutive.injective

def swapL (L : Finset (Lin n)) : Finset (Lin n) := L.image swapP

theorem mem_swapL {L : Finset (Lin n)} {q : Lin n} : q ∈ swapL L ↔ swapP q ∈ L := by
  constructor
  · intro h
    obtain ⟨r, hr, hrq⟩ := Finset.mem_image.1 h
    rw [← hrq, swapP_swapP]
    exact hr
  · intro h
    exact Finset.mem_image.2 ⟨swapP q, h, swapP_swapP q⟩

theorem swapP_mem_swapL {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) : swapP p ∈ swapL L :=
  mem_swapL.2 (by rw [swapP_swapP]; exact hp)

@[simp] theorem swapL_swapL (L : Finset (Lin n)) : swapL (swapL L) = L := by
  ext r
  rw [mem_swapL, mem_swapL, swapP_swapP]

@[simp] theorem card_swapL (L : Finset (Lin n)) : (swapL L).card = L.card :=
  Finset.card_image_of_injective _ swapP_injective

@[simp] theorem swapL_erase (L : Finset (Lin n)) (p : Lin n) :
    swapL (L.erase p) = (swapL L).erase (swapP p) :=
  Finset.image_erase swapP_injective L p

@[simp] theorem swapL_insert (L : Finset (Lin n)) (p : Lin n) :
    swapL (insert p L) = insert (swapP p) (swapL L) :=
  Finset.image_insert _ _ _

@[simp] theorem swapL_empty : swapL (∅ : Finset (Lin n)) = ∅ := rfl

theorem swapL_eq_empty_iff {L : Finset (Lin n)} : swapL L = ∅ ↔ L = ∅ :=
  Finset.image_eq_empty

theorem sum_swapL (S : Finset (Lin n)) (F : Lin n → ℝ) :
    (∑ x ∈ swapL S, F x) = ∑ x ∈ S, F (swapP x) :=
  Finset.sum_image fun _ _ _ _ hxy => swapP_injective hxy

theorem carA_swapL (L : Finset (Lin n)) : carA (swapL L) = swapL (carB L) := by
  ext r
  rw [mem_carA, mem_swapL, mem_swapL, mem_carB, swapP_snd]

theorem carB_swapL (L : Finset (Lin n)) : carB (swapL L) = swapL (carA L) := by
  ext r
  rw [mem_carB, mem_swapL, mem_swapL, mem_carA, swapP_fst]

theorem carC_swapL (L : Finset (Lin n)) : carC (swapL L) = swapL (carC L) := by
  ext r
  rw [mem_carC, mem_swapL, mem_swapL, mem_carC, swapP_fst, swapP_snd]
  tauto

@[simp] theorem na_swapL (L : Finset (Lin n)) : na (swapL L) = nb L := by
  rw [na, nb, carA_swapL, card_swapL]

@[simp] theorem nb_swapL (L : Finset (Lin n)) : nb (swapL L) = na L := by
  rw [na, nb, carB_swapL, card_swapL]

@[simp] theorem tt_swapL (L : Finset (Lin n)) : tt (swapL L) = tt L := by
  rw [tt, tt, carC_swapL, card_swapL]

theorem coverA_swapL (L : Finset (Lin n)) : coverA (swapL L) = coverB L := by
  ext k
  rw [mem_coverA, mem_coverB]
  constructor
  · rintro ⟨r, hr, hk⟩
    exact ⟨swapP r, mem_swapL.1 hr, hk⟩
  · rintro ⟨r, hr, hk⟩
    exact ⟨swapP r, swapP_mem_swapL hr, hk⟩

theorem coverB_swapL (L : Finset (Lin n)) : coverB (swapL L) = coverA L := by
  ext k
  rw [mem_coverB, mem_coverA]
  constructor
  · rintro ⟨r, hr, hk⟩
    exact ⟨swapP r, mem_swapL.1 hr, hk⟩
  · rintro ⟨r, hr, hk⟩
    exact ⟨swapP r, swapP_mem_swapL hr, hk⟩

theorem swapL_filter_snd (L : Finset (Lin n)) (F : Finset (Finset (Fin n))) :
    ((swapL L).filter fun r => r.1 ∈ F) = swapL (L.filter fun r => r.2 ∈ F) := by
  ext r
  rw [Finset.mem_filter, mem_swapL, mem_swapL, Finset.mem_filter, swapP_snd]

theorem wf_swapL {L : Finset (Lin n)} (h : WF L) : WF (swapL L) := by
  refine ⟨fun r hr => ?_, fun r hr r' hr' hne => ?_, fun r hr r' hr' hne => ?_⟩
  · rw [mem_swapL] at hr
    exact (h.carries _ hr).symm
  · rw [mem_swapL] at hr hr'
    exact h.disjB _ hr _ hr' fun hc => hne (swapP_injective hc)
  · rw [mem_swapL] at hr hr'
    exact h.disjA _ hr _ hr' fun hc => hne (swapP_injective hc)

theorem wf_swapL_iff {L : Finset (Lin n)} : WF (swapL L) ↔ WF L := by
  constructor
  · intro h
    have := wf_swapL h
    rwa [swapL_swapL] at this
  · exact wf_swapL

theorem swapL_coalL (L : Finset (Lin n)) (p q : Lin n) :
    swapL (coalL L p q) = coalL (swapL L) (swapP p) (swapP q) := by
  rw [coalL, coalL, swapL_insert, swapL_erase, swapL_erase]
  rfl

theorem swapL_recL (L : Finset (Lin n)) (p : Lin n) :
    swapL (recL L p) = recL (swapL L) (swapP p) := by
  rw [recL, recL, swapL_insert, swapL_insert, swapL_erase]
  exact Finset.insert_comm _ _ _

theorem dtotArg_swapL (ρ : ℝ) (L : Finset (Lin n)) : dtotArg ρ (swapL L) = dtotArg ρ L := by
  rw [dtotArg, dtotArg, card_swapL, tt_swapL]

theorem stepArg_swapL (ρ : ℝ) (g : Finset (Lin n) → ℝ) (L : Finset (Lin n)) :
    stepArg ρ (fun M => g (swapL M)) L = stepArg ρ g (swapL L) := by
  have hcoal : (∑ r ∈ swapL L, ∑ r' ∈ (swapL L).erase r, g (coalL (swapL L) r r'))
      = ∑ x ∈ L, ∑ y ∈ L.erase x, g (swapL (coalL L x y)) := by
    rw [sum_swapL]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← swapL_erase, sum_swapL]
    exact Finset.sum_congr rfl fun y _ => by rw [swapL_coalL]
  have hrec : (∑ r ∈ carC (swapL L), g (recL (swapL L) r))
      = ∑ x ∈ carC L, g (swapL (recL L x)) := by
    rw [carC_swapL, sum_swapL]
    exact Finset.sum_congr rfl fun x _ => by rw [swapL_recL]
  rw [stepArg, stepArg, hcoal, hrec]

end Rhone.Coalescent.MarginalLumping
