/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Support

/-! # The `A ↔ B` symmetry of the partition-carrying chain -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset Filter Topology TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ} {θA θB ρ : ℝ} {ζA ζB : Blocks n}

def swapLin (p : Lin n) : Lin n := (p.2, p.1)

def swapL (L : Finset (Lin n)) : Finset (Lin n) := L.image swapLin

def swapP (s : PSt n) : PSt n := (swapL s.1, s.2.2, s.2.1)

@[simp] theorem swapLin_swapLin (p : Lin n) : swapLin (swapLin p) = p := rfl

theorem swapLin_injective : Function.Injective (swapLin (n := n)) :=
  fun p q h => by rw [← swapLin_swapLin p, h, swapLin_swapLin]

@[simp] theorem mem_swapL {L : Finset (Lin n)} {p : Lin n} : p ∈ swapL L ↔ swapLin p ∈ L := by
  simp only [swapL, Finset.mem_image]
  exact ⟨fun ⟨q, hq, hqp⟩ => by rw [← hqp]; simpa using hq, fun h => ⟨swapLin p, h, rfl⟩⟩

@[simp] theorem swapL_swapL (L : Finset (Lin n)) : swapL (swapL L) = L := by
  ext p
  simp

@[simp] theorem swapL_empty : swapL (∅ : Finset (Lin n)) = ∅ := by simp [swapL]

theorem swapL_eq_empty_iff {L : Finset (Lin n)} : swapL L = ∅ ↔ L = ∅ := by
  constructor
  · intro h
    rw [← swapL_swapL L, h, swapL_empty]
  · rintro rfl
    exact swapL_empty

theorem sum_swapL {M : Type*} [AddCommMonoid M] (L : Finset (Lin n)) (f : Lin n → M) :
    (∑ p ∈ swapL L, f p) = ∑ p ∈ L, f (swapLin p) :=
  Finset.sum_image fun _ _ _ _ h => swapLin_injective h

theorem swapL_erase (L : Finset (Lin n)) (p : Lin n) :
    swapL (L.erase p) = (swapL L).erase (swapLin p) := by
  ext r
  simp only [mem_swapL, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (by rw [hc, swapLin_swapLin]), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h1 (by rw [← hc, swapLin_swapLin]), h2⟩

@[simp] theorem swapL_insert (L : Finset (Lin n)) (p : Lin n) :
    swapL (insert p L) = insert (swapLin p) (swapL L) := by
  ext r
  simp only [mem_swapL, Finset.mem_insert]
  exact ⟨fun h => h.imp (fun hc => by rw [← swapLin_swapLin r, hc]) id,
    fun h => h.imp (fun hc => by rw [hc, swapLin_swapLin]) id⟩

@[simp] theorem carA_swapL (L : Finset (Lin n)) : carA (swapL L) = swapL (carB L) := by
  ext p
  simp only [mem_carA, mem_carB, mem_swapL]
  rfl

@[simp] theorem carB_swapL (L : Finset (Lin n)) : carB (swapL L) = swapL (carA L) := by
  ext p
  simp only [mem_carA, mem_carB, mem_swapL]
  rfl

@[simp] theorem carC_swapL (L : Finset (Lin n)) : carC (swapL L) = swapL (carC L) := by
  ext p
  simp only [mem_carC, mem_swapL]
  exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

@[simp] theorem card_swapL (L : Finset (Lin n)) : (swapL L).card = L.card :=
  Finset.card_image_of_injective _ swapLin_injective

theorem na_swapL (L : Finset (Lin n)) : na (swapL L) = nb L := by
  unfold na nb
  rw [carA_swapL, card_swapL]

theorem nb_swapL (L : Finset (Lin n)) : nb (swapL L) = na L := by
  unfold na nb
  rw [carB_swapL, card_swapL]

theorem tt_swapL (L : Finset (Lin n)) : tt (swapL L) = tt L := by
  unfold tt
  rw [carC_swapL, card_swapL]

theorem dtot_swapL (L : Finset (Lin n)) : dtot θB θA ρ (swapL L) = dtot θA θB ρ L := by
  rw [dtot, dtot, card_swapL, na_swapL, nb_swapL, tt_swapL]
  ring

theorem coalL_swapL (L : Finset (Lin n)) (p q : Lin n) :
    coalL (swapL L) (swapLin p) (swapLin q) = swapL (coalL L p q) := by
  rw [coalL, coalL, swapL_insert, swapL_erase, swapL_erase]
  rfl

theorem mutAL_swapL (L : Finset (Lin n)) (p : Lin n) :
    mutAL (swapL L) (swapLin p) = swapL (mutBL L p) := by
  rw [mutAL, mutBL]
  by_cases h : p.1 = ∅
  · rw [ite_eq_left (show (swapLin p).2 = ∅ from h), ite_eq_left h, swapL_erase]
  · rw [ite_eq_right (show ¬ (swapLin p).2 = ∅ from h), ite_eq_right h, swapL_insert, swapL_erase]
    rfl

theorem mutBL_swapL (L : Finset (Lin n)) (p : Lin n) :
    mutBL (swapL L) (swapLin p) = swapL (mutAL L p) := by
  rw [mutBL, mutAL]
  by_cases h : p.2 = ∅
  · rw [ite_eq_left (show (swapLin p).1 = ∅ from h), ite_eq_left h, swapL_erase]
  · rw [ite_eq_right (show ¬ (swapLin p).1 = ∅ from h), ite_eq_right h, swapL_insert, swapL_erase]
    rfl

theorem recL_swapL (L : Finset (Lin n)) (p : Lin n) :
    recL (swapL L) (swapLin p) = swapL (recL L p) := by
  rw [recL, recL, swapL_insert, swapL_insert, swapL_erase, Finset.insert_comm]
  rfl

theorem wf_swapL {L : Finset (Lin n)} (h : WF L) : WF (swapL L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact (h.carries _ (mem_swapL.1 hp)).symm
  · intro p hp q hq hne
    exact h.disjB _ (mem_swapL.1 hp) _ (mem_swapL.1 hq) fun hc => hne (swapLin_injective hc)
  · intro p hp q hq hne
    exact h.disjA _ (mem_swapL.1 hp) _ (mem_swapL.1 hq) fun hc => hne (swapLin_injective hc)

@[simp] theorem coverA_swapL (L : Finset (Lin n)) : coverA (swapL L) = coverB L := by
  ext k
  simp only [mem_coverA, mem_coverB, mem_swapL]
  exact ⟨fun ⟨p, hp, hk⟩ => ⟨swapLin p, hp, hk⟩,
    fun ⟨p, hp, hk⟩ => ⟨swapLin p, by simpa using hp, hk⟩⟩

@[simp] theorem coverB_swapL (L : Finset (Lin n)) : coverB (swapL L) = coverA L := by
  ext k
  simp only [mem_coverA, mem_coverB, mem_swapL]
  exact ⟨fun ⟨p, hp, hk⟩ => ⟨swapLin p, hp, hk⟩,
    fun ⟨p, hp, hk⟩ => ⟨swapLin p, by simpa using hp, hk⟩⟩

theorem WFP.swap {s : PSt n} (hs : WFP s) : WFP (swapP s) := by
  refine ⟨wf_swapL hs.wf, hs.neB, hs.neA, hs.pdB, hs.pdA, ?_, ?_⟩
  · change Disjoint (coverA (swapL s.1)) (s.2.2.biUnion id)
    rw [coverA_swapL]
    exact hs.freshB
  · change Disjoint (coverB (swapL s.1)) (s.2.1.biUnion id)
    rw [coverB_swapL]
    exact hs.freshA

theorem stepP_swap (g : PSt n → ℝ) (s : PSt n) :
    stepP θB θA ρ g (swapP s) = stepP θA θB ρ (fun t => g (swapP t)) s := by
  have hco : ∀ p q : Lin n, coalP (swapP s) (swapLin p) (swapLin q) = swapP (coalP s p q) :=
    fun p q => congrArg (fun X => ((X, s.2.2, s.2.1) : PSt n)) (coalL_swapL s.1 p q)
  have hmA : ∀ p : Lin n, mutAP (swapP s) (swapLin p) = swapP (mutBP s p) :=
    fun p => congrArg (fun X => ((X, insert p.2 s.2.2, s.2.1) : PSt n)) (mutAL_swapL s.1 p)
  have hmB : ∀ p : Lin n, mutBP (swapP s) (swapLin p) = swapP (mutAP s p) :=
    fun p => congrArg (fun X => ((X, s.2.2, insert p.1 s.2.1) : PSt n)) (mutBL_swapL s.1 p)
  have hre : ∀ p : Lin n, recP (swapP s) (swapLin p) = swapP (recP s p) :=
    fun p => congrArg (fun X => ((X, s.2.2, s.2.1) : PSt n)) (recL_swapL s.1 p)
  have hfst : (swapP s).1 = swapL s.1 := rfl
  have e1 : (∑ p ∈ (swapP s).1, ∑ q ∈ (swapP s).1.erase p, g (coalP (swapP s) p q))
      = ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g (swapP (coalP s p q)) := by
    rw [hfst, sum_swapL]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← swapL_erase, sum_swapL]
    exact Finset.sum_congr rfl fun q _ => by rw [hco p q]
  have e2 : (∑ p ∈ carA (swapP s).1, g (mutAP (swapP s) p))
      = ∑ p ∈ carB s.1, g (swapP (mutBP s p)) := by
    rw [hfst, carA_swapL, sum_swapL]
    exact Finset.sum_congr rfl fun p _ => by rw [hmA p]
  have e3 : (∑ p ∈ carB (swapP s).1, g (mutBP (swapP s) p))
      = ∑ p ∈ carA s.1, g (swapP (mutAP s p)) := by
    rw [hfst, carB_swapL, sum_swapL]
    exact Finset.sum_congr rfl fun p _ => by rw [hmB p]
  have e4 : (∑ p ∈ carC (swapP s).1, g (recP (swapP s) p))
      = ∑ p ∈ carC s.1, g (swapP (recP s p)) := by
    rw [hfst, carC_swapL, sum_swapL]
    exact Finset.sum_congr rfl fun p _ => by rw [hre p]
  rw [stepP, stepP, e1, e2, e3, e4]
  ring

theorem hitAt_swap (s : PSt n) : hitAt ζB ζA (swapP s) = hitAt ζA ζB s := by
  rw [hitAt, hitAt]
  by_cases h : s.2.1 = ζA ∧ s.2.2 = ζB
  · rw [ite_eq_left (show (swapP s).2.1 = ζB ∧ (swapP s).2.2 = ζA from ⟨h.2, h.1⟩), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ⟨hc.2, hc.1⟩), ite_eq_right h]

theorem hitNP_swap (N : ℕ) (s : PSt n) :
    hitNP ζB ζA θB θA ρ N (swapP s) = hitNP ζA ζB θA θB ρ N s := by
  induction N generalizing s with
  | zero =>
    by_cases h : s.1 = ∅
    · have h' : (swapP s).1 = ∅ := by
        change swapL s.1 = ∅
        rw [h, swapL_empty]
      rw [hitNP_zero, hitNP_zero, ite_eq_left h', ite_eq_left h, hitAt_swap]
    · have h' : (swapP s).1 ≠ ∅ := fun hc => h (swapL_eq_empty_iff.1 hc)
      rw [hitNP_zero, hitNP_zero, ite_eq_right h', ite_eq_right h]
  | succ N ih =>
    by_cases h : s.1 = ∅
    · have h' : (swapP s).1 = ∅ := by
        rw [show (swapP s).1 = swapL s.1 from rfl, h, swapL_empty]
      rw [hitNP_of_empty _ h', hitNP_of_empty _ h, hitAt_swap]
    · have h' : (swapP s).1 ≠ ∅ := by
        rw [show (swapP s).1 = swapL s.1 from rfl]
        exact fun hc => h (swapL_eq_empty_iff.1 hc)
      rw [hitNP_succ_of_ne N h', hitNP_succ_of_ne N h, stepP_swap,
        show (swapP s).1 = swapL s.1 from rfl, dtot_swapL]
      congr 2
      exact funext fun t => ih t

@[simp] theorem swapL_fullState : swapL (fullState n) = fullState n := by
  ext p
  simp only [mem_swapL, mem_fullState]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← swapLin_swapLin p, hk]; rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

@[simp] theorem swapP_initP : swapP (initP n) = initP n := by
  rw [swapP, initP]
  simp only [swapL_fullState]

theorem esfKernel_swap (ζA ζB : Blocks n) :
    esfKernel θB θA ρ ζB ζA = esfKernel θA θB ρ ζA ζB := by
  have h : ∀ N, hitNP ζB ζA θB θA ρ N (initP n) = hitNP ζA ζB θA θB ρ N (initP n) := by
    intro N
    conv_lhs => rw [← swapP_initP (n := n)]
    exact hitNP_swap N (initP n)
  rw [esfKernel, esfKernel, PPst, PPst]
  exact congrArg iSup (funext h)

end Rhone.Coalescent.EsfPair
