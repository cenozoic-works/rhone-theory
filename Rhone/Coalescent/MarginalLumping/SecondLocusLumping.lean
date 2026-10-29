/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.MarginalLumping.Swap

/-! # The `B`-marginal lumping: Kingman's coalescent at the second locus -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ} {ρ : ℝ} {L : Finset (Lin n)} {p q : Lin n}

def partB (L : Finset (Lin n)) : Finset (Finset (Fin n)) := (carB L).image Prod.snd

theorem mem_partB {S : Finset (Fin n)} : S ∈ partB L ↔ ∃ p ∈ carB L, p.2 = S := by
  simp [partB]

theorem partB_eq_partA_swapL (L : Finset (Lin n)) : partB L = partA (swapL L) := by
  rw [partA, carA_swapL, swapL, Finset.image_image, partB]
  rfl

theorem snd_injOn (hw : WF L) : ∀ p ∈ carB L, ∀ r ∈ carB L, p.2 = r.2 → p = r := by
  intro p hp r hr hpr
  have h := fst_injOn (wf_swapL hw) (swapP p) (by rw [carA_swapL]; exact swapP_mem_swapL hp)
    (swapP r) (by rw [carA_swapL]; exact swapP_mem_swapL hr) hpr
  simpa using congrArg swapP h

theorem card_partB (hw : WF L) : (partB L).card = nb L := by
  rw [partB_eq_partA_swapL, card_partA (wf_swapL hw), na_swapL]

theorem partB_coal_both (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p) (h1 : p.2.Nonempty)
    (h2 : q.2.Nonempty) : partB (coalL L p q) = mergeP (partB L) p.2 q.2 := by
  have hq' : swapP q ∈ (swapL L).erase (swapP p) := by
    rw [← swapL_erase]
    exact swapP_mem_swapL hq
  rw [partB_eq_partA_swapL, partB_eq_partA_swapL, swapL_coalL,
    partA_coal_both (wf_swapL hw) (swapP_mem_swapL hp) hq' h1 h2]
  rfl

theorem partB_coal_deg (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p)
    (h : ¬ (p.2.Nonempty ∧ q.2.Nonempty)) : partB (coalL L p q) = partB L := by
  have hq' : swapP q ∈ (swapL L).erase (swapP p) := by
    rw [← swapL_erase]
    exact swapP_mem_swapL hq
  rw [partB_eq_partA_swapL, partB_eq_partA_swapL, swapL_coalL,
    partA_coal_not (wf_swapL hw) (swapP_mem_swapL hp) hq' h]

theorem partB_rec (hw : WF L) (hp : p ∈ carC L) : partB (recL L p) = partB L := by
  have hp' : swapP p ∈ carC (swapL L) := by
    rw [carC_swapL]
    exact swapP_mem_swapL hp
  rw [partB_eq_partA_swapL, partB_eq_partA_swapL, swapL_recL, partA_rec (wf_swapL hw) hp']

theorem card_partB_coal (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p) (h1 : p.2.Nonempty)
    (h2 : q.2.Nonempty) : (partB (coalL L p q)).card + 1 = (partB L).card := by
  have hq' : swapP q ∈ (swapL L).erase (swapP p) := by
    rw [← swapL_erase]
    exact swapP_mem_swapL hq
  rw [partB_eq_partA_swapL, partB_eq_partA_swapL, swapL_coalL]
  exact card_partA_coal (wf_swapL hw) (swapP_mem_swapL hp) hq' h1 h2

theorem kingman_generator_B (hw : WF L) (f : Finset (Finset (Fin n)) → ℝ) :
    stepArg ρ (fun M => f (partB M)) L - dtotArg ρ L * f (partB L)
      = ∑ S ∈ partB L, ∑ T ∈ (partB L).erase S,
          (f (mergeP (partB L) S T) - f (partB L)) := by
  have hs := stepArg_swapL ρ (fun M => f (partA M)) L
  have hfun : (fun M : Finset (Lin n) => f (partB M))
      = fun M : Finset (Lin n) => f (partA (swapL M)) :=
    funext fun M => by rw [partB_eq_partA_swapL]
  rw [hfun, hs, ← dtotArg_swapL ρ L, partB_eq_partA_swapL]
  exact kingman_generator (wf_swapL hw) f

end Rhone.Coalescent.MarginalLumping
