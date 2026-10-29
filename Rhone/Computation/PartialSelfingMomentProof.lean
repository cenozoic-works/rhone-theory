/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.PartialSelfingFiniteProof

/-! # Identity-by-descent and kinship moments of the rational partial-selfing laws -/

@[expose] public section
namespace Rhone.Computation.PartialSelfing
open Finset Dynamics.MendelianIBD

private theorem cast_ite (p : Prop) [Decidable p] (a b : Rat) :
    ((if p then a else b : Rat) : Real) = if p then (a : Real) else (b : Real) := by
  split_ifs <;> rfl

theorem ibd_cast {d : Nat} (p : Diploid d → Rat) :
    (ibd p : Real) = founderIbd (fun x => (p x : Real)) id := by
  simp [ibd, sumDip_cast, founderIbd, cast_ite]

theorem kinship_cast {d : Nat} (q : Diploid d × Diploid d → Rat) :
    (kinship q : Real) = founderKinship (fun xy => (q xy : Real)) Prod.fst Prod.snd := by
  simp [kinship, sumParents_cast, sumFin_cast, founderKinship, cast_ite]

theorem input_real (d t : Nat) (s : Rat) (q p : Array Rat)
    (hv : ValidInput d t s q p) :
    0 ≤ (s : Real) ∧ (s : Real) ≤ 1 ∧
    (∀ x : Diploid d, 0 ≤ (dipLaw d p x : Real)) ∧
    (∑ x : Diploid d, (dipLaw d p x : Real)) = 1 ∧
    (∀ xy : Diploid d × Diploid d, 0 ≤ (parentLaw d q xy : Real)) ∧
    (∑ xy : Diploid d × Diploid d, (parentLaw d q xy : Real)) = 1 ∧
    founderKinship (fun xy => (parentLaw d q xy : Real)) Prod.fst Prod.snd = 0 := by
  rcases hv with ⟨_hd0, _hd8, _ht, hs0, hs1, _hpSize, _hqSize, hp0, hq0, hp, hq, hk⟩
  refine ⟨by exact_mod_cast hs0, by exact_mod_cast hs1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := hp0 (x 0) (x 1)
    rw [pair_eta] at h
    exact_mod_cast h
  · have h := congrArg (fun r : Rat => (r : Real)) hp
    simpa only [sumDip_cast, Rat.cast_one] using h
  · intro xy
    have h := hq0 (xy.1 0) (xy.1 1) (xy.2 0) (xy.2 1)
    simp only [pair_eta] at h
    exact_mod_cast h
  · have h := congrArg (fun r : Rat => (r : Real)) hq
    simpa only [sumParents_cast, Rat.cast_one] using h
  · have h := congrArg (fun r : Rat => (r : Real)) hk
    simpa only [kinship_cast, Rat.cast_zero] using h

theorem generation_ibd_formula (d t : Nat) (s : Rat) (q p : Array Rat)
    (hv : ValidInput d t s q p) (k : Nat) :
    (ibd (generation s (parentLaw d q) (dipLaw d p) k) : Real) =
      (s : Real) / (2 - (s : Real)) + ((s : Real) / 2) ^ k *
        ((ibd (dipLaw d p) : Real) - (s : Real) / (2 - (s : Real))) := by
  rcases input_real d t s q p hv with ⟨hs0, hs1, hp0, hp, hq0, hq, hk⟩
  rw [ibd_cast]
  have he : (fun x => (generation s (parentLaw d q) (dipLaw d p) k x : Real)) =
      partialSelfingGeneration (s : Real) (fun _ xy => (parentLaw d q xy : Real))
        (fun x => (dipLaw d p x : Real)) k := by
    funext x
    exact generation_cast s (parentLaw d q) (dipLaw d p) k x
  rw [he]
  have h := partial_selfing_generation_ibd (s : Real)
    (fun _ xy => (parentLaw d q xy : Real)) (fun x => (dipLaw d p x : Real))
    hs0 hs1 hp0 hp (fun _ => hq0) (fun _ => hq) (fun _ => hk) k
  rw [← ibd_cast] at h
  simpa only [Rhone.Dynamics.Inbreeding.partialSelfingFixed] using h

end Rhone.Computation.PartialSelfing
