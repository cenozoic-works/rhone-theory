/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.PartialSelfingMomentProof

/-! # Soundness and conditional completeness of the partial-selfing certificate check -/

@[expose] public section
namespace Rhone.Computation.PartialSelfing
open Dynamics.MendelianIBD

theorem check_iff (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat) :
    check d t s q p environment table moments equilibrium qKinship = true ↔
      ValidCertificate d t s q p environment table moments equilibrium qKinship := by
  simp [check]

theorem certificate_laws (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat)
    (hv : ValidCertificate d t s q p environment table moments equilibrium qKinship)
    (k : Nat) (hk : k ≤ t) (z : Diploid d) :
    dipLaw d (table.getD k #[]) z = generation s (parentLaw d q) (dipLaw d p) k z := by
  rcases hv with ⟨_hi, _heSize, he, _htSize, _hmSize, hstart, _hm, hstep, _hf, _hq⟩
  have henv : dipLaw d environment = outcross (parentLaw d q) := by
    funext x
    have h := he (x 0) (x 1)
    simpa only [pair_eta] using h
  have aux : ∀ j, j ≤ t → ∀ x : Diploid d,
      dipLaw d (table.getD j #[]) x = generation s (parentLaw d q) (dipLaw d p) j x := by
    intro j
    induction j with
    | zero =>
      intro _ x
      simp only [hstart, generation]
    | succ j ih =>
      intro hj x
      have hlt : j < t := Nat.lt_of_succ_le hj
      have hprev : dipLaw d (table.getD j #[]) =
          generation s (parentLaw d q) (dipLaw d p) j := by
        funext y
        exact ih (Nat.le_of_lt hlt) y
      have h := hstep ⟨j, hlt⟩ (x 0) (x 1)
      simpa only [pair_eta, hprev, henv, generation, step] using h
  exact aux k hk z

theorem check_law_cast (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat)
    (hv : check d t s q p environment table moments equilibrium qKinship = true)
    (k : Nat) (hk : k ≤ t) (z : Diploid d) :
    (dipLaw d (table.getD k #[]) z : Real) =
      partialSelfingGeneration (s : Real) (fun _ xy => (parentLaw d q xy : Real))
        (fun x => (dipLaw d p x : Real)) k z := by
  rw [certificate_laws d t s q p environment table moments equilibrium qKinship
    ((check_iff d t s q p environment table moments equilibrium qKinship).1 hv) k hk z]
  exact generation_cast s (parentLaw d q) (dipLaw d p) k z

theorem check_moment_cast (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat)
    (hv : check d t s q p environment table moments equilibrium qKinship = true)
    (k : Fin (t + 1)) :
    (moments.getD k 0 : Real) = founderIbd
      (partialSelfingGeneration (s : Real) (fun _ xy => (parentLaw d q xy : Real))
        (fun x => (dipLaw d p x : Real)) k) id := by
  have hc := (check_iff d t s q p environment table moments equilibrium qKinship).1 hv
  rcases hc with ⟨_hi, _heSize, _he, _htSize, _hmSize, _hstart, hm, _hstep, _hf, _hq⟩
  rw [(hm k).2, ibd_cast]
  congr 1
  funext z
  exact check_law_cast d t s q p environment table moments equilibrium qKinship
    hv k (Nat.le_of_lt_succ k.isLt) z

theorem check_of_exact (d t : Nat) (s : Rat) (q p environment : Array Rat)
    (table : Array (Array Rat)) (moments : Array Rat) (equilibrium qKinship : Rat)
    (hi : ValidInput d t s q p) (heSize : environment.size = d * d)
    (he : ∀ a b : Fin d, dipLaw d environment (pair a b) = outcross (parentLaw d q) (pair a b))
    (htSize : table.size = t + 1) (hmSize : moments.size = t + 1)
    (hstart : table.getD 0 #[] = p)
    (hlawSize : ∀ k : Fin (t + 1), (table.getD k #[]).size = d * d)
    (hlaw : ∀ k : Fin (t + 1), ∀ z : Diploid d,
      dipLaw d (table.getD k #[]) z = generation s (parentLaw d q) (dipLaw d p) k z)
    (hm : ∀ k : Fin (t + 1), moments.getD k 0 =
      ibd (generation s (parentLaw d q) (dipLaw d p) k))
    (hf : equilibrium = fixed s) (hq : qKinship = kinship (parentLaw d q)) :
    check d t s q p environment table moments equilibrium qKinship = true := by
  apply (check_iff d t s q p environment table moments equilibrium qKinship).2
  refine ⟨hi, heSize, he, htSize, hmSize, hstart, ?_, ?_, hf, hq⟩
  · intro k
    refine ⟨hlawSize k, ?_⟩
    have hfun := funext (hlaw k)
    rw [hfun]
    exact hm k
  · intro k a b
    have hk : k.val < t + 1 := Nat.lt_trans k.isLt (Nat.lt_succ_self t)
    have hkNext : k.val + 1 < t + 1 := Nat.succ_lt_succ k.isLt
    rw [hlaw ⟨k.val + 1, hkNext⟩, he a b]
    have hfun : dipLaw d (table.getD k #[]) =
        generation s (parentLaw d q) (dipLaw d p) k := funext (hlaw ⟨k.val, hk⟩)
    rw [hfun]
    rfl

end Rhone.Computation.PartialSelfing
