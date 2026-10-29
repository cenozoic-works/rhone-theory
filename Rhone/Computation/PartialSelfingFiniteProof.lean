/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.PartialSelfing
public import Rhone.Computation.AbsorptionCoreProof
public import Rhone.Dynamics.PartialSelfingLaw
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Equality of the rational partial-selfing definitions with the real founder-copy law -/

@[expose] public section
namespace Rhone.Computation.PartialSelfing
open Finset Dynamics.MendelianIBD

theorem sumFin_cast (n : Nat) (f : Fin n → Rat) :
    (sumFin n f : Real) = ∑ i : Fin n, (f i : Real) := by
  rw [sumFin, Absorption.sum_cast]
  calc
    _ = ∑ i : Fin n, ((if h : i.val < n then f ⟨i.val, h⟩ else 0 : Rat) : Real) :=
      (Fin.sum_univ_eq_sum_range (fun i : Nat =>
        ((if h : i < n then f ⟨i, h⟩ else 0 : Rat) : Real)) n).symm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp [i.isLt]

theorem pair_eta {d : Nat} (x : Diploid d) : pair (x 0) (x 1) = x := by
  funext i
  fin_cases i <;> simp [pair]

theorem sumDip_cast (d : Nat) (f : Diploid d → Rat) :
    (sumDip d f : Real) = ∑ x : Diploid d, (f x : Real) := by
  rw [sumDip, sumFin_cast]
  simp_rw [sumFin_cast]
  let e : (Fin d × Fin d) ≃ Diploid d := (finTwoArrowEquiv (Fin d)).symm
  have he (xy : Fin d × Fin d) : e xy = pair xy.1 xy.2 := by
    funext i
    fin_cases i <;> simp [e, finTwoArrowEquiv, pair]
  have h := e.sum_comp (fun x => (f x : Real))
  rw [Fintype.sum_prod_type] at h
  simpa only [he] using h

theorem sumParents_cast (d : Nat) (f : Diploid d × Diploid d → Rat) :
    (sumParents d f : Real) = ∑ xy : Diploid d × Diploid d, (f xy : Real) := by
  simp only [sumParents, sumDip_cast, Fintype.sum_prod_type]

private theorem child_eq_iff {d : Nat} (x y z : Diploid d) (i j : Fin 2) :
    mendelianChild x y i j = z ↔ x i = z 0 ∧ y j = z 1 := by
  constructor
  · intro h
    exact ⟨by simpa [mendelianChild] using congrFun h 0,
      by simpa [mendelianChild] using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext k
    fin_cases k <;> simp [mendelianChild, h0, h1]

theorem transmission_cast {d : Nat} (w : Rat) (x y z : Diploid d) :
    (transmission w x y z : Real) = ∑ i : Fin 2, ∑ j : Fin 2,
      if mendelianChild x y i j = z then (w : Real) / 4 else 0 := by
  simp only [transmission, sumFin_cast]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp only [child_eq_iff]
  split_ifs <;> simp

theorem selfed_cast {d : Nat} (p : Diploid d → Rat) (z : Diploid d) :
    (selfed p z : Real) = selfingLaw (fun x => (p x : Real)) z := by
  simp only [selfed, sumDip_cast, transmission_cast, selfingLaw, mendelianLaw,
    offspringPushforwardMass, Fintype.sum_prod_type, id_eq]

theorem outcross_cast {d : Nat} (q : Diploid d × Diploid d → Rat) (z : Diploid d) :
    (outcross q z : Real) = mendelianLaw (fun xy => (q xy : Real)) Prod.fst Prod.snd z := by
  simp only [outcross, sumParents_cast, transmission_cast, mendelianLaw,
    offspringPushforwardMass, Fintype.sum_prod_type]

theorem step_cast {d : Nat} (s : Rat) (q : Diploid d × Diploid d → Rat)
    (p : Diploid d → Rat) (z : Diploid d) :
    (step s q p z : Real) = partialSelfingLaw (s : Real)
      (fun xy => (q xy : Real)) (fun x => (p x : Real)) z := by
  simp only [step, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    selfed_cast, outcross_cast, partialSelfingLaw]

theorem generation_cast {d : Nat} (s : Rat) (q : Diploid d × Diploid d → Rat)
    (p : Diploid d → Rat) (t : Nat) (z : Diploid d) :
    (generation s q p t z : Real) = partialSelfingGeneration (s : Real)
      (fun _ xy => (q xy : Real)) (fun x => (p x : Real)) t z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    rw [generation, step_cast, partialSelfingGeneration]
    have he : (fun x => (generation s q p t x : Real)) =
        partialSelfingGeneration (s : Real) (fun _ xy => (q xy : Real))
          (fun x => (p x : Real)) t := by
      funext x
      exact ih x
    rw [he]

end Rhone.Computation.PartialSelfing
