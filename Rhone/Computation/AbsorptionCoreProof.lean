/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Absorption
public import Rhone.Computation.DriftProof
public import Rhone.MarkovChain.HittingTime

/-! # Checked first-step tables equal the mathematical absorption expectations -/

@[expose] public section
namespace Rhone.Computation.Absorption
open Finset MarkovChain

theorem sum_cast (f : Nat → Rat) (k : Nat) :
    (sum f k : Real) = ∑ j ∈ range k, (f j : Real) := by
  induction k with
  | zero => simp [sum]
  | succ k ih => simp [sum, ih, sum_range_succ]

theorem check_iff (n : Nat) (row : Nat → Nat → Rat) (table : Array Rat) :
    check n row table = true ↔ ValidTable n row table := by
  simp [check]

private theorem boundary_iff (n : Nat) (i : Fin (n + 1)) :
    i.val = 0 ∨ i.val = n ↔ i ∈ fixationBoundary n := by
  rw [mem_fixationBoundary]
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext (by simpa only [Fin.val_zero] using h))
    · exact Or.inr (Fin.ext (by simpa only [Fin.val_last] using h))
  · rintro (rfl | rfl)
    · exact Or.inl (by simp only [Fin.val_zero])
    · exact Or.inr (by simp only [Fin.val_last])

theorem check_iff_absorbTime (n : Nat) (row : Nat → Nat → Rat)
    (C : FinChain (Fin (n + 1)))
    (hP : ∀ i j : Fin (n + 1), (row i j : Real) = C.P i j)
    (hA : C.IsAbsorbingSet (fixationBoundary n))
    (hR : C.Reaches (fixationBoundary n)) (table : Array Rat) :
    check n row table = true ↔ table.size = n + 1 ∧
      ∀ i : Fin (n + 1), (table.getD i 0 : Real) = C.absorbTime (fixationBoundary n) i := by
  have hsum (i : Fin (n + 1)) :
      (sum (fun j => row i j * table.getD j 0) (n + 1) : Real) =
        ∑ j : Fin (n + 1), C.P i j * (table.getD j 0 : Real) := by
    rw [sum_cast]
    calc
      _ = ∑ j : Fin (n + 1), ((row i j * table.getD j 0 : Rat) : Real) :=
        (Fin.sum_univ_eq_sum_range (fun j : Nat =>
          ((row i j * table.getD j 0 : Rat) : Real)) (n + 1)).symm
      _ = _ := by
        apply sum_congr rfl
        intro j _
        simp only [Rat.cast_mul, hP i j]
  rw [check_iff]
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    have he : (fun i : Fin (n + 1) => (table.getD i 0 : Real)) =
        C.absorbTime (fixationBoundary n) := by
      apply FinChain.eq_absorbTime_of_step hA hR
      · intro i hi
        have hb := (boundary_iff n i).2 hi
        have hz := ht.2 i
        rw [ite_eq_left hb] at hz
        exact_mod_cast hz
      · intro i hi
        have hb : ¬(i.val = 0 ∨ i.val = n) := fun hb => hi ((boundary_iff n i).1 hb)
        have hs := ht.2 i
        rw [ite_eq_right hb] at hs
        have hc := congrArg (fun x : Rat => (x : Real)) hs
        simpa only [Rat.cast_add, Rat.cast_one, hsum] using hc
    intro i
    exact congrFun he i
  · rintro ⟨hlen, he⟩
    refine ⟨hlen, fun i => ?_⟩
    by_cases hb : i.val = 0 ∨ i.val = n
    · rw [ite_eq_left hb]
      have hz := C.absorbTime_of_mem hA ((boundary_iff n i).1 hb)
      have hc : (table.getD i 0 : Real) = 0 := (he i).trans hz
      exact_mod_cast hc
    · rw [ite_eq_right hb]
      have hi : i ∉ fixationBoundary n := fun hi => hb ((boundary_iff n i).2 hi)
      have hs := C.absorbTime_step hA hR hi
      rw [← he i] at hs
      simp only [← he] at hs
      have hc : (table.getD i 0 : Real) =
          ((1 + sum (fun j => row i j * table.getD j 0) (n + 1) : Rat) : Real) := by
        simpa only [Rat.cast_add, Rat.cast_one, hsum] using hs
      exact_mod_cast hc

end Rhone.Computation.Absorption
