/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.WeirCockerham
public import Rhone.Statistics.WeirCockerhamHaploid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable Weir-Cockerham components equal the specification

Source: weir_cockerham1984, pp. 1362–1363. -/

@[expose] public section
namespace Rhone.Computation.WeirCockerham
open Finset

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1] : Rat) : ℝ))).symm

def nOf (s : List (Nat × Nat)) : Fin s.length → ℕ := fun i => (s[i.1]).1

def xOf (s : List (Nat × Nat)) : Fin s.length → ℕ := fun i => (s[i.1]).2

theorem totalN_eq (s : List (Nat × Nat)) :
    ((totalN s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.totalN (nOf s) := by
  unfold totalN Rhone.Statistics.WeirCockerham.totalN
  rw [cast_sumBy]
  simp [nOf]

theorem sumSqN_eq (s : List (Nat × Nat)) :
    ((sumSqN s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.sumSqN (nOf s) := by
  unfold sumSqN Rhone.Statistics.WeirCockerham.sumSqN
  rw [cast_sumBy]
  simp only [nOf, Rat.cast_pow, Rat.cast_natCast]

theorem popCount_eq (s : List (Nat × Nat)) : ((popCount s : Rat) : ℝ) = (s.length : ℝ) := by
  simp [popCount]

theorem ncBar_eq (s : List (Nat × Nat)) :
    ((ncBar s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.ncBar (nOf s) := by
  unfold ncBar Rhone.Statistics.WeirCockerham.ncBar
  push_cast
  rw [totalN_eq, sumSqN_eq, popCount_eq]

theorem pBar_eq (s : List (Nat × Nat)) :
    ((pBar s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.pBar (nOf s) (xOf s) := by
  unfold pBar Rhone.Statistics.WeirCockerham.pBar
  rw [Rat.cast_div, totalN_eq, cast_sumBy]
  simp [xOf]

theorem msp_eq (s : List (Nat × Nat)) :
    ((msp s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.msp (nOf s) (xOf s) := by
  unfold msp Rhone.Statistics.WeirCockerham.msp
  rw [Rat.cast_div, cast_sumBy, Rat.cast_sub, popCount_eq]
  simp only [nOf, xOf, Rat.cast_pow, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_one, pBar_eq]

theorem msg_eq (s : List (Nat × Nat)) :
    ((msg s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.msg (nOf s) (xOf s) := by
  unfold msg Rhone.Statistics.WeirCockerham.msg
  rw [Rat.cast_div, cast_sumBy, Rat.cast_sub, totalN_eq, popCount_eq]
  simp [nOf, xOf]

theorem wcA_eq (s : List (Nat × Nat)) :
    ((wcA s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.wcA (nOf s) (xOf s) := by
  unfold wcA Rhone.Statistics.WeirCockerham.wcA
  rw [Rat.cast_div, Rat.cast_sub, msp_eq, msg_eq, ncBar_eq]

theorem wcB_eq (s : List (Nat × Nat)) :
    ((wcB s : Rat) : ℝ) = Rhone.Statistics.WeirCockerham.wcB (nOf s) (xOf s) := by
  unfold wcB Rhone.Statistics.WeirCockerham.wcB
  exact msg_eq s

theorem wcTotal_eq (s : List (Nat × Nat)) :
    ((wcTotal s : Rat) : ℝ) =
      Rhone.Statistics.WeirCockerham.wcA (nOf s) (xOf s) +
        Rhone.Statistics.WeirCockerham.wcB (nOf s) (xOf s) := by
  unfold wcTotal
  rw [Rat.cast_add, wcA_eq, wcB_eq]

end Rhone.Computation.WeirCockerham
