/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Selection
public import Rhone.Dynamics.MultiAlleleSelection
public import Rhone.Dynamics.HeterozygoteAdvantageConvergence
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable selection recursion equals the specification

Source: crow_kimura1970, sec. 6.2. -/

@[expose] public section
namespace Rhone.Computation.Selection
open Finset

theorem cast_sumRange (f : Nat → Rat) (n : Nat) :
    ((sumRange f n : Rat) : ℝ) = ∑ i ∈ range n, ((f i : Rat) : ℝ) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Rat.cast_add, ih, Finset.sum_range_succ]

theorem marginalFit_eq (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) (i : Fin K) :
    ((marginalFit K W p i.val : Rat) : ℝ) =
      Rhone.Dynamics.marginalFit (fun a b : Fin K => ((W a.val b.val : Rat) : ℝ))
        (fun a : Fin K => ((p a.val : Rat) : ℝ)) i := by
  unfold marginalFit Rhone.Dynamics.marginalFit
  rw [cast_sumRange, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem multiMeanFit_eq (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) :
    ((multiMeanFit K W p : Rat) : ℝ) =
      Rhone.Dynamics.multiMeanFit (fun a b : Fin K => ((W a.val b.val : Rat) : ℝ))
        (fun a : Fin K => ((p a.val : Rat) : ℝ)) := by
  unfold multiMeanFit Rhone.Dynamics.multiMeanFit
  rw [cast_sumRange, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Rat.cast_mul, marginalFit_eq]

theorem multiSelStep_eq (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) (i : Fin K) :
    ((multiSelStep K W p i.val : Rat) : ℝ) =
      Rhone.Dynamics.multiSelStep (fun a b : Fin K => ((W a.val b.val : Rat) : ℝ))
        (fun a : Fin K => ((p a.val : Rat) : ℝ)) i := by
  unfold multiSelStep Rhone.Dynamics.multiSelStep
  rw [Rat.cast_div, Rat.cast_mul, marginalFit_eq, multiMeanFit_eq]

theorem meanFit_eq (w11 w12 w22 p : Rat) :
    ((meanFit w11 w12 w22 p : Rat) : ℝ) =
      Rhone.Dynamics.meanFit (w11 : ℝ) (w12 : ℝ) (w22 : ℝ) (p : ℝ) := by
  unfold meanFit Rhone.Dynamics.meanFit
  push_cast
  rfl

theorem selStep_eq (w11 w12 w22 p : Rat) :
    ((selStep w11 w12 w22 p : Rat) : ℝ) =
      Rhone.Dynamics.selStep (w11 : ℝ) (w12 : ℝ) (w22 : ℝ) (p : ℝ) := by
  unfold selStep Rhone.Dynamics.selStep
  rw [Rat.cast_div, meanFit_eq]
  push_cast
  rfl

theorem multiSelStep_two (w11 w12 w22 p : Rat) :
    multiSelStep 2 (fun a b => if a = 0 then (if b = 0 then w11 else w12)
        else (if b = 0 then w12 else w22)) (fun a => if a = 0 then p else 1 - p) 0 =
      selStep w11 w12 w22 p := by
  simp only [multiSelStep, marginalFit, multiMeanFit, sumRange, selStep, meanFit]
  simp
  congr 1 <;> ring

theorem polyEq_eq (w11 w12 w22 : Rat) :
    ((polyEq w11 w12 w22 : Rat) : ℝ) =
      Rhone.Dynamics.polyEq (w11 : ℝ) (w12 : ℝ) (w22 : ℝ) := by
  unfold polyEq Rhone.Dynamics.polyEq
  push_cast
  rfl

theorem selOrbit_eq (w11 w12 w22 p0 : Rat) (t : Nat) :
    ((selOrbit w11 w12 w22 p0 t : Rat) : ℝ) =
      Rhone.Dynamics.selOrbit (w11 : ℝ) (w12 : ℝ) (w22 : ℝ) (p0 : ℝ) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [selOrbit, selStep_eq, ih, Rhone.Dynamics.selOrbit_succ]

theorem interiorEquilibriumExists_iff (w11 w12 w22 : Rat) :
    interiorEquilibriumExists w11 w12 w22 = true ↔
      (0 < polyEq w11 w12 w22 ∧ polyEq w11 w12 w22 < 1) := by
  have h := Rhone.Dynamics.polyEq_mem_Ioo_iff w11 w12 w22
  unfold interiorEquilibriumExists
  rw [decide_eq_true_iff]
  exact h.symm

theorem selOrbit_overdominance_geometric (w11 w12 w22 p0 : Rat) (h11 : 0 ≤ w11)
    (h22 : 0 ≤ w22) (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t : Nat,
      |((selOrbit w11 w12 w22 p0 t : Rat) : ℝ) - ((polyEq w11 w12 w22 : Rat) : ℝ)| ≤
        c ^ t * |(p0 : ℝ) - ((polyEq w11 w12 w22 : Rat) : ℝ)| := by
  have ho' : (w11 : ℝ) < w12 ∧ (w22 : ℝ) < w12 := ⟨by exact_mod_cast ho.1, by exact_mod_cast ho.2⟩
  obtain ⟨c, hc0, hc1, h⟩ := Rhone.Dynamics.overdominance_orbit_geometric
    (w11 := (w11 : ℝ)) (w12 := (w12 : ℝ)) (w22 := (w22 : ℝ)) (p0 := (p0 : ℝ))
    (by exact_mod_cast h11) (by exact_mod_cast h22) ho' (by exact_mod_cast hp0)
    (by exact_mod_cast hp1)
  refine ⟨c, hc0, hc1, fun t => ?_⟩
  rw [selOrbit_eq, polyEq_eq]
  exact h t

end Rhone.Computation.Selection
