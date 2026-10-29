/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Lande
public import Rhone.Statistics.GeneticResponse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable Lande response equals the specification

Source: lande1979, p. 406, eq. (6)–(7a); lande_arnold1983, p. 1212, eq. 5a, 6a. -/

@[expose] public section
namespace Rhone.Computation.Lande
open Finset

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1] : Rat) : ℝ))).symm

theorem cast_sumTo (f : Nat → Rat) (n : Nat) :
    ((sumTo f n : Rat) : ℝ) = ∑ i : Fin n, ((f i.1 : Rat) : ℝ) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo, Rat.cast_add, ih, Fin.sum_univ_castSucc]
    simp

def addReal (gs : List (List Rat)) (m : Nat) : Fin gs.length → Fin m → ℝ :=
  fun γ j => ((value gs[γ.1] j.1 : Rat) : ℝ)

theorem cast_mean (f : List Rat → Rat) (gs : List (List Rat)) :
    ((mean f gs : Rat) : ℝ) =
      Rhone.Statistics.popMean (fun i : Fin gs.length => ((f gs[i.1] : Rat) : ℝ)) := by
  unfold mean Rhone.Statistics.popMean
  rw [Rat.cast_div, cast_sumBy, Rat.cast_natCast, Fintype.card_fin]

theorem cast_gEntry (gs : List (List Rat)) (m : Nat) (j k : Fin m) :
    ((gEntry gs j.1 k.1 : Rat) : ℝ) = Rhone.Statistics.geneticCovariance (addReal gs m) j k := by
  unfold gEntry Rhone.Statistics.geneticCovariance Rhone.Statistics.popCov
  rw [Rat.cast_sub, Rat.cast_mul, cast_mean, cast_mean, cast_mean]
  simp only [addReal, Rat.cast_mul]

theorem responseAt_eq (gs : List (List Rat)) (β : List Rat) (j : Fin β.length) :
    ((responseAt gs β j.1 : Rat) : ℝ) =
      ∑ k : Fin β.length, Rhone.Statistics.geneticCovariance (addReal gs β.length) j k *
        ((β.getD k.1 0 : Rat) : ℝ) := by
  unfold responseAt
  rw [cast_sumTo]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.cast_mul, cast_gEntry gs β.length j k]

theorem response_getElem (gs : List (List Rat)) (β : List Rat) :
    (response gs β).length = β.length ∧
      ∀ (j : Nat) (hj : j < (response gs β).length), (response gs β)[j] = responseAt gs β j := by
  refine ⟨by simp [response], fun j hj => ?_⟩
  simp [response]

theorem response_eq_selection {E : Type*} [Fintype E] [Nonempty E]
    (gs : List (List Rat)) (hgs : gs ≠ []) (β : List Rat)
    (e : E → Fin β.length → ℝ) (w : Fin gs.length × E → ℝ)
    (hw0 : ∀ pair, 0 ≤ w pair) (hw : 0 < Rhone.Statistics.popMean w)
    (hfit : ∀ pair, w pair / Rhone.Statistics.popMean w = 1 +
      ∑ k, ((β.getD k.1 0 : Rat) : ℝ) *
        (Rhone.Statistics.genotypeEnvironmentPhenotype (addReal gs β.length) e pair k -
          Rhone.Statistics.popMean (fun pair =>
            Rhone.Statistics.genotypeEnvironmentPhenotype (addReal gs β.length) e pair k)))
    (j : Fin β.length) :
    Rhone.Statistics.selectionResponse w (fun pair => addReal gs β.length pair.1 j) =
      ((responseAt gs β j.1 : Rat) : ℝ) := by
  have : Nonempty (Fin gs.length) :=
    ⟨⟨0, List.length_pos_iff.2 hgs⟩⟩
  rw [responseAt_eq]
  exact Rhone.Statistics.genetic_response_lande (addReal gs β.length) e w
    (fun k => ((β.getD k.1 0 : Rat) : ℝ)) hw0 hw hfit j

end Rhone.Computation.Lande
