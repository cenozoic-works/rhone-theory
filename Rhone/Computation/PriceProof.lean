/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Price
public import Rhone.Statistics.Price
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Executable Price equation equals the specification

Source: price1970, p. 520, eq. (4); frank1995_price, p. 376, eq. (3). -/

@[expose] public section
namespace Rhone.Computation.Price
open Finset

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1] : Rat) : ℝ))).symm

def wReal (l : List Parent) : Fin l.length → ℝ := fun i => ((l[i.1]).w : ℝ)

def zReal (l : List Parent) : Fin l.length → ℝ := fun i => ((l[i.1]).z : ℝ)

def zNextReal (l : List Parent) : Fin l.length → ℝ := fun i => ((l[i.1]).z' : ℝ)

theorem cast_mean (f : Parent → Rat) (l : List Parent) :
    ((mean f l : Rat) : ℝ) =
      Rhone.Statistics.popMean (fun i : Fin l.length => ((f l[i.1] : Rat) : ℝ)) := by
  unfold mean Rhone.Statistics.popMean
  rw [Rat.cast_div, cast_sumBy, Rat.cast_natCast, Fintype.card_fin]

theorem cast_meanW (l : List Parent) :
    ((mean (fun p => p.w) l : Rat) : ℝ) = Rhone.Statistics.popMean (wReal l) :=
  cast_mean _ l

theorem cast_meanTrait (l : List Parent) :
    ((meanTrait l : Rat) : ℝ) = Rhone.Statistics.popMean (zReal l) :=
  cast_mean _ l

theorem cast_selectionTerm (l : List Parent) :
    ((selectionTerm l : Rat) : ℝ) = Rhone.Statistics.popCov (wReal l) (zReal l) := by
  unfold selectionTerm cov Rhone.Statistics.popCov
  rw [Rat.cast_sub, Rat.cast_mul, cast_mean, cast_mean, cast_mean]
  simp [wReal, zReal]
  rfl

theorem cast_transmissionTerm (l : List Parent) :
    ((transmissionTerm l : Rat) : ℝ) =
      Rhone.Statistics.popMean (fun i => wReal l i * (zNextReal l i - zReal l i)) := by
  unfold transmissionTerm
  rw [cast_mean]
  simp [wReal, zReal, zNextReal]

theorem cast_nextMean (l : List Parent) :
    ((nextMean l : Rat) : ℝ) = Rhone.Statistics.nextMean (wReal l) (zNextReal l) := by
  unfold nextMean Rhone.Statistics.nextMean
  rw [Rat.cast_div, cast_mean, cast_mean]
  simp [wReal, zNextReal]
  rfl

theorem deltaMean_eq_none_iff (l : List Parent) :
    deltaMean l = none ↔ mean (fun p => p.w) l = 0 := by
  unfold deltaMean
  by_cases h : mean (fun p => p.w) l = 0 <;> simp [h]

theorem deltaMean_eq (l : List Parent) (hw : mean (fun p => p.w) l ≠ 0) :
    ∃ q : Rat, deltaMean l = some q ∧
      (q : ℝ) = Rhone.Statistics.nextMean (wReal l) (zNextReal l) - Rhone.Statistics.popMean
          (zReal l) := by
  refine ⟨nextMean l - meanTrait l, by simp [deltaMean, hw], ?_⟩
  rw [Rat.cast_sub, cast_nextMean, cast_meanTrait]

theorem price_equation_exec (l : List Parent) (hw : mean (fun p => p.w) l ≠ 0) :
    ∃ q : Rat, deltaMean l = some q ∧
      (q : ℝ) = Rhone.Statistics.nextMean (wReal l) (zNextReal l) - Rhone.Statistics.popMean
          (zReal l) ∧
      Rhone.Statistics.popMean (wReal l) * (q : ℝ) =
        Rhone.Statistics.popCov (wReal l) (zReal l) +
          Rhone.Statistics.popMean (fun i => wReal l i * (zNextReal l i - zReal l i)) := by
  obtain ⟨q, hq, hqe⟩ := deltaMean_eq l hw
  refine ⟨q, hq, hqe, ?_⟩
  have hw' : Rhone.Statistics.popMean (wReal l) ≠ 0 := by
    rw [← cast_meanW]; exact_mod_cast hw
  rw [hqe]
  exact Rhone.Statistics.price_equation (wReal l) (zReal l) (zNextReal l) hw'

theorem deltaMeanPrice_eq_deltaMean (l : List Parent) : deltaMeanPrice l = deltaMean l := by
  by_cases hw : mean (fun p => p.w) l = 0
  · simp [deltaMeanPrice, deltaMean, hw]
  · obtain ⟨q, hq, hqe, hp⟩ := price_equation_exec l hw
    have hw' : ((mean (fun p => p.w) l : Rat) : ℝ) ≠ 0 := by exact_mod_cast hw
    have hcast : (((selectionTerm l + transmissionTerm l) / mean (fun p => p.w) l : Rat) : ℝ)
        = (q : ℝ) := by
      rw [Rat.cast_div, Rat.cast_add, cast_selectionTerm, cast_transmissionTerm, cast_meanW]
      rw [cast_meanW] at hw'
      field_simp
      linarith
    have heq : (selectionTerm l + transmissionTerm l) / mean (fun p => p.w) l = q := by
      exact_mod_cast hcast
    simp [deltaMeanPrice, hw, hq, heq]

end Rhone.Computation.Price
