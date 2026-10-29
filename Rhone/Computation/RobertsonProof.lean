/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Robertson
public import Rhone.Computation.PriceProof
public import Rhone.Statistics.Price
public import Mathlib.Basic.Real.Basic

/-!
# Executable Robertson-Price identity equals the specification

Source: robertson1966, p. 97, eq. (4), p. 99; frank1995_price, p. 374, eq. (1); price1970, p. 520,
eq. (1). -/

@[expose] public section
namespace Rhone.Computation.Robertson
open Price

theorem robertsonChange_eq_none_iff (l : List Parent) :
    robertsonChange l = none ↔ mean (fun p => p.w) l = 0 := by
  unfold robertsonChange
  by_cases h : mean (fun p => p.w) l = 0 <;> simp [h]

theorem robertsonChange_eq (l : List Parent) (hw : mean (fun p => p.w) l ≠ 0)
    (hf : ∀ p ∈ l, p.z' = p.z) :
    ∃ q : Rat, robertsonChange l = some q ∧
      (q : ℝ) = Rhone.Statistics.popCov (wReal l) (zReal l) / Rhone.Statistics.popMean (wReal l) ∧
      (q : ℝ) = Rhone.Statistics.nextMean (wReal l) (zNextReal l) - Rhone.Statistics.popMean
          (zReal l) := by
  refine ⟨cov (fun p => p.w) (fun p => p.z) l / mean (fun p => p.w) l,
    by simp [robertsonChange, hw], ?_⟩
  have hw' : Rhone.Statistics.popMean (wReal l) ≠ 0 := by
    rw [← cast_meanW]; exact_mod_cast hw
  have hz : zNextReal l = zReal l := by
    funext i
    simp only [zNextReal, zReal]
    rw [hf _ (List.getElem_mem i.2)]
  have h1 : (((cov (fun p => p.w) (fun p => p.z) l / mean (fun p => p.w) l : Rat)) : ℝ) =
      Rhone.Statistics.popCov (wReal l) (zReal l) / Rhone.Statistics.popMean (wReal l) := by
    rw [Rat.cast_div, ← cast_meanW]
    exact congrArg (· / _) (cast_selectionTerm l)
  refine ⟨h1, ?_⟩
  rw [h1, hz]
  exact (Rhone.Statistics.robertson_price (wReal l) (zReal l) hw').symm

theorem robertsonChange_eq_deltaMean (l : List Parent) (hf : ∀ p ∈ l, p.z' = p.z) :
    robertsonChange l = deltaMean l := by
  by_cases hw : mean (fun p => p.w) l = 0
  · simp [robertsonChange, deltaMean, hw]
  · obtain ⟨q, hq, hq1, hq2⟩ := robertsonChange_eq l hw hf
    obtain ⟨r, hr, hr1⟩ := deltaMean_eq l hw
    have : q = r := by
      have : (q : ℝ) = (r : ℝ) := by rw [hq2, hr1]
      exact_mod_cast this
    rw [hq, hr, this]

end Rhone.Computation.Robertson
