/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Breeders
public import Rhone.Statistics.Breeder
public import Mathlib.Basic.Real.Basic

/-!
# Executable breeder's equation equals the specification

Source: lush1943, ch. 12, p. 143; felsenstein_teg2019, eq. (IX-69), p. 443; falconer_mackay1996,
ch. 11. -/

@[expose] public section
namespace Rhone.Computation.Breeders

theorem response_eq_none_iff (VA VP S : Rat) : response VA VP S = none ↔ VP = 0 := by
  unfold response
  by_cases h : VP = 0 <;> simp [h]

theorem heritability_eq_none_iff (VA VP : Rat) : heritability VA VP = none ↔ VP = 0 := by
  unfold heritability
  by_cases h : VP = 0 <;> simp [h]

theorem response_eq {ι : Type*} [Fintype ι] (w m o : ι → ℝ) (a : ℝ) (VA VP S : Rat)
    (hVP : VP ≠ 0) (hw : Rhone.Statistics.popMean w ≠ 0)
    (hlin : ∀ i, o i = a + ((VA / VP : Rat) : ℝ) * m i)
    (hS : (S : ℝ) = Rhone.Statistics.selectionDifferential w m) :
    ∃ R : Rat, response VA VP S = some R ∧
      (R : ℝ) = Rhone.Statistics.selectionResponse w o := by
  refine ⟨VA / VP * S, by simp [response, hVP], ?_⟩
  rw [Rhone.Statistics.breeder_equation w m o a _ hw hlin, Rat.cast_mul, hS]

theorem response_eq_of_covariances {ι : Type*} [Fintype ι] [NeZero (Fintype.card ι : ℝ)]
    (w m o : ι → ℝ) (a h2 : ℝ) (VA VP S : Rat)
    (hw : Rhone.Statistics.popMean w ≠ 0) (hlin : ∀ i, o i = a + h2 * m i)
    (hVA : (VA : ℝ) = Rhone.Statistics.popCov o m) (hVP : (VP : ℝ) = Rhone.Statistics.popCov m m)
    (hv : Rhone.Statistics.popCov m m ≠ 0)
    (hS : (S : ℝ) = Rhone.Statistics.selectionDifferential w m) :
    ∃ H R : Rat, heritability VA VP = some H ∧ (H : ℝ) = h2 ∧
      response VA VP S = some R ∧ (R : ℝ) = Rhone.Statistics.selectionResponse w o := by
  have hVP0 : VP ≠ 0 := by
    intro h; apply hv; rw [← hVP, h]; simp
  have hslope : h2 = Rhone.Statistics.popCov o m / Rhone.Statistics.popCov m m :=
    Rhone.Statistics.heritability_eq_regression_slope m o a h2 hlin hv
  have hH : ((VA / VP : Rat) : ℝ) = h2 := by
    rw [Rat.cast_div, hVA, hVP, ← hslope]
  refine ⟨VA / VP, VA / VP * S, by simp [heritability, hVP0], hH,
    by simp [response, hVP0], ?_⟩
  rw [Rat.cast_mul, hH, hS]
  exact (Rhone.Statistics.breeder_equation w m o a h2 hw hlin).symm

end Rhone.Computation.Breeders
