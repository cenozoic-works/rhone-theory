/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFAllocationRawMoments

/-!
# Exact second and fourth LD moments of finite multinomial haplotype sampling

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset
open scoped Matrix

/-- Source: ewens2004, sec. 3.1. -/
def momentProjection (M : ℕ) : Matrix (Fin 3) (Fin 14) ℝ :=
  let m := (M : ℝ)
  !![0, 0, 0, 0, 0, 0, 1/m^2, -1/m^3, -1/m^3, 1/m^4, 0, 0, 0, 0;
     0, 0, 0, 1/m, 0, 0, -1/m^2, 2/m^3, 2/m^3, -4/m^4, -2/m^2, -2/m^2, 4/m^3, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1/m^4, 0, 0, -2/m^3, 1/m^2]

/-- Source: ewens2004, sec. 3.1. -/
theorem count_gametes_total (M : ℕ) (hM : 0 < M) (a : AlleleCounts M 4) :
    (countGametes M a).total = 1 := by
  have hsum := a.sum_real
  norm_num [Fin.sum_univ_succ, ← add_assoc] at hsum
  unfold countGametes Dynamics.TwoLocusSelection.fromVector Dynamics.Gametes.total
  norm_num
  rw [← add_div, ← add_div, ← add_div, hsum]
  exact div_self (Nat.cast_ne_zero.mpr hM.ne')

/-- Source: ewens2004, sec. 3.1. -/
theorem moment_statistics_projection (M : ℕ) (hM : 0 < M) (a : AlleleCounts M 4) :
    momentStatistics (countGametes M a) = momentProjection M *ᵥ rawCountFeatures M a := by
  have hd := Dynamics.Gametes.D_eq_x11_sub (count_gametes_total M hM a)
  unfold momentStatistics
  rw [hd]
  ext i
  fin_cases i <;>
    norm_num [momentProjection, rawCountFeatures, rawFeatures,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, countGametes,
      Dynamics.TwoLocusSelection.fromVector, Dynamics.Gametes.pA, Dynamics.Gametes.pB] <;>
    field_simp [Nat.cast_ne_zero.mpr hM.ne'] <;> ring

/-- Source: ewens2004, sec. 3.1. -/
theorem raw_moment_projection (M : ℕ) (hM : 0 < M) (g : Dynamics.Gametes ℝ) (ht : g.total = 1) :
    momentProjection M *ᵥ rawMomentFormula M g = samplingMomentMatrix M *ᵥ momentStatistics g := by
  have hd := Dynamics.Gametes.D_eq_x11_sub ht
  ext i
  fin_cases i <;>
    norm_num [momentProjection, rawMomentFormula, samplingMomentMatrix, momentStatistics,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hd] <;>
    field_simp [Nat.cast_ne_zero.mpr hM.ne'] <;> ring

/-- Source: ewens2004, sec. 3.1. -/
theorem sampling_moment_recursion (M : ℕ) (hM : 0 < M) (g : Dynamics.Gametes ℝ)
    (hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector g i) (ht : g.total = 1) :
    (fun i => samplingExpectation M g (fun a => momentStatistics (countGametes M a) i)) =
      samplingMomentMatrix M *ᵥ momentStatistics g := by
  have _ := hg
  have halloc := allocation_raw_moments M g ht
  rw [← raw_moment_projection M hM g ht, ← halloc, Matrix.mulVec_sum]
  ext i
  rw [sampling_expectation_allocation]
  simp only [Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    ← moment_statistics_projection M hM]

end Rhone.MarkovChain.WFAllocationLD
