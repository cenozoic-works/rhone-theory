/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.Observation
public import Rhone.Statistics.BinnedPanLaw.Quadrature
public import Rhone.Statistics.ThreeSiteSeparator.SortedPairMoments

/-! # Histogram moment identity with finite rational quadrature -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeSiteSeparator
    ConcretePatternMoments
variable {n : ℕ}

theorem histogram_unit_support (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) : ∀ᵐ z ∂histogram w, z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨r, _, _, _, he⟩ := exists_pan_histogram hn w hw hs
  have hc : panClockLaw 1 r = histogram w := by
    rw [panClockLaw_exp (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [neg_one_mul] using he
  rw [← hc]
  exact panClockLaw_unit_support 1 r

def momentQuadrature (w : Fin n → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | p + 1, 0 => 1 - ((p : ℝ) + 1) * cubeQuadrature w p
  | 0, q + 1 => 1 - (3 * ((q : ℝ) + 1) / 2) * weightedQuadrature w q +
      (((q : ℝ) + 1) / 2) * cubeQuadrature w q
  | p + 1, q + 1 => mixedQuadrature w (p + 1) (q + 1)

theorem histogram_moment_quadrature (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) (p q : ℕ) :
    (∫ z, z.1 ^ p * z.2 ^ q ∂sortedPairLaw (histogram w)) = momentQuadrature w p q := by
  let := histogram_probability w (fun i => (hw i).le) hs
  let := sortedPairLaw_probability (histogram w)
  have hunit := histogram_unit_support hn w hw hs
  have hcdf : (fun x => (histogram w).real (Iic x)) = histogramCDF w :=
    funext (histogram_real_Iic hn w (fun i => (hw i).le))
  have hcont : Continuous (fun x => (histogram w).real (Iic x)) := by
    rw [hcdf]
    exact (histogramCDF_lipschitz w).choose_spec.continuous
  have hcdf3 : (fun x => (histogram w).real (Iic x) ^ 3) =
      (fun x => histogramCDF w x ^ 3) := by
    funext x
    rw [histogram_real_Iic hn w (fun i => (hw i).le)]
  cases p with
  | zero =>
    cases q with
    | zero => simp [momentQuadrature]
    | succ q =>
      simp only [pow_zero, one_mul, momentQuadrature]
      rw [sortedPair_snd_moment (histogram w) hunit hcont q, hcdf, hcdf3,
        weighted_quadrature hn]
      unfold weightedPrimitive
      dsimp only
      rw [cube_quadrature hn]
  | succ p =>
    cases q with
    | zero =>
      simp only [pow_zero, mul_one, momentQuadrature]
      rw [sortedPair_fst_moment (histogram w) hunit p, hcdf3]
      unfold weightedPrimitive
      dsimp only
      rw [cube_quadrature hn]
    | succ q =>
      rw [sortedPair_mixed_moment (histogram w) hunit hcont p q, hcdf,
        mixed_quadrature hn]
      rfl

theorem histogram_table_quadrature (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) (j : Fin 19) :
    histogramMoments w j = momentQuadrature w (exponents j).1 (exponents j).2 :=
  histogram_moment_quadrature hn w hw hs _ _

end Rhone.Statistics.BinnedPanLaw
