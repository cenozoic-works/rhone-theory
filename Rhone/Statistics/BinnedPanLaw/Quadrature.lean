/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.PolynomialIntegrals
public import Rhone.Statistics.ThreeSiteSeparator.CDFMoments

/-! # Finite exact quadrature for the CDF moment formula -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw
open ThreeSiteSeparator
variable {n : ℕ}

def primitiveConstant (w : Fin n → ℝ) (q : ℕ) (i : Fin n) : ℝ :=
  prefixPrimitive w q i.val - binIntercept w i / (q + 1) * ((i : ℝ) / n) ^ (q + 1) -
    binSlope w i / (q + 2) * ((i : ℝ) / n) ^ (q + 2)

theorem weighted_primitive_polynomial (hn : 0 < n) (w : Fin n → ℝ) (q : ℕ) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :
    weightedPrimitive q (histogramCDF w) x = primitiveConstant w q i +
      binIntercept w i / (q + 1) * x ^ (q + 1) +
      binSlope w i / (q + 2) * x ^ (q + 2) := by
  rw [weighted_primitive_piece hn w q i hx]
  unfold cellPrimitive powerIntegral primitiveConstant
  push_cast
  ring

def weightedQuadrature (w : Fin n → ℝ) (p : ℕ) : ℝ :=
  ∑ i, cellPrimitive w p i (((i : ℝ) + 1) / n)

def cubeQuadrature (w : Fin n → ℝ) (p : ℕ) : ℝ :=
  ∑ i, cubeIntegral p (binIntercept w i) (binSlope w i)
    ((i : ℝ) / n) (((i : ℝ) + 1) / n)

def crossQuadrature (w : Fin n → ℝ) (p q : ℕ) : ℝ :=
  ∑ i, crossIntegral p q (binIntercept w i) (binSlope w i) (primitiveConstant w q i)
    ((i : ℝ) / n) (((i : ℝ) + 1) / n)

theorem weighted_quadrature (hn : 0 < n) (w : Fin n → ℝ) (p : ℕ) :
    weightedPrimitive p (histogramCDF w) 1 = weightedQuadrature w p := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := prefix_primitive_integral hn w p n le_rfl
  simpa only [div_self hn', prefixPrimitive, Finset.filter_true_of_mem
    (fun (i : Fin n) _ => i.isLt), weightedPrimitive, weightedQuadrature] using h

theorem cube_quadrature (hn : 0 < n) (w : Fin n → ℝ) (p : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ p * histogramCDF w x ^ 3) = cubeQuadrature w p := by
  have hF := (histogramCDF_lipschitz w).choose_spec.continuous
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Continuous (fun x : ℝ => x ^ p * histogramCDF w x ^ 3) := by fun_prop
  rw [integral_grid_sum hn _ hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← cube_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hab : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hn'.le
  rw [uIcc_of_le hab] at hx
  dsimp only
  rw [histogramCDF_piece hn w i hx]

theorem cross_quadrature (hn : 0 < n) (w : Fin n → ℝ) (p q : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ p * histogramCDF w x ^ 2 *
      weightedPrimitive q (histogramCDF w) x) = crossQuadrature w p q := by
  have hF := (histogramCDF_lipschitz w).choose_spec.continuous
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Continuous (fun x => x ^ p * histogramCDF w x ^ 2 *
      weightedPrimitive q (histogramCDF w) x) := by fun_prop
  rw [integral_grid_sum hn _ hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← cross_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hab : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hn'.le
  rw [uIcc_of_le hab] at hx
  dsimp only
  rw [weighted_primitive_polynomial hn w q i hx, histogramCDF_piece hn w i hx]

def mixedQuadrature (w : Fin n → ℝ) (p q : ℕ) : ℝ :=
  1 - (3 * q / 2) * weightedQuadrature w (q - 1) +
    ((q : ℝ) / 2 - p) * cubeQuadrature w (p + q - 1) +
    (3 * (p : ℝ) * q / 2) * crossQuadrature w (p - 1) (q - 1)

theorem mixed_quadrature (hn : 0 < n) (w : Fin n → ℝ) (p q : ℕ) :
    cdfMixedMoment p q (histogramCDF w) = mixedQuadrature w p q := by
  unfold cdfMixedMoment mixedQuadrature
  rw [weighted_quadrature hn, cube_quadrature hn, cross_quadrature hn]

end Rhone.Statistics.BinnedPanLaw
