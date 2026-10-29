/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SelectionGradient
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!
# Inverse covariance formulas for the declared finite regression model

Source: lande_arnold1983, pp. 1212–1213. -/
@[expose] public section
namespace Rhone.Statistics
open Finset
/-- Source: lande_arnold1983, pp. 1212–1213. -/
noncomputable def offspringCrossCovariance {ι κ η : Type*} [Fintype ι]
    (m : ι → κ → ℝ) (o : ι → η → ℝ) (j : η) (k : κ) : ℝ :=
  popCov (fun i => o i j) (fun i => m i k)

private theorem mean_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    popMean (fun i => c * f i) = c * popMean f := by
  simp only [popMean, ← Finset.mul_sum]
  ring

private theorem mean_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : κ → ι → ℝ) :
    popMean (fun i => ∑ k, f k i) = ∑ k, popMean (f k) := by
  simp only [popMean, Finset.sum_div]
  rw [Finset.sum_comm]

private theorem cov_affine {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ι → ℝ) (c : ℝ) (b : κ → ℝ) :
    popCov f (fun i => c + ∑ k, b k * g k i) = ∑ k, b k * popCov f (g k) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hconst : popMean (fun _ : ι => c) = c := by simp [popMean, hc]
  simp only [popCov, mul_add, popMean_add, mean_sum]
  rw [hconst]
  have hprod : (fun i => f i * c) = (fun i => c * f i) := by funext i; ring
  rw [hprod, mean_mul]
  have hsum : (fun i => f i * ∑ k, b k * g k i) =
      (fun i => ∑ k, b k * (f i * g k i)) := by
    funext i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, mean_sum]
  simp only [mean_mul, Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem selection_gradient_matrix_inverse
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (β : κ → ℝ)
    (hw : popMean w ≠ 0)
    (horth : ∀ j, popCov (fun i => z i j) (selectionResidual w z β) = 0)
    (hdet : Matrix.det (phenotypeCovariance z) ≠ 0) :
    β = Matrix.mulVec (phenotypeCovariance z : Matrix κ κ ℝ)⁻¹
      (fun j => selectionDifferential w (fun i => z i j)) := by
  let P : Matrix κ κ ℝ := phenotypeCovariance z
  change β = Matrix.mulVec P⁻¹ _
  have hdetP : P.det ≠ 0 := hdet
  have hnormal : Matrix.mulVec P β =
      (fun j => selectionDifferential w (fun i => z i j)) := by
    funext j
    exact selection_gradient_normal_equation w z β hw horth j
  rw [← hnormal, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hdetP),
    Matrix.one_mulVec]

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem affine_offspring_cross_covariance
    {ι κ η : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (m : ι → κ → ℝ) (o : ι → η → ℝ)
    (a : η → ℝ) (B : η → κ → ℝ)
    (hlin : ∀ i j, o i j = a j + ∑ k, B j k * m i k) :
    ∀ j k, offspringCrossCovariance m o j k =
      ∑ l, B j l * phenotypeCovariance m l k := by
  intro j k
  unfold offspringCrossCovariance
  have ho : (fun i => o i j) = (fun i => a j + ∑ l, B j l * m i l) := by
    funext i
    exact hlin i j
  rw [ho, popCov_comm, cov_affine]
  apply sum_congr rfl
  intro l _
  rw [phenotypeCovariance, popCov_comm]

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem multivariate_response_matrix_inverse_covariance
    {ι κ η : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]
    (w : ι → ℝ) (m : ι → κ → ℝ) (o : ι → η → ℝ)
    (a : η → ℝ) (B : η → κ → ℝ)
    (hw : popMean w ≠ 0)
    (hlin : ∀ i j, o i j = a j + ∑ k, B j k * m i k)
    (hdet : Matrix.det (phenotypeCovariance m) ≠ 0) :
    (fun j => selectionResponse w (fun i => o i j)) =
      Matrix.mulVec (offspringCrossCovariance m o)
        (Matrix.mulVec (phenotypeCovariance m : Matrix κ κ ℝ)⁻¹
          (fun j => selectionDifferential w (fun i => m i j))) := by
  let P : Matrix κ κ ℝ := phenotypeCovariance m
  let C : Matrix η κ ℝ := offspringCrossCovariance m o
  let Bm : Matrix η κ ℝ := B
  change _ = Matrix.mulVec C (Matrix.mulVec P⁻¹ _)
  have hdetP : P.det ≠ 0 := hdet
  have hc : C = Bm * P := by
    funext j k
    exact affine_offspring_cross_covariance m o a B hlin j k
  rw [hc, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hdetP), Matrix.mul_one]
  funext j
  exact multivariate_breeder_equation w m o a B hw hlin j

end Rhone.Statistics
