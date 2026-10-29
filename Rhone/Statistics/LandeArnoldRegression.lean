/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KinSelectionRegression
public import Rhone.Statistics.MultivariateResponse

/-!
# Lande-Arnold coefficients from relative-fitness regression

Source: lande_arnold1983, pp. 1212–1213. -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

/-- Source: lande_arnold1983, pp. 1212–1213. -/
noncomputable def landeArnoldRelativeFitness (w : ι → ℝ) (i : ι) : ℝ :=
  w i / popMean w

/-- Source: lande_arnold1983, pp. 1212–1213. -/
noncomputable def landeArnoldDesign (z : ι → κ → ℝ) (i : ι) : Option κ → ℝ
  | none => 1
  | some j => z i j - popMean (fun i => z i j)

/-- Source: lande_arnold1983, pp. 1212–1213. -/
noncomputable def landeArnoldResidual (w : ι → ℝ) (z : ι → κ → ℝ)
    (γ : Option κ → ℝ) (i : ι) : ℝ :=
  landeArnoldRelativeFitness w i - fisherScore (landeArnoldDesign z) γ i

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_fit_exists (w : ι → ℝ) (z : ι → κ → ℝ) :
    ∃ γ : Option κ → ℝ,
      IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ := by
  exact fisher_leastSquares_exists _ _ _ (fun _ => by unfold kinParentWeight; positivity)

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_fit_orthogonal (w : ι → ℝ) (z : ι → κ → ℝ)
    (γ : Option κ → ℝ)
    (hfit : IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ) :
    popMean (landeArnoldResidual w z γ) = 0 ∧
    ∀ j, popCov (landeArnoldResidual w z γ) (fun i => z i j) = 0 := by
  have hn := fisher_leastSquares_normal kinParentWeight (landeArnoldRelativeFitness w)
    (landeArnoldDesign z) γ (fun _ => by unfold kinParentWeight; positivity) hfit
  have hu (f : ι → ℝ) : wMean kinParentWeight f = popMean f := by
    simp [wMean, kinParentWeight, popMean, div_eq_mul_inv, ← Finset.sum_mul, mul_comm]
  have h0 := hn none
  simp only [landeArnoldDesign, mul_one] at h0
  change wMean kinParentWeight (landeArnoldResidual w z γ) = 0 at h0
  rw [hu] at h0
  refine ⟨h0, ?_⟩
  intro j
  have hj := hn (some j)
  change wMean kinParentWeight
    (fun i => landeArnoldResidual w z γ i * (z i j - popMean (fun i => z i j))) = 0 at hj
  rw [hu] at hj
  have hm : popMean (fun i => landeArnoldResidual w z γ i * popMean (fun i => z i j)) =
      popMean (landeArnoldResidual w z γ) * popMean (fun i => z i j) := by
    simpa [mul_comm] using kin_mean_mul (popMean (fun i => z i j)) (landeArnoldResidual w z γ)
  unfold popCov
  simpa only [mul_sub, popMean_sub, hm] using hj

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_fit_intercept (w : ι → ℝ) (z : ι → κ → ℝ)
    (γ : Option κ → ℝ) (hw : 0 < popMean w)
    (hfit : IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ) :
    γ none = 1 ∧ landeArnoldResidual w z γ = selectionResidual w z (fun j => γ (some j)) := by
  have hsum (f : κ → ι → ℝ) : popMean (fun i => ∑ j, f j i) = ∑ j, popMean (f j) := by
    simp only [popMean, Finset.sum_div]
    rw [Finset.sum_comm]
  have hc (j : κ) : popMean (fun i => (z i j - popMean (fun i => z i j)) * γ (some j)) = 0 := by
    simpa [popMean_sub, kin_mean_const, mul_comm] using
      kin_mean_mul (γ (some j)) (fun i => z i j - popMean (fun i => z i j))
  have hscore : popMean (fisherScore (landeArnoldDesign z) γ) = γ none := by
    change popMean (fun i => fisherScore (landeArnoldDesign z) γ i) = γ none
    simp [fisherScore, Fintype.sum_option, landeArnoldDesign, one_mul, popMean_add,
      kin_mean_const, hsum, hc, Finset.sum_const_zero, add_zero]
  have hrel : popMean (landeArnoldRelativeFitness w) = 1 := by
    change popMean (fun i => w i / popMean w) = 1
    simpa [landeArnoldRelativeFitness, div_eq_mul_inv, mul_comm, hw.ne'] using
      kin_mean_mul (popMean w)⁻¹ w
  have hres := (lande_arnold_fit_orthogonal w z γ hfit).1
  have hintercept : γ none = 1 := by
    unfold landeArnoldResidual at hres
    rw [popMean_sub, hrel, hscore] at hres
    linarith
  refine ⟨hintercept, ?_⟩
  funext i
  unfold landeArnoldResidual landeArnoldRelativeFitness fisherScore selectionResidual
  simp only [Fintype.sum_option, landeArnoldDesign, one_mul, hintercept]
  have hsum' : (∑ j, (z i j - popMean (fun i => z i j)) * γ (some j)) =
      ∑ j, γ (some j) * (z i j - popMean (fun i => z i j)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum']
  ring

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_fit_normal (w : ι → ℝ) (z : ι → κ → ℝ)
    (γ : Option κ → ℝ) (hw : 0 < popMean w)
    (hfit : IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ) :
    Matrix.mulVec (phenotypeCovariance z) (fun j => γ (some j)) =
      (fun j => selectionDifferential w (fun i => z i j)) := by
  have hres := (lande_arnold_fit_intercept w z γ hw hfit).2
  have horth := (lande_arnold_fit_orthogonal w z γ hfit).2
  funext j
  apply selection_gradient_normal_equation w z _ hw.ne'
  intro k
  rw [← hres, popCov_comm]
  exact horth k

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_fit_inverse [DecidableEq κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (γ : Option κ → ℝ) (hw : 0 < popMean w)
    (hfit : IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ)
    (hdet : Matrix.det (phenotypeCovariance z) ≠ 0) :
    (fun j => γ (some j)) =
      Matrix.mulVec (phenotypeCovariance z : Matrix κ κ ℝ)⁻¹
        (fun j => selectionDifferential w (fun i => z i j)) := by
  apply selection_gradient_matrix_inverse w z _ hw.ne' _ hdet
  intro j
  rw [← (lande_arnold_fit_intercept w z γ hw hfit).2, popCov_comm]
  exact (lande_arnold_fit_orthogonal w z γ hfit).2 j

/-- Source: lande_arnold1983, pp. 1212–1213. -/
theorem lande_arnold_gradient_exists [DecidableEq κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (hw : 0 < popMean w)
    (hdet : Matrix.det (phenotypeCovariance z) ≠ 0) :
    ∃ γ : Option κ → ℝ,
      IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ ∧
      γ none = 1 ∧ (fun j => γ (some j)) =
        Matrix.mulVec (phenotypeCovariance z : Matrix κ κ ℝ)⁻¹
          (fun j => selectionDifferential w (fun i => z i j)) := by
  obtain ⟨γ, hγ⟩ := lande_arnold_fit_exists w z
  exact ⟨γ, hγ, (lande_arnold_fit_intercept w z γ hw hγ).1,
    lande_arnold_fit_inverse w z γ hw hγ hdet⟩

end Rhone.Statistics
