/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentWindowPSD

/-! # Algebraic covariance lower bounds for a single ancestral chromosome -/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def covarianceLower (e : ℝ) (μ : ι → ℝ) : Matrix ι ι ℝ :=
  e • diagonal μ + (1 - e) • vecMulVec μ μ

omit [Fintype ι] in
lemma covarianceLower_psd [Finite ι] (e : ℝ) (μ : ι → ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hμ : ∀ i, 0 ≤ μ i) : (covarianceLower e μ).PosSemidef := by
  have ho : (vecMulVec μ μ).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star μ
  exact ((PosSemidef.diagonal hμ).smul he0).add (ho.smul (sub_nonneg.mpr he1))

lemma covarianceLower_quadratic (e : ℝ) (μ v : ι → ℝ) :
    v ⬝ᵥ (covarianceLower e μ *ᵥ v) =
      e * (∑ i, μ i * (v i)^2) + (1 - e) * (mean μ v)^2 := by
  have hdiag : v ⬝ᵥ (diagonal μ *ᵥ v) = ∑ i, μ i * (v i)^2 := by
    simp only [Matrix.mulVec, dotProduct, diagonal_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have houter : v ⬝ᵥ (fun i => μ i * (μ ⬝ᵥ v)) = (mean μ v)^2 := by
    unfold dotProduct mean
    have he (i : ι) : v i * (μ i * (∑ j, μ j * v j)) =
        (μ i * v i) * (∑ j, μ j * v j) := by ring
    simp_rw [he]
    rw [← Finset.sum_mul]
    ring
  have hvec : vecMulVec μ μ *ᵥ v = fun i => μ i * (μ ⬝ᵥ v) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, mul_assoc, Finset.mul_sum]
  simp only [covarianceLower, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hvec, hdiag, houter]

omit [DecidableEq ι] in
lemma quadratic_lower_of_psd_sub {C D : Matrix ι ι ℝ} (h : (C - D).PosSemidef)
    (v : ι → ℝ) : v ⬝ᵥ (D *ᵥ v) ≤ v ⬝ᵥ (C *ᵥ v) := by
  have hn := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hn
  linarith

theorem same_root_covariance_gap_pos {e : ℝ} (he : 0 < e) (μ : ι → ℝ)
    (hμ : ∑ i, μ i = 1) (hp : ∀ i, 0 < μ i) (hne : ∃ i j, μ i ≠ μ j)
    (C : Matrix ι ι ℝ) (hC : (C - covarianceLower e μ).PosSemidef) :
    0 < μ ⬝ᵥ (C *ᵥ μ) - (mean μ μ)^2 := by
  have hl := quadratic_lower_of_psd_sub hC μ
  rw [covarianceLower_quadratic] at hl
  have hv := variance_pos μ μ hp hne
  rw [variance_identity μ μ hμ] at hv
  have hpos := mul_pos he hv
  nlinarith

end Rhone.Statistics.Identifiability.SilentWindow
