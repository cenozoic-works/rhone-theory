/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KinSelection
public import Rhone.Statistics.FisherLeastSquares

/-!
# Hamilton coefficients from least-squares fits

Source: price1972, p. 488, eq. A18; hamilton1964a, pp. 14–15. -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Source: price1972, p. 485, eq. A1. -/
noncomputable def kinParentWeight (_i : ι) : ℝ := 1 / (Fintype.card ι)

/-- Source: price1972, p. 488, eq. A18; hamilton1964a, pp. 14–15. -/
noncomputable def kinSocialDesign (z y : ι → ℝ) (i : ι) : Fin 3 → ℝ := ![1,z i,y i]

/-- Source: price1972, p. 488, eq. A18. -/
noncomputable def kinRelatednessDesign (z : ι → ℝ) (i : ι) : Fin 2 → ℝ := ![1,z i]

/-- Source: price1972, p. 488, eq. A18. -/
noncomputable def kinResidual (w z y : ι → ℝ) (β : Fin 3 → ℝ) (i : ι) : ℝ :=
  w i - fisherScore (kinSocialDesign z y) β i

/-- Source: price1972, p. 488, eq. A18. -/
theorem kin_social_fit_exists (w z y : ι → ℝ) :
    ∃ β : Fin 3 → ℝ, IsFisherLeastSquares kinParentWeight w (kinSocialDesign z y) β := by
  exact fisher_leastSquares_exists _ _ _ (fun _ => by unfold kinParentWeight; positivity)

/-- Source: price1972, p. 488, eq. A18. -/
theorem kin_social_fit_orthogonal (w z y : ι → ℝ) (β : Fin 3 → ℝ)
    (hfit : IsFisherLeastSquares kinParentWeight w (kinSocialDesign z y) β) :
    popMean (kinResidual w z y β) = 0 ∧
    popCov (kinResidual w z y β) z = 0 ∧
    popCov (kinResidual w z y β) y = 0 := by
  have hn := fisher_leastSquares_normal kinParentWeight w (kinSocialDesign z y) β
    (fun _ => by unfold kinParentWeight; positivity) hfit
  have hu (f : ι → ℝ) : wMean kinParentWeight f = popMean f := by
    simp [wMean,kinParentWeight,popMean,div_eq_mul_inv,← Finset.sum_mul,mul_comm]
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  simp only [kinSocialDesign, Fin.isValue, Matrix.cons_val_zero, mul_one, hu,
    Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
  change popMean (kinResidual w z y β) = 0 at h0
  change popMean (fun i => kinResidual w z y β i * z i) = 0 at h1
  change popMean (fun i => kinResidual w z y β i * y i) = 0 at h2
  exact ⟨h0,by simp [popCov,h0,h1],by simp [popCov,h0,h2]⟩

/-- Source: price1972, p. 488, eq. A18; hamilton1964a, pp. 14–15. -/
theorem hamilton_from_leastSquares (w z y : ι → ℝ) (β : Fin 3 → ℝ)
    (hw : 0 < popMean w) (hz : 0 < popCov z z)
    (hfit : IsFisherLeastSquares kinParentWeight w (kinSocialDesign z y) β) :
    nextMean w z - popMean z = popCov z z * (β 2 * relatedness y z + β 1) / popMean w ∧
    (0 < nextMean w z - popMean z ↔ 0 < β 2 * relatedness y z + β 1) := by
  have hres := (kin_social_fit_orthogonal w z y β hfit).2.1
  have hmodel : ∀ i, w i = β 0 - (-β 1) * z i + β 2 * y i + kinResidual w z y β i := by
    intro i
    simp [kinResidual,fisherScore,kinSocialDesign,Fin.sum_univ_succ]
    ring
  constructor
  · simpa using hamilton_price w z y (kinResidual w z y β) (β 0) (β 2) (-β 1) hw hz hmodel hres
  · have h := hamilton_price_positive_iff w z y (kinResidual w z y β)
      (β 0) (β 2) (-β 1) hw hz hmodel hres
    exact h.trans (by constructor <;> intro hh <;> linarith)

/-- Source: price1972, p. 488, eq. A18; hamilton1964a, pp. 14–15. -/
theorem kin_relatedness_fit_exists (y z : ι → ℝ) (hz : 0 < popCov z z) :
    ∃ β : Fin 2 → ℝ,
      IsFisherLeastSquares kinParentWeight y (kinRelatednessDesign z) β ∧
      β 1 = relatedness y z := by
  obtain ⟨β,hβ⟩ := fisher_leastSquares_exists kinParentWeight y (kinRelatednessDesign z)
    (fun _ => by unfold kinParentWeight; positivity)
  refine ⟨β,hβ,?_⟩
  have hn := fisher_leastSquares_normal kinParentWeight y (kinRelatednessDesign z) β
    (fun _ => by unfold kinParentWeight; positivity) hβ
  have hu (f : ι → ℝ) : wMean kinParentWeight f = popMean f := by
    simp [wMean,kinParentWeight,popMean,div_eq_mul_inv,← Finset.sum_mul,mul_comm]
  have h0 := hn 0
  have h1 := hn 1
  simp only [fisherScore, kinRelatednessDesign, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, one_mul, Finset.univ_unique, Fin.default_eq_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Finset.sum_singleton,
    Fin.succ_zero_eq_one, mul_one, hu, Matrix.cons_val_one] at h0 h1
  simp only [sub_mul,add_mul] at h1
  simp only [popMean_sub,popMean_add,kin_mean_const] at h0 h1
  have hm0 : popMean (fun g => z g * β 1) = β 1 * popMean z := by
    simpa [mul_comm] using kin_mean_mul (β 1) z
  have hm1 : popMean (fun g => β 0 * z g) = β 0 * popMean z := kin_mean_mul _ _
  have hm2 : popMean (fun g => z g * β 1 * z g) = β 1 * popMean (fun g => z g * z g) := by
    convert kin_mean_mul (β 1) (fun g => z g * z g) using 1
    congr 1
    funext g
    ring
  rw [hm0] at h0
  rw [hm1,hm2] at h1
  unfold relatedness
  apply (eq_div_iff hz.ne').mpr
  unfold popCov
  nlinarith [congrArg (fun t : ℝ => t * popMean z) h0,h1]
end Rhone.Statistics
