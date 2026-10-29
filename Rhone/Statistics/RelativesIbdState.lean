/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.IndependentRelatives

/-!
# Single-locus covariance between relatives with identity coefficients as parameters

Source: kempthorne1954, p. 112. -/

@[expose] public section

namespace Rhone.Statistics

noncomputable def ibdStateCov (k : Fin 3 → ℝ) (p : ℝ) (G : Fin 3 → ℝ) : ℝ :=
  k 0 * (genoMean p G) ^ 2 + k 1 * sharedAlleleProduct p G G +
    k 2 * hwExp p (fun g => (G g) ^ 2) - (genoMean p G) ^ 2

noncomputable def ibdStateKinship (k : Fin 3 → ℝ) : ℝ := k 1 / 4 + k 2 / 2

def ibdStateFraternity (k : Fin 3 → ℝ) : ℝ := k 2

noncomputable def ibdStateOfCoefficients (θ δ : ℝ) : Fin 3 → ℝ :=
  ![1 - 4 * θ + δ, 4 * θ - 2 * δ, δ]

noncomputable def ibdStateJoint (k : Fin 3 → ℝ) (p : ℝ) (pair : Fin 3 × Fin 3) : ℝ :=
  k 0 * (hwProbability p pair.1 * hwProbability p pair.2) + k 1 * sharedJoint p pair +
    k 2 * (if pair.1 = pair.2 then hwProbability p pair.1 else 0)

theorem ibd_state_covariance (k : Fin 3 → ℝ) (p : ℝ) (G : Fin 3 → ℝ)
    (hk : k 0 + k 1 + k 2 = 1) :
    ibdStateCov k p G =
      2 * ibdStateKinship k * varA p G + ibdStateFraternity k * varD p G := by
  have hk0 : k 0 = 1 - k 1 - k 2 := by linarith
  rw [varA_eq, varD_eq]
  simp only [ibdStateCov, ibdStateKinship, ibdStateFraternity, sharedAlleleProduct, genoMean,
    hwExp, avgEffect, addParam, domParam, hk0]
  ring

theorem ibdStateOfCoefficients_sum (θ δ : ℝ) :
    ibdStateOfCoefficients θ δ 0 + ibdStateOfCoefficients θ δ 1 +
      ibdStateOfCoefficients θ δ 2 = 1 := by
  simp only [ibdStateOfCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem ibdStateKinship_ofCoefficients (θ δ : ℝ) :
    ibdStateKinship (ibdStateOfCoefficients θ δ) = θ := by
  simp only [ibdStateKinship, ibdStateOfCoefficients, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem ibdStateFraternity_ofCoefficients (θ δ : ℝ) :
    ibdStateFraternity (ibdStateOfCoefficients θ δ) = δ := by
  simp [ibdStateFraternity, ibdStateOfCoefficients]

theorem covariance_of_kinship_fraternity (θ δ p : ℝ) (G : Fin 3 → ℝ) :
    ibdStateCov (ibdStateOfCoefficients θ δ) p G = 2 * θ * varA p G + δ * varD p G := by
  rw [ibd_state_covariance _ p G (ibdStateOfCoefficients_sum θ δ),
    ibdStateKinship_ofCoefficients, ibdStateFraternity_ofCoefficients]

theorem ibdStateJoint_product (k : Fin 3 → ℝ) (p : ℝ) (G : Fin 3 → ℝ) :
    ∑ pair : Fin 3 × Fin 3, ibdStateJoint k p pair * (G pair.1 * G pair.2) -
      (genoMean p G) ^ 2 = ibdStateCov k p G := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, ibdStateJoint, ibdStateCov, sharedJoint,
    hwProbability, sharedAlleleProduct, genoMean, hwExp]
  ring

theorem relativeJoint_parentOffspring (p : ℝ) (pair : Fin 3 × Fin 3) :
    relativeJoint .parentOffspring p pair = ibdStateJoint ![0, 1, 0] p pair := by
  simp [relativeJoint, ibdStateJoint]

theorem relativeJoint_halfSib (p : ℝ) (pair : Fin 3 × Fin 3) :
    relativeJoint .halfSib p pair = ibdStateJoint ![1 / 2, 1 / 2, 0] p pair := by
  simp only [relativeJoint, ibdStateJoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem relativeJoint_fullSib (p : ℝ) (pair : Fin 3 × Fin 3) :
    relativeJoint .fullSib p pair = ibdStateJoint ![1 / 4, 1 / 2, 1 / 4] p pair := by
  simp only [relativeJoint, ibdStateJoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem parentOffspringCov_eq_ibdStateCov (p : ℝ) (G : Fin 3 → ℝ) :
    parentOffspringCov p G = ibdStateCov ![0, 1, 0] p G := by
  simp only [parentOffspringCov, sharedAlleleCov, ibdStateCov, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem halfSibCov_eq_ibdStateCov (p : ℝ) (G : Fin 3 → ℝ) :
    halfSibCov p G = ibdStateCov ![1 / 2, 1 / 2, 0] p G := by
  simp only [halfSibCov, ibdStateCov, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem fullSibCov_eq_ibdStateCov (p : ℝ) (G : Fin 3 → ℝ) :
    fullSibCov p G = ibdStateCov ![1 / 4, 1 / 2, 1 / 4] p G := by
  simp only [fullSibCov, ibdStateCov, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- Source: kempthorne1954, p. 112; felsenstein_teg2019, sec. IX.5, eq. (IX-51), eq. (IX-53), pp.
428–429. -/
theorem parent_offspring_covariance_of_ibd_state (p : ℝ) (G : Fin 3 → ℝ) :
    parentOffspringCov p G = varA p G / 2 := by
  rw [parentOffspringCov_eq_ibdStateCov, ibd_state_covariance _ p G (by norm_num)]
  simp only [ibdStateKinship, ibdStateFraternity, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Source: kempthorne1954, p. 112; felsenstein_teg2019, sec. IX.5, eq. (IX-51), eq. (IX-54), pp.
428–429. -/
theorem half_sib_covariance_of_ibd_state (p : ℝ) (G : Fin 3 → ℝ) :
    halfSibCov p G = varA p G / 4 := by
  rw [halfSibCov_eq_ibdStateCov, ibd_state_covariance _ p G (by norm_num)]
  simp only [ibdStateKinship, ibdStateFraternity, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Source: kempthorne1954, p. 112; felsenstein_teg2019, sec. IX.5, eq. (IX-51), eq. (IX-55), pp.
428–429. -/
theorem full_sib_covariance_of_ibd_state (p : ℝ) (G : Fin 3 → ℝ) :
    fullSibCov p G = varA p G / 2 + varD p G / 4 := by
  rw [fullSibCov_eq_ibdStateCov, ibd_state_covariance _ p G (by norm_num)]
  simp only [ibdStateKinship, ibdStateFraternity, Matrix.cons_val_one, Matrix.cons_val]
  ring

end Rhone.Statistics
