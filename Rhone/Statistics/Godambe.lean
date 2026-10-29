/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.Star.Real

/-!
# Composite likelihood and the Godambe (sandwich) identities

Source: godambe1960, eq. (2), p. 1208, Theorem, p. 1209; varin_reid_firth2011, sec. 2.2, eq. (2.4),
p. 8; lindsay1988, sec. 2, eq. (2.2), (2.5)–(2.7), pp. 222–224; varin_reid_firth2011, sec. 2.3,
p. 9. -/

@[expose] public section
noncomputable section

namespace Rhone.Statistics.Godambe

open Matrix

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

def godambe (H J : Matrix n n ℝ) : Matrix n n ℝ := Hᵀ * J⁻¹ * H

def sandwich (H J : Matrix n n ℝ) : Matrix n n ℝ := H⁻¹ * J * (H⁻¹)ᵀ

variable {H J : Matrix n n ℝ}

theorem sandwich_mul_godambe (hH : IsUnit H.det) (hJ : IsUnit J.det) :
    sandwich H J * godambe H J = 1 := by
  have hHt : IsUnit Hᵀ.det := by rwa [det_transpose]
  have h1 : (H⁻¹)ᵀ * Hᵀ = 1 := by
    rw [← transpose_mul, mul_nonsing_inv _ hH, transpose_one]
  calc sandwich H J * godambe H J
      = H⁻¹ * J * ((H⁻¹)ᵀ * Hᵀ) * J⁻¹ * H := by simp only [sandwich, godambe, Matrix.mul_assoc]
    _ = 1 := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc H⁻¹ J J⁻¹, mul_nonsing_inv _ hJ, Matrix.mul_one,
          nonsing_inv_mul _ hH]

theorem godambe_mul_sandwich (hH : IsUnit H.det) (hJ : IsUnit J.det) :
    godambe H J * sandwich H J = 1 := by
  have h1 : Hᵀ * (H⁻¹)ᵀ = 1 := by
    rw [← transpose_mul, nonsing_inv_mul _ hH, transpose_one]
  calc godambe H J * sandwich H J
      = Hᵀ * J⁻¹ * (H * H⁻¹) * J * (H⁻¹)ᵀ := by simp only [sandwich, godambe, Matrix.mul_assoc]
    _ = 1 := by
        rw [mul_nonsing_inv _ hH, Matrix.mul_one, Matrix.mul_assoc Hᵀ J⁻¹ J, nonsing_inv_mul _ hJ,
          Matrix.mul_one, h1]

theorem sandwich_eq_inv_godambe (hH : IsUnit H.det) (hJ : IsUnit J.det) :
    sandwich H J = (godambe H J)⁻¹ :=
  (inv_eq_right_inv (godambe_mul_sandwich hH hJ)).symm

theorem sandwich_self (hH : IsUnit H.det) (hsymm : Hᵀ = H) : sandwich H H = H⁻¹ := by
  have : (H⁻¹)ᵀ = H⁻¹ := by rw [transpose_nonsing_inv, hsymm]
  rw [sandwich, nonsing_inv_mul _ hH, Matrix.one_mul, this]

theorem godambe_self (hH : IsUnit H.det) : godambe H H = Hᵀ := by
  rw [godambe, Matrix.mul_assoc, nonsing_inv_mul _ hH, Matrix.mul_one]

theorem sandwich_isSymm (hJ : J.IsSymm) : (sandwich H J).IsSymm := by
  unfold sandwich IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hJ.eq, Matrix.mul_assoc]

theorem sandwich_posSemidef (hJ : J.PosSemidef) : (sandwich H J).PosSemidef := by
  have := hJ.conjTranspose_mul_mul_same (H⁻¹)ᵀ
  simpa [sandwich, conjTranspose_eq_transpose_of_trivial] using this

theorem sandwich_posDef (hH : IsUnit H.det) (hJ : J.PosDef) : (sandwich H J).PosDef := by
  have hinj : Function.Injective ((H⁻¹)ᵀ).mulVec := by
    have hu : IsUnit ((H⁻¹)ᵀ).det := by
      rw [det_transpose]; exact (isUnit_nonsing_inv_det _ hH)
    intro x y hxy
    have := congrArg (fun v => ((H⁻¹)ᵀ)⁻¹ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hu] using this
  have := hJ.conjTranspose_mul_mul_same hinj
  simpa [sandwich, conjTranspose_eq_transpose_of_trivial] using this

theorem godambe_posDef (hH : IsUnit H.det) (hJ : J.PosDef) : (godambe H J).PosDef := by
  have hJi : (J⁻¹).PosDef := Matrix.posDef_inv_iff.2 hJ
  have hinj : Function.Injective H.mulVec := by
    intro x y hxy
    have := congrArg (fun v => H⁻¹ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hH] using this
  have := hJi.conjTranspose_mul_mul_same hinj
  simpa [godambe, conjTranspose_eq_transpose_of_trivial] using this

end Algebra

theorem sandwich_fin_one (H J : Matrix (Fin 1) (Fin 1) ℝ) :
    sandwich H J 0 0 = J 0 0 / (H 0 0) ^ 2 := by
  simp [sandwich, Matrix.mul_apply, div_eq_mul_inv, sq]
  ring

section Composite

variable {p : ℕ} {ι Ω Y : Type*}

def pd (j : Fin p) (F : (Fin p → ℝ) → ℝ) (θ : Fin p → ℝ) : ℝ :=
  fderiv ℝ F θ (Pi.single j 1)

structure CompositeModel (p : ℕ) (ι Ω Y : Type*) [Fintype Y] where
  T : ι → Ω → Y
  q : ι → (Fin p → ℝ) → Y → ℝ
  pos : ∀ i θ y, 0 < q i θ y
  sum_one : ∀ i θ, ∑ y, q i θ y = 1
  contDiff : ∀ i y, ContDiff ℝ 2 fun θ => q i θ y

variable [Fintype Y]

def score (M : CompositeModel p ι Ω Y) (i : ι) (j : Fin p) (y : Y) (θ : Fin p → ℝ) : ℝ :=
  pd j (fun θ' => Real.log (M.q i θ' y)) θ

def hess (M : CompositeModel p ι Ω Y) (i : ι) (j k : Fin p) (y : Y) (θ : Fin p → ℝ) : ℝ :=
  pd k (fun θ' => score M i j y θ') θ

def totalScore [Fintype ι] (M : CompositeModel p ι Ω Y) (j : Fin p) (x : Ω)
    (θ : Fin p → ℝ) : ℝ :=
  ∑ i, score M i j (M.T i x) θ

def componentFisher (M : CompositeModel p ι Ω Y) (θ : Fin p → ℝ) (i : ι) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∑ y, M.q i θ y * (score M i j y θ * score M i k y θ)

section Calculus

variable {F : (Fin p → ℝ) → ℝ}

lemma differentiable_pd (hF : ContDiff ℝ 2 F) (j : Fin p) : Differentiable ℝ (pd j F) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (h1.differentiable one_ne_zero).clm_apply (differentiable_const _)

lemma pd_log (hF : ContDiff ℝ 2 F) (hpos : ∀ θ, 0 < F θ) (j : Fin p) (θ : Fin p → ℝ) :
    pd j (fun θ' => Real.log (F θ')) θ = pd j F θ / F θ := by
  have hd : HasFDerivAt F (fderiv ℝ F θ) θ := ((hF.differentiable (by norm_num)) θ).hasFDerivAt
  have := (hd.log (hpos θ).ne').fderiv
  unfold pd
  rw [this]
  simp [div_eq_inv_mul]

lemma pd_mul {s G : (Fin p → ℝ) → ℝ} (hs : Differentiable ℝ s) (hG : Differentiable ℝ G)
    (k : Fin p) (θ : Fin p → ℝ) :
    pd k (fun θ' => s θ' * G θ') θ = pd k s θ * G θ + s θ * pd k G θ := by
  unfold pd
  rw [fderiv_fun_mul (hs θ) (hG θ)]
  simp [smul_eq_mul]
  ring

lemma score_mul (M : CompositeModel p ι Ω Y) (i : ι) (j : Fin p) (y : Y) (θ : Fin p → ℝ) :
    score M i j y θ * M.q i θ y = pd j (fun θ' => M.q i θ' y) θ := by
  unfold score
  rw [pd_log (M.contDiff i y) (fun θ => M.pos i θ y)]
  exact div_mul_cancel₀ _ (M.pos i θ y).ne'

lemma differentiable_score (M : CompositeModel p ι Ω Y) (i : ι) (j : Fin p) (y : Y) :
    Differentiable ℝ (fun θ => score M i j y θ) := by
  have : (fun θ => score M i j y θ) = fun θ =>
      pd j (fun θ' => M.q i θ' y) θ / M.q i θ y := by
    funext θ
    unfold score
    exact pd_log (M.contDiff i y) (fun θ => M.pos i θ y) j θ
  rw [this]
  simp_rw [div_eq_mul_inv]
  exact (differentiable_pd (M.contDiff i y) j).mul
    (((M.contDiff i y).differentiable (by norm_num)).inv fun θ => (M.pos i θ y).ne')

lemma hess_mul (M : CompositeModel p ι Ω Y) (i : ι) (j k : Fin p) (y : Y) (θ : Fin p → ℝ) :
    hess M i j k y θ * M.q i θ y =
      pd k (pd j (fun θ' => M.q i θ' y)) θ - score M i j y θ * pd k (fun θ' => M.q i θ' y) θ := by
  have hF : Differentiable ℝ (fun θ' => M.q i θ' y) := (M.contDiff i y).differentiable (by norm_num)
  have h1 : (fun θ' => score M i j y θ' * M.q i θ' y) = pd j (fun θ' => M.q i θ' y) := by
    funext θ'; exact score_mul M i j y θ'
  have h2 := pd_mul (differentiable_score M i j y) hF k θ
  rw [h1] at h2
  unfold hess
  linarith

lemma sum_pd_q (M : CompositeModel p ι Ω Y) (i : ι) (j : Fin p) (θ : Fin p → ℝ) :
    ∑ y, pd j (fun θ' => M.q i θ' y) θ = 0 := by
  have hconst : (fun θ' => ∑ y, M.q i θ' y) = fun _ => (1 : ℝ) := funext (M.sum_one i)
  have hdiff : ∀ y ∈ (Finset.univ : Finset Y),
      DifferentiableAt ℝ (fun θ' => M.q i θ' y) θ := fun y _ =>
    ((M.contDiff i y).differentiable (by norm_num)) θ
  have h := fderiv_fun_sum hdiff
  rw [hconst] at h
  simp only [fderiv_fun_const] at h
  have := congrArg (fun L => L (Pi.single j (1 : ℝ))) h
  simp at this
  unfold pd
  exact this.symm

lemma sum_pd_pd_q (M : CompositeModel p ι Ω Y) (i : ι) (j k : Fin p) (θ : Fin p → ℝ) :
    ∑ y, pd k (pd j (fun θ' => M.q i θ' y)) θ = 0 := by
  have hconst : (fun θ' => ∑ y, pd j (fun θ'' => M.q i θ'' y) θ') = fun _ => (0 : ℝ) :=
    funext (sum_pd_q M i j)
  have hdiff : ∀ y ∈ (Finset.univ : Finset Y),
      DifferentiableAt ℝ (pd j (fun θ' => M.q i θ' y)) θ := fun y _ =>
    differentiable_pd (M.contDiff i y) j θ
  have h := fderiv_fun_sum hdiff
  rw [hconst] at h
  simp only [fderiv_fun_const] at h
  have := congrArg (fun L => L (Pi.single k (1 : ℝ))) h
  simp at this
  unfold pd
  exact this.symm

theorem neg_expect_hess_eq_fisher (M : CompositeModel p ι Ω Y) (θ : Fin p → ℝ) (i : ι)
    (j k : Fin p) :
    -∑ y, M.q i θ y * hess M i j k y θ = componentFisher M θ i j k := by
  have h : ∀ y, M.q i θ y * hess M i j k y θ =
      pd k (pd j (fun θ' => M.q i θ' y)) θ -
        M.q i θ y * (score M i j y θ * score M i k y θ) := fun y => by
    have h1 := hess_mul M i j k y θ
    have h2 := score_mul M i k y θ
    rw [← h2] at h1
    linarith
  simp_rw [h]
  rw [Finset.sum_sub_distrib, sum_pd_pd_q M i j k θ]
  simp [componentFisher]

end Calculus

variable [Fintype Ω] [DecidableEq Y]

def MarginalCorrect (M : CompositeModel p ι Ω Y) (P : Ω → ℝ) (θ : Fin p → ℝ) (i : ι) : Prop :=
  ∀ y, ∑ x ∈ Finset.univ.filter (fun x => M.T i x = y), P x = M.q i θ y

lemma sum_comp {M : CompositeModel p ι Ω Y} {P : Ω → ℝ} {θ : Fin p → ℝ} {i : ι}
    (hmc : MarginalCorrect M P θ i) (g : Y → ℝ) :
    ∑ x, P x * g (M.T i x) = ∑ y, M.q i θ y * g y := by
  rw [← Finset.sum_fiberwise Finset.univ (M.T i) (fun x => P x * g (M.T i x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← hmc y, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]

theorem expect_score_eq_zero {M : CompositeModel p ι Ω Y} {P : Ω → ℝ} {θ : Fin p → ℝ} {i : ι}
    (hmc : MarginalCorrect M P θ i) (j : Fin p) :
    ∑ x, P x * score M i j (M.T i x) θ = 0 := by
  rw [sum_comp hmc (fun y => score M i j y θ)]
  have : ∀ y, M.q i θ y * score M i j y θ = pd j (fun θ' => M.q i θ' y) θ := fun y => by
    rw [mul_comm]; exact score_mul M i j y θ
  simp_rw [this]
  exact sum_pd_q M i j θ

theorem expect_totalScore_eq_zero [Fintype ι] {M : CompositeModel p ι Ω Y} {P : Ω → ℝ}
    {θ : Fin p → ℝ} (hmc : ∀ i, MarginalCorrect M P θ i) (j : Fin p) :
    ∑ x, P x * totalScore M j x θ = 0 := by
  unfold totalScore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => expect_score_eq_zero (hmc i) j

def sensitivity [Fintype ι] (M : CompositeModel p ι Ω Y) (P : Ω → ℝ) (θ : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k => -∑ x, P x * ∑ i, hess M i j k (M.T i x) θ

def scoreMean [Fintype ι] (M : CompositeModel p ι Ω Y) (P : Ω → ℝ) (θ : Fin p → ℝ)
    (j : Fin p) : ℝ :=
  ∑ x, P x * totalScore M j x θ

def variability [Fintype ι] (M : CompositeModel p ι Ω Y) (P : Ω → ℝ) (θ : Fin p → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∑ x, P x * ((totalScore M j x θ - scoreMean M P θ j) *
    (totalScore M k x θ - scoreMean M P θ k))

theorem sensitivity_eq_sum_fisher [Fintype ι] {M : CompositeModel p ι Ω Y} {P : Ω → ℝ}
    {θ : Fin p → ℝ} (hmc : ∀ i, MarginalCorrect M P θ i) :
    sensitivity M P θ = ∑ i, componentFisher M θ i := by
  ext j k
  simp only [sensitivity, Matrix.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_comp (hmc i) (fun y => hess M i j k y θ)]
  exact neg_expect_hess_eq_fisher M θ i j k

theorem variability_eq_second_moment [Fintype ι] {M : CompositeModel p ι Ω Y} {P : Ω → ℝ}
    {θ : Fin p → ℝ} (hmc : ∀ i, MarginalCorrect M P θ i) (j k : Fin p) :
    variability M P θ j k = ∑ x, P x * (totalScore M j x θ * totalScore M k x θ) := by
  have h0 : ∀ j, scoreMean M P θ j = 0 := expect_totalScore_eq_zero hmc
  simp [variability, h0]

omit [DecidableEq Y] in
theorem variability_posSemidef [Fintype ι] (M : CompositeModel p ι Ω Y) {P : Ω → ℝ}
    (hP : ∀ x, 0 ≤ P x) (θ : Fin p → ℝ) : (variability M P θ).PosSemidef := by
  have h : variability M P θ = ∑ x, P x • Matrix.vecMulVec
      (fun j => totalScore M j x θ - scoreMean M P θ j)
      (fun j => totalScore M j x θ - scoreMean M P θ j) := by
    ext j k
    simp [variability, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [h]
  refine Matrix.posSemidef_sum _ fun x _ => ?_
  have := (Matrix.posSemidef_vecMulVec_self_star
    (fun j => totalScore M j x θ - scoreMean M P θ j)).smul (hP x)
  simpa using this

theorem variability_eq_sensitivity_of_unique [Fintype ι] [Unique ι] {M : CompositeModel p ι Ω Y}
    {P : Ω → ℝ} {θ : Fin p → ℝ} (hmc : ∀ i, MarginalCorrect M P θ i) :
    variability M P θ = sensitivity M P θ := by
  ext j k
  rw [variability_eq_second_moment hmc, sensitivity_eq_sum_fisher hmc]
  simp only [Matrix.sum_apply, Fintype.sum_unique, totalScore, componentFisher]
  exact sum_comp (hmc default) (fun y => score M default j y θ * score M default k y θ)

omit [DecidableEq Y] in
theorem sandwich_scalar [Fintype ι] (M : CompositeModel 1 ι Ω Y) (P : Ω → ℝ) (θ : Fin 1 → ℝ) :
    sandwich (sensitivity M P θ) (variability M P θ) 0 0 =
      variability M P θ 0 0 / (sensitivity M P θ 0 0) ^ 2 :=
  sandwich_fin_one _ _

theorem sandwich_scalar_unique [Fintype ι] [Unique ι] {M : CompositeModel 1 ι Ω Y}
    {P : Ω → ℝ} {θ : Fin 1 → ℝ} (hmc : ∀ i, MarginalCorrect M P θ i) :
    sandwich (sensitivity M P θ) (variability M P θ) 0 0 = (sensitivity M P θ 0 0)⁻¹ := by
  rw [sandwich_scalar, variability_eq_sensitivity_of_unique hmc]
  rcases eq_or_ne (sensitivity M P θ 0 0) 0 with h | h
  · simp [h]
  · field_simp

end Composite

def logistic (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

lemma logistic_pos (t : ℝ) : 0 < logistic t := by unfold logistic; positivity

lemma one_sub_logistic_pos (t : ℝ) : 0 < 1 - logistic t := by
  have : 1 - logistic t = Real.exp (-t) / (1 + Real.exp (-t)) := by
    unfold logistic; field_simp; ring
  rw [this]; positivity

def logisticModel : CompositeModel 1 Unit Bool Bool where
  T := fun _ x => x
  q := fun _ θ y => if y then logistic (θ 0) else 1 - logistic (θ 0)
  pos := fun _ θ y => by
    cases y
    · simpa using one_sub_logistic_pos (θ 0)
    · simpa using logistic_pos (θ 0)
  sum_one := fun _ θ => by simp
  contDiff := fun _ y => by
    cases y
    · simp only [Bool.false_eq_true, ite_false, logistic]
      exact contDiff_const.sub (contDiff_const.div (by fun_prop) fun θ => by positivity)
    · simp only [ite_true, logistic]
      exact contDiff_const.div (by fun_prop) fun θ => by positivity

theorem logisticModel_marginalCorrect (θ : Fin 1 → ℝ) :
    MarginalCorrect logisticModel (logisticModel.q () θ) θ () := by
  intro y
  have : Finset.univ.filter (fun x : Bool => logisticModel.T () x = y) = {y} := by
    ext x; simp [logisticModel, eq_comm]
  rw [this, Finset.sum_singleton]

end Rhone.Statistics.Godambe
