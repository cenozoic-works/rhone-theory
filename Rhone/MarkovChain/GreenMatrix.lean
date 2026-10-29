/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # The Green matrix of a killed finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.GreenMatrix

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [Field 𝕜]

noncomputable def green (Q : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 := (1 - Q)⁻¹

def killing (Q : Matrix ι ι 𝕜) : ι → 𝕜 := (1 - Q) *ᵥ 1

noncomputable def meanTime (Q : Matrix ι ι 𝕜) : ι → 𝕜 := green Q *ᵥ 1

noncomputable def greenRow (Q : Matrix ι ι 𝕜) (a : ι) : ι → 𝕜 := (green Q a a)⁻¹ • green Q a

def augmented (Q : Matrix ι ι 𝕜) (μ : ι → 𝕜) (m : 𝕜) : Matrix (Option ι) (Option ι) 𝕜 :=
  Matrix.of fun i j =>
    match i, j with
    | some i, some j => Q i j
    | some i, none => killing Q i
    | none, some j => μ j
    | none, none => m

variable {Q : Matrix ι ι 𝕜}

theorem killing_apply (Q : Matrix ι ι 𝕜) (i : ι) : killing Q i = 1 - ∑ j, Q i j := by
  rw [killing, sub_mulVec, one_mulVec, Pi.sub_apply, Pi.one_apply]
  simp [mulVec, dotProduct]

theorem green_mul (hQ : IsUnit (1 - Q)) : green Q * (1 - Q) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hQ)

theorem mul_green (hQ : IsUnit (1 - Q)) : (1 - Q) * green Q = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQ)

theorem eq_vecMul_green (hQ : IsUnit (1 - Q)) {u v : ι → 𝕜} (h : v ᵥ* (1 - Q) = u) :
    v = u ᵥ* green Q := by
  rw [← h, vecMul_vecMul, mul_green hQ, vecMul_one]

theorem green_mulVec_killing (hQ : IsUnit (1 - Q)) : green Q *ᵥ killing Q = 1 := by
  rw [killing, mulVec_mulVec, green_mul hQ, one_mulVec]

theorem one_sub_mulVec_meanTime (hQ : IsUnit (1 - Q)) : (1 - Q) *ᵥ meanTime Q = 1 := by
  rw [meanTime, mulVec_mulVec, mul_green hQ, one_mulVec]

theorem eq_meanTime (hQ : IsUnit (1 - Q)) {τ : ι → 𝕜} (h : (1 - Q) *ᵥ τ = 1) :
    τ = meanTime Q := by
  rw [meanTime, ← h, mulVec_mulVec, green_mul hQ, one_mulVec]

theorem dotProduct_one_eq (hQ : IsUnit (1 - Q)) {u v : ι → 𝕜} (h : v ᵥ* (1 - Q) = u) :
    v ⬝ᵥ 1 = u ⬝ᵥ meanTime Q := by
  rw [eq_vecMul_green hQ h, meanTime, dotProduct_mulVec]

theorem greenRow_self {a : ι} (h : green Q a a ≠ 0) : greenRow Q a a = 1 := by
  simp [greenRow, h]

theorem greenRow_vecMul (hQ : IsUnit (1 - Q)) (a : ι) :
    greenRow Q a ᵥ* (1 - Q) = (green Q a a)⁻¹ • Pi.single a 1 := by
  have hrow : green Q a = Pi.single a 1 ᵥ* green Q := (single_one_vecMul a (green Q)).symm
  rw [greenRow, smul_vecMul, hrow, vecMul_vecMul, green_mul hQ, vecMul_one]

theorem greenRow_vecMul_apply_of_ne (hQ : IsUnit (1 - Q)) {a j : ι} (hj : j ≠ a) :
    (greenRow Q a ᵥ* (1 - Q)) j = 0 := by
  rw [greenRow_vecMul hQ]
  simp [hj]

theorem eq_greenRow (hQ : IsUnit (1 - Q)) {a : ι} {d : ι → 𝕜} (ha : d a = 1)
    (hoff : ∀ j, j ≠ a → (d ᵥ* (1 - Q)) j = 0) : d = greenRow Q a ∧ green Q a a ≠ 0 := by
  have hvec : d ᵥ* (1 - Q) = (d ᵥ* (1 - Q)) a • Pi.single a 1 := by
    funext j
    by_cases hj : j = a
    · subst hj
      simp
    · simp [hoff j hj, hj]
  have hd : d = (d ᵥ* (1 - Q)) a • green Q a := by
    have h := eq_vecMul_green hQ hvec
    rwa [smul_vecMul, single_one_vecMul] at h
  have hmul : (d ᵥ* (1 - Q)) a * green Q a a = 1 := by
    have h := congrFun hd a
    rw [ha] at h
    simpa using h.symm
  have hne : green Q a a ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  refine ⟨?_, hne⟩
  rw [greenRow, ← eq_inv_of_mul_eq_one_left hmul]
  exact hd

theorem greenRow_dotProduct_killing (hQ : IsUnit (1 - Q)) (a : ι) :
    greenRow Q a ⬝ᵥ killing Q = (green Q a a)⁻¹ := by
  have h : green Q a ⬝ᵥ killing Q = 1 := congrFun (green_mulVec_killing hQ) a
  rw [greenRow, smul_dotProduct, h, smul_eq_mul, mul_one]

theorem greenRow_dotProduct_one (Q : Matrix ι ι 𝕜) (a : ι) :
    greenRow Q a ⬝ᵥ 1 = (green Q a a)⁻¹ * meanTime Q a := by
  rw [greenRow, smul_dotProduct, smul_eq_mul]
  rfl

theorem greenRow_ratio (hQ : IsUnit (1 - Q)) {a : ι} (h : green Q a a ≠ 0) :
    (greenRow Q a ⬝ᵥ 1) / (greenRow Q a ⬝ᵥ killing Q) = meanTime Q a := by
  rw [greenRow_dotProduct_killing hQ, greenRow_dotProduct_one]
  field_simp

theorem one_sub_eq_dotProduct_killing {ν : ι → 𝕜} {lam : 𝕜} (hν : ν ᵥ* Q = lam • ν)
    (h1 : ν ⬝ᵥ 1 = 1) : 1 - lam = ν ⬝ᵥ killing Q := by
  rw [killing, dotProduct_mulVec, vecMul_sub, vecMul_one, hν, sub_dotProduct, smul_dotProduct,
    h1, smul_eq_mul, mul_one]

theorem dotProduct_meanTime_of_eigen (hQ : IsUnit (1 - Q)) {ν : ι → 𝕜} {lam : 𝕜}
    (hν : ν ᵥ* Q = lam • ν) (h1 : ν ⬝ᵥ 1 = 1) : ν ⬝ᵥ meanTime Q = (1 - lam)⁻¹ := by
  have hvec : ν ᵥ* (1 - Q) = (1 - lam) • ν := by
    rw [vecMul_sub, vecMul_one, hν, sub_smul, one_smul]
  have h := dotProduct_one_eq hQ hvec
  rw [h1, smul_dotProduct, smul_eq_mul] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem one_sub_ne_zero_of_eigen (hQ : IsUnit (1 - Q)) {ν : ι → 𝕜} {lam : 𝕜}
    (hν : ν ᵥ* Q = lam • ν) (h1 : ν ⬝ᵥ 1 = 1) : 1 - lam ≠ 0 := by
  have hvec : ν ᵥ* (1 - Q) = (1 - lam) • ν := by
    rw [vecMul_sub, vecMul_one, hν, sub_smul, one_smul]
  have h := dotProduct_one_eq hQ hvec
  rw [h1, smul_dotProduct, smul_eq_mul] at h
  exact left_ne_zero_of_mul_eq_one h.symm

theorem vecMul_pow_of_eigen {ν : ι → 𝕜} {lam : 𝕜} (hν : ν ᵥ* Q = lam • ν) (t : ℕ) :
    ν ᵥ* Q ^ t = lam ^ t • ν := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, hν, smul_smul, pow_succ]

theorem dotProduct_pow_mulVec_one {ν : ι → 𝕜} {lam : 𝕜} (hν : ν ᵥ* Q = lam • ν)
    (h1 : ν ⬝ᵥ 1 = 1) (t : ℕ) : ν ⬝ᵥ (Q ^ t *ᵥ 1) = lam ^ t := by
  rw [dotProduct_mulVec, vecMul_pow_of_eigen hν, smul_dotProduct, h1, smul_eq_mul, mul_one]

theorem vecMul_one_sub_of_stationary {B : Matrix ι ι 𝕜} {π : ι → 𝕜}
    (hπ : π ᵥ* (Q + B) = π) : π ᵥ* (1 - Q) = π ᵥ* B := by
  rw [vecMul_add] at hπ
  rw [vecMul_sub, vecMul_one]
  exact sub_eq_of_eq_add' hπ.symm

theorem kac_dotProduct_meanTime (hQ : IsUnit (1 - Q)) {B : Matrix ι ι 𝕜} {π : ι → 𝕜}
    (hπ : π ᵥ* (Q + B) = π) : (π ᵥ* B) ⬝ᵥ meanTime Q = π ⬝ᵥ 1 :=
  (dotProduct_one_eq hQ (vecMul_one_sub_of_stationary hπ)).symm

theorem kac_dotProduct_one {B : Matrix ι ι 𝕜} (hB : B *ᵥ 1 = killing Q) (π : ι → 𝕜) :
    (π ᵥ* B) ⬝ᵥ 1 = π ⬝ᵥ killing Q := by
  rw [← dotProduct_mulVec, hB]

theorem kac_vecMul_green_mul (hQ : IsUnit (1 - Q)) {B : Matrix ι ι 𝕜} {π : ι → 𝕜}
    (hπ : π ᵥ* (Q + B) = π) : (π ᵥ* B) ᵥ* (green Q * B) = π ᵥ* B := by
  rw [← vecMul_vecMul, ← eq_vecMul_green hQ (vecMul_one_sub_of_stationary hπ)]

theorem kac_formula (hQ : IsUnit (1 - Q)) {B : Matrix ι ι 𝕜} {π : ι → 𝕜}
    (hπ : π ᵥ* (Q + B) = π) (hB : B *ᵥ 1 = killing Q) (h1 : π ⬝ᵥ 1 = 1)
    (hne : π ⬝ᵥ killing Q ≠ 0) :
    ((π ⬝ᵥ killing Q)⁻¹ • (π ᵥ* B)) ⬝ᵥ 1 = 1 ∧
      ((π ⬝ᵥ killing Q)⁻¹ • (π ᵥ* B)) ⬝ᵥ meanTime Q = (π ⬝ᵥ killing Q)⁻¹ := by
  constructor
  · rw [smul_dotProduct, kac_dotProduct_one hB, smul_eq_mul, inv_mul_cancel₀ hne]
  · rw [smul_dotProduct, kac_dotProduct_meanTime hQ hπ, h1, smul_eq_mul, mul_one]

theorem sum_some_eq_of_vecMul_augmented (hQ : IsUnit (1 - Q)) {μ : ι → 𝕜} {m : 𝕜}
    {σ : Option ι → 𝕜} (hσ : σ ᵥ* augmented Q μ m = σ) :
    ∑ i, σ (some i) = σ none * (μ ⬝ᵥ meanTime Q) := by
  have hvec : (fun i => σ (some i)) ᵥ* (1 - Q) = σ none • μ := by
    funext j
    have h := congrFun hσ (some j)
    simp only [vecMul, dotProduct, Fintype.sum_option, augmented, Matrix.of_apply] at h
    rw [vecMul_sub, vecMul_one]
    simp only [Pi.sub_apply, vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [← h, add_sub_cancel_right]
  have h := dotProduct_one_eq hQ hvec
  rw [dotProduct_one, smul_dotProduct, smul_eq_mul] at h
  exact h

theorem dotProduct_meanTime_of_vecMul_augmented (hQ : IsUnit (1 - Q)) {μ : ι → 𝕜} {m : 𝕜}
    {σ : Option ι → 𝕜} (hσ : σ ᵥ* augmented Q μ m = σ) (h1 : ∑ i, σ i = 1)
    (hne : σ none ≠ 0) : μ ⬝ᵥ meanTime Q = (1 - σ none) / σ none := by
  have h := sum_some_eq_of_vecMul_augmented hQ hσ
  rw [Fintype.sum_option] at h1
  rw [eq_div_iff hne]
  rw [← h1, h]
  ring

end Rhone.MarkovChain.GreenMatrix
