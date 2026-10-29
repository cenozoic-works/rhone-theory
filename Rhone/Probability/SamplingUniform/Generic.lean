/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.Construction
public import Rhone.Probability.RareAlleleHierarchy.Alpha

/-! # The concrete generic centred hierarchy in the frequency variables -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open MvPolynomial Matrix LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy
    RareAlleleHierarchy

variable {K : Type*} [Field K]

noncomputable def genericPhi (a b ρ : K) (i j t : ℕ) : MvPolynomial (Fin 2) K :=
  C ((Dfull a b ρ i j)⁻¹) *
    clearedPhi (C a) (C b) (C ρ) kapX gamX kapY gamY i j t

theorem genericPhi_clear (a b ρ : K) {i j : ℕ} (hD : Dfull a b ρ i j ≠ 0) (t : ℕ) :
    C (Dfull a b ρ i j) * genericPhi a b ρ i j t =
      clearedPhi (C a) (C b) (C ρ) kapX gamX kapY gamY i j t := by
  simp only [genericPhi, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hD, map_one, one_mul]

@[simp] theorem genericPhi_one_left (a b ρ : K) (j t : ℕ) :
    genericPhi a b ρ 1 j t = 0 := by
  simp [genericPhi, clearedPhi_one_left]

@[simp] theorem genericPhi_one_right (a b ρ : K) (i t : ℕ) :
    genericPhi a b ρ i 1 t = 0 := by
  simp [genericPhi, clearedPhi_one_right]

@[simp] theorem genericPhi_zero_zero (a b ρ : K) (t : ℕ) :
    genericPhi a b ρ 0 0 t = 1 := by
  simp [genericPhi, clearedPhi_A, edgeNumerator, Dfull_j_zero]

theorem genericPhi_clamp (a b ρ : K) (i j t : ℕ) (ht : min i j ≤ t) :
    genericPhi a b ρ i j t = genericPhi a b ρ i j (min i j) := by
  unfold genericPhi
  congr 1
  by_cases hj : j = 0
  · subst j; rw [clearedPhi_A, clearedPhi_A]
  by_cases hi : i = 0
  · subst i; rw [clearedPhi_B, clearedPhi_B]
  by_cases h1i : i = 1
  · subst i; rw [clearedPhi_one_left, clearedPhi_one_left]
  by_cases h1j : j = 1
  · subst j; rw [clearedPhi_one_right, clearedPhi_one_right]
  rw [clearedPhi_interior _ _ _ _ _ _ _ (by omega) (by omega),
    clearedPhi_interior _ _ _ _ _ _ _ (by omega) (by omega)]
  congr 1
  exact Fin.ext (by simp [blockLevel, min_eq_right ht])

theorem genericPhi_cut (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0)
    {i j x y : ℕ} (hi : 2 ≤ i) (hx : x ≤ i) (hy : y ≤ j)
    (hlt : x < i ∨ y < j) (u : ℕ) :
    cutRatio (C a) (C b) (C ρ) i j x y *
        clearedPhi (C a) (C b) (C ρ) kapX gamX kapY gamY x y u =
      C (Dcut a b ρ i j) * genericPhi a b ρ x y u := by
  rw [← genericPhi_clear a b ρ (hD x y) u]
  calc
    _ = (Dfull (C a) (C b) (C ρ) x y * cutRatio (C a) (C b) (C ρ) i j x y) *
        genericPhi a b ρ x y u := by rw [← Dfull_map C]; ring
    _ = _ := by rw [Dfull_mul_cutRatio _ _ _ hx hy hlt hi, ← Dcut_map C]

theorem genericPhi_matrix (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0)
    {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.T (MvPolynomial (Fin 2) K) i j (C a) (C b) (C ρ) *ᵥ
        (fun t : Fin (min i j + 1) => genericPhi a b ρ i j t) =
      fun t : Fin (min i j + 1) => recursionSource kapX gamX kapY gamY (genericPhi a b ρ) i j t :=
          by
  let S : Fin (min i j + 1) → MvPolynomial (Fin 2) K :=
    fun t => recursionSource kapX gamX kapY gamY (genericPhi a b ρ) i j t
  have hsrc (t : ℕ) :
      recursionSource kapX gamX kapY gamY
        (fun x y u => cutRatio (C a) (C b) (C ρ) i j x y *
          clearedPhi (C a) (C b) (C ρ) kapX gamX kapY gamY x y u) i j t =
        C (Dcut a b ρ i j) * recursionSource kapX gamX kapY gamY (genericPhi a b ρ) i j t := by
    rw [← recursionSource_mul]
    apply recursionSource_congr_lower _ _ _ _ hi hj
    intro x y u hx hy hlt
    exact genericPhi_cut a b ρ hD hi hx hy (by omega) u
  have hvec : (fun t : Fin (min i j + 1) => genericPhi a b ρ i j t) =
      (C ((Dfull a b ρ i j)⁻¹) : MvPolynomial (Fin 2) K) •
        (Analysis.DenominatorEquation.U (MvPolynomial (Fin 2) K) i j (C a) (C b) (C ρ) *ᵥ
          ((C (Dcut a b ρ i j) : MvPolynomial (Fin 2) K) • S)) := by
    funext t
    have hlevel : blockLevel i j t = t :=
      Fin.ext (min_eq_left (by have := t.isLt; omega))
    rw [genericPhi, clearedPhi_interior _ _ _ _ _ _ _ hi hj]
    simp only [hsrc, hlevel, Pi.smul_apply, smul_eq_mul, S]
    rfl
  rw [hvec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Analysis.DenominatorEquation.T_mul_U,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← LinearAlgebra.Tridiag.E_map C, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  have hc : (Dfull a b ρ i j)⁻¹ * LinearAlgebra.Tridiag.E K i j a b ρ * Dcut a b ρ i j = 1 := by
    rw [mul_assoc, mul_comm (LinearAlgebra.Tridiag.E K i j a b ρ), Dcut_mul_E _ _ _ hi hj,
      inv_mul_cancel₀ (hD i j)]
  rw [hc, map_one, one_mul]

noncomputable def edgePhi (a : K) (κ γ : MvPolynomial (Fin 2) K) (n : ℕ) :
    MvPolynomial (Fin 2) K := C ((poch a n)⁻¹) * edgeNumerator (C a) κ γ n

@[simp] theorem genericPhi_A (a b ρ : K) (i t : ℕ) :
    genericPhi a b ρ i 0 t = edgePhi a kapX gamX i := by
  simp [genericPhi, clearedPhi_A, Dfull_j_zero, edgePhi]

@[simp] theorem genericPhi_B (a b ρ : K) (j t : ℕ) :
    genericPhi a b ρ 0 j t = edgePhi b kapY gamY j := by
  simp [genericPhi, clearedPhi_B, Dfull_i_zero, edgePhi]

theorem edgePhi_clear (a : K) (κ γ : MvPolynomial (Fin 2) K) {n : ℕ}
    (hn : poch a n ≠ 0) :
    C (poch a n) * edgePhi a κ γ n = edgeNumerator (C a) κ γ n := by
  simp only [edgePhi, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn, map_one, one_mul]

theorem edgePhi_rec (a : K) (κ γ : MvPolynomial (Fin 2) K)
    (hP : ∀ n, poch a n ≠ 0) (n : ℕ) :
    (C a + ((n + 1 : ℕ) : MvPolynomial (Fin 2) K)) * edgePhi a κ γ (n + 2) =
      ((n + 1 : ℕ) : MvPolynomial (Fin 2) K) *
        (κ * edgePhi a κ γ n + γ * edgePhi a κ γ (n + 1)) := by
  apply mul_left_cancel₀ (show C (poch a (n + 1)) ≠ (0 : MvPolynomial (Fin 2) K) from
    C_ne_zero.mpr (hP (n + 1)))
  have hstep : C (poch a (n + 1)) *
      (C a + ((n + 1 : ℕ) : MvPolynomial (Fin 2) K)) = C (poch a (n + 2)) := by
    rw [poch_succ_top a (by omega : 2 ≤ n + 2)]
    simp only [show n + 2 - 1 = n + 1 by omega, map_mul, map_add, map_natCast]
  have hprev : (C (poch a (n + 1)) : MvPolynomial (Fin 2) K) =
      C (poch a n) * edgeFactor (C a) (n + 1) := by
    rw [poch_edgeFactor a (n + 1)]
    simp only [Nat.add_sub_cancel, map_mul]
    congr 1
    simp [edgeFactor, apply_ite C]
  calc
    _ = edgeNumerator (C a) κ γ (n + 2) := by
      rw [← mul_assoc, hstep, edgePhi_clear a κ γ (hP (n + 2))]
    _ = _ := by
      rw [edgeNumerator]
      have hn := edgePhi_clear a κ γ (hP n)
      have hn1 := edgePhi_clear a κ γ (hP (n + 1))
      rw [← hn, ← hn1]
      rw [hprev]
      ring

theorem edgePhi_row (a : K) (κ γ : MvPolynomial (Fin 2) K)
    (hP : ∀ n, poch a n ≠ 0) (i : ℕ) :
    C ((((i * (i - 1) : ℕ) : K)) + a * i) * edgePhi a κ γ i =
      κ * (((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K) * edgePhi a κ γ (i - 2)) +
        γ * ((i * (i - 1) : ℕ) : MvPolynomial (Fin 2) K) * edgePhi a κ γ (i - 1) := by
  rcases i with _ | i
  · simp
  rcases i with _ | n
  · simp [edgePhi, edgeNumerator]
  have hr := edgePhi_rec a κ γ hP n
  simp only [Nat.add_sub_cancel, show n + 1 + 1 - 2 = n by omega]
  simp only [map_add, map_mul, map_natCast, map_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one] at hr ⊢
  linear_combination ((n : MvPolynomial (Fin 2) K) + 2) * hr

theorem genericPhi_isRecursionSolution (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0) :
    IsRecursionSolution a b ρ (genericPhi a b ρ) := by
  intro i j t ht
  have hPA : ∀ n, poch a n ≠ 0 := fun n => by simpa [Dfull_j_zero] using hD n 0
  have hPB : ∀ n, poch b n ≠ 0 := fun n => by simpa [Dfull_i_zero] using hD 0 n
  by_cases hj : j = 0
  · subst j
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa [LinearAlgebra.Tridiag.dcoef, recursionSource] using edgePhi_row a kapX gamX hPA i
  by_cases hi : i = 0
  · subst i
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa [LinearAlgebra.Tridiag.dcoef, recursionSource] using edgePhi_row b kapY gamY hPB j
  by_cases h1i : i = 1
  · subst i
    have ht1 : t ≤ 1 := le_trans ht (min_le_left _ _)
    interval_cases t <;> simp [recursionSource]
  by_cases h1j : j = 1
  · subst j
    have ht1 : t ≤ 1 := le_trans ht (min_le_right _ _)
    interval_cases t <;> simp [recursionSource]
  have hrow := congrFun (genericPhi_matrix a b ρ hD (by omega : 2 ≤ i) (by omega : 2 ≤ j))
    (⟨t, by omega⟩ : Fin (min i j + 1))
  rw [T_mulVec_apply, dcoef_C] at hrow
  exact hrow

end Rhone.Probability.SamplingUniform
