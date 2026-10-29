/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Matrix

/-! # The rare-allele coefficient functionals `[p^a r^b]` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial

section Src

variable {A : Type*} [CommRing A]

def recursionSource (κA γA κB γB : A) (f : ℕ → ℕ → ℕ → A) (i j t : ℕ) : A :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : A) * f (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : A) * f (i - 2) j (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : A) * f (i - 1) j t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : A) * f i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : A) * f i (j - 2) (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : A) * f i (j - 1) t
    + ((t * (t - 1) : ℕ) : A) * (κA * κB * f (i - 2) (j - 2) (t - 2)
      + κA * γB * f (i - 2) (j - 1) (t - 2)
      + γA * κB * f (i - 1) (j - 2) (t - 2)
      + γA * γB * f (i - 1) (j - 1) (t - 1))

theorem recursionSource_eq_phiRecursionSource {F : Type*} [Field F]
    (q : Rhone.LinearAlgebra.Recursion.Config 2 2 → F)
    (πA πB : Fin 2 → F) (i j t : ℕ) :
    recursionSource (Rhone.Probability.Multilinear.kap πA) (Rhone.Probability.Multilinear.gam πA)
      (Rhone.Probability.Multilinear.kap πB) (Rhone.Probability.Multilinear.gam πB)
      (Rhone.Probability.Multilinear.Phi q πA πB) i j t =
          Rhone.Probability.SlotDeletion.phiRecursionSource q πA πB i j t :=
  rfl

theorem recursionSource_swap (κA γA κB γB : A) (f : ℕ → ℕ → ℕ → A) (i j t : ℕ) :
    recursionSource κB γB κA γA (fun a b u => f b a u) j i t = recursionSource κA γA κB γB f i j
        t := by
  simp only [recursionSource]
  ring

end Src

section Mon

noncomputable def mon (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem mon_apply_zero (a b : ℕ) : mon a b 0 = a := by
  simp [mon]

@[simp] theorem mon_apply_one (a b : ℕ) : mon a b 1 = b := by
  simp [mon]

theorem mon_zero : mon 0 0 = 0 := by
  simp [mon]

theorem finsupp_ext_fin_two {f g : Fin 2 →₀ ℕ} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  ext x
  fin_cases x
  · exact h0
  · exact h1

theorem mon_sub_A (a b : ℕ) : mon (a + 1) b - Finsupp.single (0 : Fin 2) 1 = mon a b := by
  refine finsupp_ext_fin_two ?_ ?_ <;>
    simp [Finsupp.tsub_apply]

theorem mon_sub_B (a b : ℕ) : mon a (b + 1) - Finsupp.single (1 : Fin 2) 1 = mon a b := by
  refine finsupp_ext_fin_two ?_ ?_ <;>
    simp [Finsupp.tsub_apply]

theorem zero_mem_support {a : ℕ} (b : ℕ) (h : a ≠ 0) : (0 : Fin 2) ∈ (mon a b).support := by
  rw [Finsupp.mem_support_iff, mon_apply_zero]
  exact h

theorem zero_notMem_support (b : ℕ) : (0 : Fin 2) ∉ (mon 0 b).support := by
  rw [Finsupp.mem_support_iff, mon_apply_zero]
  exact fun h => h rfl

theorem one_mem_support {b : ℕ} (a : ℕ) (h : b ≠ 0) : (1 : Fin 2) ∈ (mon a b).support := by
  rw [Finsupp.mem_support_iff, mon_apply_one]
  exact h

theorem one_notMem_support (a : ℕ) : (1 : Fin 2) ∉ (mon a 0).support := by
  rw [Finsupp.mem_support_iff, mon_apply_one]
  exact fun h => h rfl

end Mon

section Cf

variable {K : Type*} [CommRing K]

noncomputable def cf (a b : ℕ) (f : MvPolynomial (Fin 2) K) : K := f.coeff (mon a b)

theorem cf_add (a b : ℕ) (f g : MvPolynomial (Fin 2) K) :
    cf a b (f + g) = cf a b f + cf a b g := by
  simp [cf]

theorem cf_sub (a b : ℕ) (f g : MvPolynomial (Fin 2) K) :
    cf a b (f - g) = cf a b f - cf a b g := by
  simp [cf]

theorem cf_zero (a b : ℕ) : cf (K := K) a b 0 = 0 := by
  simp [cf]

theorem cf_C_mul (a b : ℕ) (c : K) (f : MvPolynomial (Fin 2) K) :
    cf a b (C c * f) = c * cf a b f := by
  simp [cf, coeff_C_mul]

theorem cf_natCast_mul (a b n : ℕ) (f : MvPolynomial (Fin 2) K) :
    cf a b ((n : MvPolynomial (Fin 2) K) * f) = (n : K) * cf a b f := by
  rw [show ((n : MvPolynomial (Fin 2) K)) = C (n : K) by simp, cf_C_mul]

theorem cf_C (a b : ℕ) (c : K) : cf a b (C c) = if a = 0 ∧ b = 0 then c else 0 := by
  rw [cf, coeff_C]
  by_cases h : a = 0 ∧ b = 0
  · rw [ite_eq_left h, ite_eq_left]
    rw [h.1, h.2, mon_zero]
  · rw [ite_eq_right h, ite_eq_right]
    intro hc
    exact h ⟨by simpa using congrArg (fun s => s (0 : Fin 2)) hc.symm,
      by simpa using congrArg (fun s => s (1 : Fin 2)) hc.symm⟩

theorem cf_X0_mul (a b : ℕ) (f : MvPolynomial (Fin 2) K) : cf (a + 1) b (X 0 * f) = cf a b f := by
  classical
  rw [cf, coeff_X_mul', ite_eq_left (zero_mem_support b (Nat.succ_ne_zero a)), mon_sub_A, cf]

theorem cf_X0_mul_zero (b : ℕ) (f : MvPolynomial (Fin 2) K) : cf 0 b (X 0 * f) = 0 := by
  classical
  rw [cf, coeff_X_mul', ite_eq_right (zero_notMem_support b)]

theorem cf_X1_mul (a b : ℕ) (f : MvPolynomial (Fin 2) K) : cf a (b + 1) (X 1 * f) = cf a b f := by
  classical
  rw [cf, coeff_X_mul', ite_eq_left (one_mem_support a (Nat.succ_ne_zero b)), mon_sub_B, cf]

theorem cf_X1_mul_zero (a : ℕ) (f : MvPolynomial (Fin 2) K) : cf a 0 (X 1 * f) = 0 := by
  classical
  rw [cf, coeff_X_mul', ite_eq_right (one_notMem_support a)]

end Cf

section Struct

variable {K : Type*} [CommRing K]

noncomputable def kapX : MvPolynomial (Fin 2) K := X 0 - X 0 ^ 2

noncomputable def gamX : MvPolynomial (Fin 2) K := 1 - 2 * X 0

noncomputable def kapY : MvPolynomial (Fin 2) K := X 1 - X 1 ^ 2

noncomputable def gamY : MvPolynomial (Fin 2) K := 1 - 2 * X 1

theorem eval_kapX (v : Fin 2 → K) : eval v (kapX : MvPolynomial (Fin 2) K) = v 0 - v 0 ^ 2 := by
  simp [kapX]

theorem eval_gamX (v : Fin 2 → K) : eval v (gamX : MvPolynomial (Fin 2) K) = 1 - 2 * v 0 := by
  simp [gamX]

theorem eval_kapY (v : Fin 2 → K) : eval v (kapY : MvPolynomial (Fin 2) K) = v 1 - v 1 ^ 2 := by
  simp [kapY]

theorem eval_gamY (v : Fin 2 → K) : eval v (gamY : MvPolynomial (Fin 2) K) = 1 - 2 * v 1 := by
  simp [gamY]

end Struct

section Bridge

variable {K : Type*} [Field K]

theorem kap_eq_sub {π : Fin 2 → K} (h : π 0 + π 1 = 1) :
    Rhone.Probability.Multilinear.kap π = π 0 - π 0 ^ 2 := by
  have h1 : π 1 = 1 - π 0 := by linear_combination h
  simp only [Rhone.Probability.Multilinear.kap, h1]
  ring

theorem gam_eq_sub {π : Fin 2 → K} (h : π 0 + π 1 = 1) :
    Rhone.Probability.Multilinear.gam π = 1 - 2 * π 0 := by
  have h1 : π 1 = 1 - π 0 := by linear_combination h
  simp only [Rhone.Probability.Multilinear.gam, h1]
  ring

theorem eval_kapX_eq_kap {π : Fin 2 → K} (h : π 0 + π 1 = 1) (v : Fin 2 → K) (hv : v 0 = π 0) :
    eval v (kapX : MvPolynomial (Fin 2) K) = Rhone.Probability.Multilinear.kap π := by
  rw [eval_kapX, kap_eq_sub h, hv]

theorem eval_gamX_eq_gam {π : Fin 2 → K} (h : π 0 + π 1 = 1) (v : Fin 2 → K) (hv : v 0 = π 0) :
    eval v (gamX : MvPolynomial (Fin 2) K) = Rhone.Probability.Multilinear.gam π := by
  rw [eval_gamX, gam_eq_sub h, hv]

theorem eval_kapY_eq_kap {π : Fin 2 → K} (h : π 0 + π 1 = 1) (v : Fin 2 → K) (hv : v 1 = π 0) :
    eval v (kapY : MvPolynomial (Fin 2) K) = Rhone.Probability.Multilinear.kap π := by
  rw [eval_kapY, kap_eq_sub h, hv]

theorem eval_gamY_eq_gam {π : Fin 2 → K} (h : π 0 + π 1 = 1) (v : Fin 2 → K) (hv : v 1 = π 0) :
    eval v (gamY : MvPolynomial (Fin 2) K) = Rhone.Probability.Multilinear.gam π := by
  rw [eval_gamY, gam_eq_sub h, hv]

end Bridge

section Action

variable {K : Type*} [CommRing K] (f : MvPolynomial (Fin 2) K)

theorem cf_X0_mul_11 : cf 1 1 (X 0 * f) = cf 0 1 f := cf_X0_mul 0 1 f
theorem cf_X0_mul_10 : cf 1 0 (X 0 * f) = cf 0 0 f := cf_X0_mul 0 0 f
theorem cf_X1_mul_11 : cf 1 1 (X 1 * f) = cf 1 0 f := cf_X1_mul 1 0 f
theorem cf_X1_mul_01 : cf 0 1 (X 1 * f) = cf 0 0 f := cf_X1_mul 0 0 f

theorem cf_two_mul (a b : ℕ) : cf a b (2 * f) = 2 * cf a b f := by
  have h2 : (2 : MvPolynomial (Fin 2) K) = C 2 :=
    (map_ofNat (C : K →+* MvPolynomial (Fin 2) K) 2).symm
  rw [h2, cf_C_mul]

private theorem kapX_mul_eq : (kapX : MvPolynomial (Fin 2) K) * f = X 0 * f - X 0 * (X 0 * f) := by
  simp only [kapX]; ring

private theorem gamX_mul_eq : (gamX : MvPolynomial (Fin 2) K) * f = f - 2 * (X 0 * f) := by
  simp only [gamX]; ring

private theorem kapY_mul_eq : (kapY : MvPolynomial (Fin 2) K) * f = X 1 * f - X 1 * (X 1 * f) := by
  simp only [kapY]; ring

private theorem gamY_mul_eq : (gamY : MvPolynomial (Fin 2) K) * f = f - 2 * (X 1 * f) := by
  simp only [gamY]; ring

theorem cf11_kapX_mul : cf 1 1 (kapX * f) = cf 0 1 f := by
  rw [kapX_mul_eq, cf_sub, cf_X0_mul_11, cf_X0_mul_11, cf_X0_mul_zero, sub_zero]

theorem cf01_kapX_mul : cf 0 1 (kapX * f) = 0 := by
  rw [kapX_mul_eq, cf_sub, cf_X0_mul_zero, cf_X0_mul_zero, sub_zero]

theorem cf10_kapX_mul : cf 1 0 (kapX * f) = cf 0 0 f := by
  rw [kapX_mul_eq, cf_sub, cf_X0_mul_10, cf_X0_mul_10, cf_X0_mul_zero, sub_zero]

theorem cf00_kapX_mul : cf 0 0 (kapX * f) = 0 := by
  rw [kapX_mul_eq, cf_sub, cf_X0_mul_zero, cf_X0_mul_zero, sub_zero]

theorem cf11_gamX_mul : cf 1 1 (gamX * f) = cf 1 1 f - 2 * cf 0 1 f := by
  rw [gamX_mul_eq, cf_sub, cf_two_mul, cf_X0_mul_11]

theorem cf01_gamX_mul : cf 0 1 (gamX * f) = cf 0 1 f := by
  rw [gamX_mul_eq, cf_sub, cf_two_mul, cf_X0_mul_zero, mul_zero, sub_zero]

theorem cf10_gamX_mul : cf 1 0 (gamX * f) = cf 1 0 f - 2 * cf 0 0 f := by
  rw [gamX_mul_eq, cf_sub, cf_two_mul, cf_X0_mul_10]

theorem cf00_gamX_mul : cf 0 0 (gamX * f) = cf 0 0 f := by
  rw [gamX_mul_eq, cf_sub, cf_two_mul, cf_X0_mul_zero, mul_zero, sub_zero]

theorem cf11_kapY_mul : cf 1 1 (kapY * f) = cf 1 0 f := by
  rw [kapY_mul_eq, cf_sub, cf_X1_mul_11, cf_X1_mul_11, cf_X1_mul_zero, sub_zero]

theorem cf10_kapY_mul : cf 1 0 (kapY * f) = 0 := by
  rw [kapY_mul_eq, cf_sub, cf_X1_mul_zero, cf_X1_mul_zero, sub_zero]

theorem cf01_kapY_mul : cf 0 1 (kapY * f) = cf 0 0 f := by
  rw [kapY_mul_eq, cf_sub, cf_X1_mul_01, cf_X1_mul_01, cf_X1_mul_zero, sub_zero]

theorem cf00_kapY_mul : cf 0 0 (kapY * f) = 0 := by
  rw [kapY_mul_eq, cf_sub, cf_X1_mul_zero, cf_X1_mul_zero, sub_zero]

theorem cf11_gamY_mul : cf 1 1 (gamY * f) = cf 1 1 f - 2 * cf 1 0 f := by
  rw [gamY_mul_eq, cf_sub, cf_two_mul, cf_X1_mul_11]

theorem cf10_gamY_mul : cf 1 0 (gamY * f) = cf 1 0 f := by
  rw [gamY_mul_eq, cf_sub, cf_two_mul, cf_X1_mul_zero, mul_zero, sub_zero]

theorem cf01_gamY_mul : cf 0 1 (gamY * f) = cf 0 1 f - 2 * cf 0 0 f := by
  rw [gamY_mul_eq, cf_sub, cf_two_mul, cf_X1_mul_01]

theorem cf00_gamY_mul : cf 0 0 (gamY * f) = cf 0 0 f := by
  rw [gamY_mul_eq, cf_sub, cf_two_mul, cf_X1_mul_zero, mul_zero, sub_zero]

theorem cf11_kapX_kapY_mul : cf 1 1 (kapX * kapY * f) = cf 0 0 f := by
  rw [mul_assoc, cf11_kapX_mul, cf01_kapY_mul]

theorem cf11_kapX_gamY_mul : cf 1 1 (kapX * gamY * f) = cf 0 1 f - 2 * cf 0 0 f := by
  rw [mul_assoc, cf11_kapX_mul, cf01_gamY_mul]

theorem cf11_gamX_kapY_mul : cf 1 1 (gamX * kapY * f) = cf 1 0 f - 2 * cf 0 0 f := by
  rw [mul_assoc, cf11_gamX_mul, cf11_kapY_mul, cf01_kapY_mul]

theorem cf11_gamX_gamY_mul :
    cf 1 1 (gamX * gamY * f) = cf 1 1 f - 2 * cf 0 1 f - 2 * cf 1 0 f + 4 * cf 0 0 f := by
  rw [mul_assoc, cf11_gamX_mul, cf11_gamY_mul, cf01_gamY_mul]
  ring

end Action

end Rhone.Probability.RareAlleleHierarchy
