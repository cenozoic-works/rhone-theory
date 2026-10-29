/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Coeff
public import Rhone.Analysis.RecombinationExpansion.Continuant

/-! # The reduced (`π`-free) hierarchy `Θ^{i,j}_t = [p¹r¹] Φ^{i,j}_t` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial Matrix

section Rate

theorem rate_identity {R : Type*} [CommRing R] (a b t : R) :
    2 * (a * b) + a * (a + 2 * t - 1) + b * (b + 2 * t - 1) + t * (t - 1)
      = (t + a + b) * (t + a + b - 1) := by
  ring

theorem self_le_mul_add (x y : ℕ) : x ≤ x * (y + x) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact Nat.le_mul_of_pos_right x (by omega)

theorem rate_identity_nat (i j t : ℕ) (hi : t ≤ i) (hj : t ≤ j) :
    2 * ((i - t) * (j - t)) + (i - t) * (i + t - 1) + (j - t) * (j + t - 1) + t * (t - 1)
      = (i + j - t) * (i + j - t - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hj
  have ea : t + a - t = a := by omega
  have eb : t + b - t = b := by omega
  have ec : t + a + (t + b) - t = t + a + b := by omega
  have ed : t + a + t - 1 = 2 * t + a - 1 := by omega
  have ee : t + b + t - 1 = 2 * t + b - 1 := by omega
  rw [ea, eb, ec, ed, ee]
  have f1 : a * (2 * t + a - 1) = a * (2 * t + a) - a := by
    rw [show 2 * t + a - 1 = (2 * t + a) - 1 from rfl, Nat.mul_sub, mul_one]
  have f2 : b * (2 * t + b - 1) = b * (2 * t + b) - b := by
    rw [show 2 * t + b - 1 = (2 * t + b) - 1 from rfl, Nat.mul_sub, mul_one]
  have f3 : t * (t - 1) = t * t - t := by rw [Nat.mul_sub, mul_one]
  have f4 : (t + a + b) * (t + a + b - 1) = (t + a + b) * (t + a + b) - (t + a + b) := by
    rw [Nat.mul_sub, mul_one]
  rw [f1, f2, f3, f4]
  have g1 : a ≤ a * (2 * t + a) := self_le_mul_add a (2 * t)
  have g2 : b ≤ b * (2 * t + b) := self_le_mul_add b (2 * t)
  have g3 : t ≤ t * t := by simpa using self_le_mul_add t 0
  have g4 : t + a + b ≤ (t + a + b) * (t + a + b) := by
    simpa using self_le_mul_add (t + a + b) 0
  zify [g1, g2, g3, g4]
  ring

end Rate

section GammaCount

theorem gamma_count_nat (i t : ℕ) :
    (i - t) * (i - t - 1) + 2 * ((i - t) * t) = (i - t) * (i + t - 1) := by
  rcases Nat.lt_or_ge i t with h | h
  · rw [show i - t = 0 by omega]
    simp
  · exact Rhone.Probability.SlotDeletion.gamma_count i t h

theorem gamma_count_cast {K : Type*} [CommRing K] (i t : ℕ) :
    (((i - t) * (i - t - 1) : ℕ) : K) + 2 * (((i - t) * t : ℕ) : K)
      = (((i - t) * (i + t - 1) : ℕ) : K) := by
  have h := gamma_count_nat i t
  exact_mod_cast congrArg (fun n : ℕ => (n : K)) h

end GammaCount

section Expand

variable {K : Type*} [CommRing K]

theorem cf11_recursionSource (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) (i j t : ℕ) :
    cf 1 1 (recursionSource kapX gamX kapY gamY Φ i j t)
      = (((i - t) * (i - t - 1) : ℕ) : K) * cf 0 1 (Φ (i - 2) j t)
        + 2 * (((i - t) * t : ℕ) : K) * cf 0 1 (Φ (i - 2) j (t - 1))
        + (((i - t) * (i + t - 1) : ℕ) : K)
            * (cf 1 1 (Φ (i - 1) j t) - 2 * cf 0 1 (Φ (i - 1) j t))
        + (((j - t) * (j - t - 1) : ℕ) : K) * cf 1 0 (Φ i (j - 2) t)
        + 2 * (((j - t) * t : ℕ) : K) * cf 1 0 (Φ i (j - 2) (t - 1))
        + (((j - t) * (j + t - 1) : ℕ) : K)
            * (cf 1 1 (Φ i (j - 1) t) - 2 * cf 1 0 (Φ i (j - 1) t))
        + ((t * (t - 1) : ℕ) : K)
            * (cf 0 0 (Φ (i - 2) (j - 2) (t - 2))
              + (cf 0 1 (Φ (i - 2) (j - 1) (t - 2)) - 2 * cf 0 0 (Φ (i - 2) (j - 1) (t - 2)))
              + (cf 1 0 (Φ (i - 1) (j - 2) (t - 2)) - 2 * cf 0 0 (Φ (i - 1) (j - 2) (t - 2)))
              + (cf 1 1 (Φ (i - 1) (j - 1) (t - 1)) - 2 * cf 0 1 (Φ (i - 1) (j - 1) (t - 1))
                  - 2 * cf 1 0 (Φ (i - 1) (j - 1) (t - 1))
                  + 4 * cf 0 0 (Φ (i - 1) (j - 1) (t - 1)))) := by
  simp only [recursionSource, mul_assoc, cf_add, cf_two_mul, cf_natCast_mul,
    cf11_kapX_mul, cf11_gamX_mul, cf11_kapY_mul, cf01_kapY_mul,
    cf11_gamY_mul, cf01_gamY_mul]
  ring

end Expand

section Hyp

variable {K : Type*} [CommRing K]

structure RareHyp (α β : ℕ → K) (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) : Prop where
  vanA : ∀ a b u : ℕ, 1 ≤ a → ∀ m : Fin 2 →₀ ℕ, m 0 = 0 → (Φ a b u).coeff m = 0
  vanB : ∀ a b u : ℕ, 1 ≤ b → ∀ m : Fin 2 →₀ ℕ, m 1 = 0 → (Φ a b u).coeff m = 0
  oneA : ∀ b u : ℕ, Φ 1 b u = 0
  oneB : ∀ a u : ℕ, Φ a 1 u = 0
  vertex : ∀ u : ℕ, cf 0 0 (Φ 0 0 u) = 1
  betaVal : ∀ b u : ℕ, 2 ≤ b → cf 0 1 (Φ 0 b u) = β b
  alphaVal : ∀ a u : ℕ, 2 ≤ a → cf 1 0 (Φ a 0 u) = α a

variable {α β : ℕ → K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem RareHyp.cf00_A (h : RareHyp α β Φ) (a b u : ℕ) (ha : 1 ≤ a) :
    cf 0 0 (Φ a b u) = 0 := h.vanA a b u ha (mon 0 0) (by simp)

theorem RareHyp.cf01_A (h : RareHyp α β Φ) (a b u : ℕ) (ha : 1 ≤ a) :
    cf 0 1 (Φ a b u) = 0 := h.vanA a b u ha (mon 0 1) (by simp)

theorem RareHyp.cf00_B (h : RareHyp α β Φ) (a b u : ℕ) (hb : 1 ≤ b) :
    cf 0 0 (Φ a b u) = 0 := h.vanB a b u hb (mon 0 0) (by simp)

theorem RareHyp.cf10_B (h : RareHyp α β Φ) (a b u : ℕ) (hb : 1 ≤ b) :
    cf 1 0 (Φ a b u) = 0 := h.vanB a b u hb (mon 1 0) (by simp)

end Hyp

section Reduced

variable {K : Type*} [CommRing K]

noncomputable def Theta (α β : ℕ → K) (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K)
    (i j t : ℕ) : K :=
  if i = 0 ∨ j = 0 then 0
  else if i = 1 then (if j = 1 then 1 else β j)
  else if j = 1 then α i
  else cf 1 1 (Φ i j t)

variable (α β : ℕ → K) (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K)

@[simp] theorem Theta_zero_left (j t : ℕ) : Theta α β Φ 0 j t = 0 := by
  rw [Theta, ite_eq_left (Or.inl rfl)]

@[simp] theorem Theta_zero_right (i t : ℕ) : Theta α β Φ i 0 t = 0 := by
  rw [Theta, ite_eq_left (Or.inr rfl)]

@[simp] theorem Theta_one_one (t : ℕ) : Theta α β Φ 1 1 t = 1 := by
  rw [Theta, ite_eq_right (by simp), ite_eq_left rfl, ite_eq_left rfl]

theorem Theta_one_right {j : ℕ} (hj : 2 ≤ j) (t : ℕ) : Theta α β Φ 1 j t = β j := by
  rw [Theta, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega)]

theorem Theta_one_left {i : ℕ} (hi : 2 ≤ i) (t : ℕ) : Theta α β Φ i 1 t = α i := by
  rw [Theta, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem Theta_eq_cf11 {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (t : ℕ) :
    Theta α β Φ i j t = cf 1 1 (Φ i j t) := by
  rw [Theta, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

noncomputable def redSource (i j t : ℕ) : K :=
  (((i - t) * (i + t - 1) : ℕ) : K) * Theta α β Φ (i - 1) j t
    + (((j - t) * (j + t - 1) : ℕ) : K) * Theta α β Φ i (j - 1) t
    + ((t * (t - 1) : ℕ) : K) * Theta α β Φ (i - 1) (j - 1) (t - 1)

end Reduced

section Collapse

variable {K : Type*} [CommRing K] {α β : ℕ → K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem redSource_eq_cf11 (h : RareHyp α β Φ) {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (t : ℕ) :
    cf 1 1 (recursionSource kapX gamX kapY gamY Φ i j t) = redSource α β Φ i j t := by
  rw [cf11_recursionSource, redSource]
  rcases Nat.eq_or_lt_of_le hi with hi2 | hi3
  · rcases Nat.eq_or_lt_of_le hj with hj2 | hj3
    · subst hi2; subst hj2
      rw [show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
        h.betaVal 2 t (le_refl 2), h.betaVal 2 (t - 1) (le_refl 2),
        h.alphaVal 2 t (le_refl 2), h.alphaVal 2 (t - 1) (le_refl 2),
        h.oneA 2 t, h.oneB 2 t, h.oneA 0 (t - 2), h.oneB 0 (t - 2), h.oneA 1 (t - 1),
        h.vertex (t - 2), Theta_one_right α β Φ (le_refl 2) t,
        Theta_one_left α β Φ (le_refl 2) t, Theta_one_one]
      simp only [cf_zero]
      rw [← gamma_count_cast (K := K) 2 t]
      ring
    · subst hi2
      rw [show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
        h.betaVal j t (by omega), h.betaVal j (t - 1) (by omega),
        h.oneA j t, h.cf10_B 2 (j - 2) t (by omega), h.cf10_B 2 (j - 2) (t - 1) (by omega),
        h.cf10_B 2 (j - 1) t (by omega), h.cf00_B 0 (j - 2) (t - 2) (by omega),
        h.betaVal (j - 1) (t - 2) (by omega), h.cf00_B 0 (j - 1) (t - 2) (by omega),
        h.oneA (j - 2) (t - 2), h.oneA (j - 1) (t - 1),
        Theta_one_right α β Φ (by omega : 2 ≤ j) t,
        Theta_eq_cf11 α β Φ (le_refl 2) (by omega : 2 ≤ j - 1) t,
        Theta_one_right α β Φ (by omega : 2 ≤ j - 1) (t - 1)]
      simp only [cf_zero]
      rw [← gamma_count_cast (K := K) 2 t]
      ring
  · rcases Nat.eq_or_lt_of_le hj with hj2 | hj3
    · subst hj2
      rw [show (2 : ℕ) - 2 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
        h.alphaVal i t (by omega), h.alphaVal i (t - 1) (by omega),
        h.oneB i t, h.cf01_A (i - 2) 2 t (by omega),
        h.cf01_A (i - 2) 2 (t - 1) (by omega),
        h.cf01_A (i - 1) 2 t (by omega),
        h.cf00_A (i - 2) 0 (t - 2) (by omega),
        h.oneB (i - 2) (t - 2), h.alphaVal (i - 1) (t - 2) (by omega),
        h.cf00_A (i - 1) 0 (t - 2) (by omega),
        h.oneB (i - 1) (t - 1),
        Theta_one_left α β Φ (by omega : 2 ≤ i) t,
        Theta_eq_cf11 α β Φ (by omega : 2 ≤ i - 1) (le_refl 2) t,
        Theta_one_left α β Φ (by omega : 2 ≤ i - 1) (t - 1)]
      simp only [cf_zero]
      rw [← gamma_count_cast (K := K) 2 t]
      ring
    · rw [h.cf01_A (i - 2) j t (by omega),
        h.cf01_A (i - 2) j (t - 1) (by omega),
        h.cf01_A (i - 1) j t (by omega),
        h.cf10_B i (j - 2) t (by omega), h.cf10_B i (j - 2) (t - 1) (by omega),
        h.cf10_B i (j - 1) t (by omega),
        h.cf00_A (i - 2) (j - 2) (t - 2) (by omega),
        h.cf01_A (i - 2) (j - 1) (t - 2) (by omega),
        h.cf00_A (i - 2) (j - 1) (t - 2) (by omega),
        h.cf10_B (i - 1) (j - 2) (t - 2) (by omega),
        h.cf00_B (i - 1) (j - 2) (t - 2) (by omega),
        h.cf01_A (i - 1) (j - 1) (t - 1) (by omega),
        h.cf10_B (i - 1) (j - 1) (t - 1) (by omega),
        h.cf00_B (i - 1) (j - 1) (t - 1) (by omega),
        Theta_eq_cf11 α β Φ (by omega : 2 ≤ i - 1) (by omega : 2 ≤ j) t,
        Theta_eq_cf11 α β Φ (by omega : 2 ≤ i) (by omega : 2 ≤ j - 1) t,
        Theta_eq_cf11 α β Φ (by omega : 2 ≤ i - 1) (by omega : 2 ≤ j - 1) (t - 1)]
      ring

end Collapse

section System

variable {K : Type*} [CommRing K]

theorem dcoef_C (i j t : ℕ) (θA θB ρ : K) :
    LinearAlgebra.Tridiag.dcoef (MvPolynomial (Fin 2) K) i j (C θA) (C θB) (C ρ) t
      = C (LinearAlgebra.Tridiag.dcoef K i j θA θB ρ t) := by
  simp [LinearAlgebra.Tridiag.dcoef]

def IsRecursionSolution (θA θB ρ : K) (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) : Prop :=
  ∀ i j t : ℕ, t ≤ min i j →
    C (LinearAlgebra.Tridiag.dcoef K i j θA θB ρ t) * Φ i j t
      - 2 * (((i - t) * (j - t) : ℕ) : MvPolynomial (Fin 2) K) * Φ i j (t + 1)
      - C ρ * ((t : ℕ) : MvPolynomial (Fin 2) K) * Φ i j (t - 1)
      = recursionSource kapX gamX kapY gamY Φ i j t

variable {θA θB ρ : K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem cf11_row (hD : IsRecursionSolution θA θB ρ Φ) (i j t : ℕ) (ht : t ≤ min i j) :
    LinearAlgebra.Tridiag.dcoef K i j θA θB ρ t * cf 1 1 (Φ i j t)
      - 2 * (((i - t) * (j - t) : ℕ) : K) * cf 1 1 (Φ i j (t + 1))
      - ρ * (t : K) * cf 1 1 (Φ i j (t - 1))
      = cf 1 1 (recursionSource kapX gamX kapY gamY Φ i j t) := by
  have h := congrArg (cf 1 1) (hD i j t ht)
  rw [cf_sub, cf_sub, cf_C_mul, mul_assoc, cf_two_mul, cf_natCast_mul, mul_assoc,
    cf_C_mul, cf_natCast_mul] at h
  rw [← h]
  ring

variable {α β : ℕ → K}

theorem trid_mul_Theta (h : RareHyp α β Φ) (hD : IsRecursionSolution θA θB ρ Φ) {i j : ℕ}
    (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.T K i j θA θB ρ *ᵥ (fun t : Fin (min i j + 1) => Theta α β Φ i j (t : ℕ))
      = fun t : Fin (min i j + 1) => redSource α β Φ i j (t : ℕ) := by
  funext t
  have ht : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  rw [Rhone.Probability.SlotDeletion.T_mulVec_apply i j θA θB ρ (fun u => Theta α β Φ i j u) t]
  simp only [Theta_eq_cf11 α β Φ hi hj]
  rw [cf11_row hD i j (t : ℕ) ht, redSource_eq_cf11 h hi hj]

noncomputable def ell (i j : ℕ) (θA θB ρ : K) (s : ℕ) : K :=
  Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry (LinearAlgebra.Tridiag.dcoef K i j θA θB ρ)
      (LinearAlgebra.Tridiag.bcoef K i j)
    (LinearAlgebra.Tridiag.ccoef K ρ) (min i j + 1) 0 s

theorem ell_dot_of_mulVec {i j : ℕ} {v w : Fin (min i j + 1) → K}
    (hT : LinearAlgebra.Tridiag.T K i j θA θB ρ *ᵥ v = w) :
    (∑ s : Fin (min i j + 1), ell i j θA θB ρ (s : ℕ) * w s)
      = LinearAlgebra.Tridiag.E K i j θA θB ρ * v 0 := by
  have key : Rhone.LinearAlgebra.RecombinationExpansion.usmani
      (LinearAlgebra.Tridiag.dcoef K i j θA θB ρ) (LinearAlgebra.Tridiag.bcoef K i j)
        (LinearAlgebra.Tridiag.ccoef K ρ) (min i j + 1) *ᵥ w
      = LinearAlgebra.Tridiag.cont (LinearAlgebra.Tridiag.dcoef K i j θA θB ρ)
          (LinearAlgebra.Tridiag.bcoef K i j)
          (LinearAlgebra.Tridiag.ccoef K ρ) (min i j + 1) • v := by
    rw [← hT, Rhone.Analysis.RecombinationExpansion.T_eq_trid, Matrix.mulVec_mulVec,
      Rhone.LinearAlgebra.RecombinationExpansion.usmani_mul_trid, Matrix.smul_mulVec,
          Matrix.one_mulVec]
  have h0 := congrFun key 0
  simp only [Matrix.mulVec, dotProduct, Rhone.LinearAlgebra.RecombinationExpansion.usmani_apply,
      Pi.smul_apply,
    smul_eq_mul] at h0
  rw [LinearAlgebra.Tridiag.E_eq_cont]
  simp only [ell]
  simpa using h0

theorem ell_dot_redSource (h : RareHyp α β Φ) (hD : IsRecursionSolution θA θB ρ Φ) {i j : ℕ}
    (hi : 2 ≤ i) (hj : 2 ≤ j) :
    (∑ s : Fin (min i j + 1), ell i j θA θB ρ (s : ℕ) * redSource α β Φ i j (s : ℕ))
      = LinearAlgebra.Tridiag.E K i j θA θB ρ * Theta α β Φ i j 0 :=
  ell_dot_of_mulVec (trid_mul_Theta h hD hi hj)

end System

section Ground

open LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem dcoef_mul_Phi_sub_eq_recursionSource (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (i j t : ℕ)
    (ht : t ≤ min i j) :
    LinearAlgebra.Tridiag.dcoef F i j θA θB ρ t * Phi q πA πB i j t
      - 2 * (((i - t) * (j - t) : ℕ) : F) * Phi q πA πB i j (t + 1)
      - ρ * (t : F) * Phi q πA πB i j (t - 1)
      = recursionSource (kap πA) (gam πA) (kap πB) (gam πB) (Phi q πA πB) i j t := by
  have hm := congrFun (T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j) ⟨t, by omega⟩
  rw [T_mulVec_apply i j θA θB ρ (fun u => Phi q πA πB i j u) ⟨t, by omega⟩] at hm
  exact hm

end Ground

end Rhone.Probability.RareAlleleHierarchy
