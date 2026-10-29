/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedForms.Block22
public import Rhone.MarkovChain.Biallelic.OneLocus

/-! # Two-sample values and the three `κ_t` -/

@[expose] public section

namespace Rhone.MarkovChain.ClosedForms

open Finset LinearAlgebra.Recursion

variable {K : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {π : Fin K → F}

def Uval (π : Fin K → F) (i₁ i₂ : Fin K) : F := π i₁ * ((if i₁ = i₂ then 1 else 0) - π i₂)

def Gval (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F :=
  qOne θ π m - ∑ i, ((Nat.choose (m i) 2 : ℕ) : F) * qOne θ π (decf m i)

def twoSame (i : Fin K) : Fin K → ℕ := incf (incf (fun _ => 0) i) i

def twoDiff (i i' : Fin K) : Fin K → ℕ := incf (incf (fun _ => 0) i) i'

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prod_rising_e (f : Fin K → F) (i : Fin K) :
    ∏ k, rising (f k) (incf (fun _ => 0) i k) = f i := by
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [incf_self]; simp
  · intro k _ hk; rw [incf_of_ne _ hk]; simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem rising_two (x : F) : rising x 2 = x * (x + 1) := by
  rw [rising_succ, rising_one]
  norm_num

theorem twoSame_apply_self (i : Fin K) : twoSame i i = 2 := by
  simp [twoSame, incf_self]

theorem twoSame_apply_of_ne {i k : Fin K} (h : k ≠ i) : twoSame i k = 0 := by
  simp [twoSame, incf_of_ne _ h]

theorem decf_twoSame (i : Fin K) : decf (twoSame i) i = incf (fun _ => 0) i := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [decf_self, twoSame_apply_self, incf_self]
  · rw [decf_of_ne _ hk, twoSame_apply_of_ne hk, incf_of_ne _ hk]

theorem twoDiff_apply_left {i i' : Fin K} (h : i ≠ i') : twoDiff i i' i = 1 := by
  simp [twoDiff, incf_of_ne _ h, incf_self]

theorem twoDiff_apply_right {i i' : Fin K} (h : i ≠ i') : twoDiff i i' i' = 1 := by
  simp [twoDiff, incf_self, incf_of_ne _ (Ne.symm h)]

theorem twoDiff_apply_of_ne {i i' k : Fin K} (h1 : k ≠ i) (h2 : k ≠ i') :
    twoDiff i i' k = 0 := by
  simp [twoDiff, incf_of_ne _ h2, incf_of_ne _ h1]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem qOne_twoSame (i : Fin K) :
    qOne θ π (twoSame i) = θ * π i * (θ * π i + 1) / (θ * (θ + 1)) := by
  have hsum : ∑ k, twoSame i k = 2 := by
    simp [twoSame, sum_incf]
  have hprod : ∏ k, rising (θ * π k) (twoSame i k) = θ * π i * (θ * π i + 1) := by
    have h1 := Biallelic.prod_rising_incf (fun k => θ * π k) (incf (fun _ => 0) i) i
    rw [twoSame, h1, prod_rising_e, incf_self]
    norm_num
  rw [qOne, hsum, hprod, rising_two]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem qOne_twoDiff {i i' : Fin K} (h : i ≠ i') :
    qOne θ π (twoDiff i i') = θ * π i * (θ * π i') / (θ * (θ + 1)) := by
  have hsum : ∑ k, twoDiff i i' k = 2 := by
    simp [twoDiff, sum_incf]
  have hprod : ∏ k, rising (θ * π k) (twoDiff i i' k) = θ * π i * (θ * π i') := by
    have h1 := Biallelic.prod_rising_incf (fun k => θ * π k) (incf (fun _ => 0) i) i'
    rw [twoDiff, h1, prod_rising_e, incf_of_ne _ (Ne.symm h)]
    norm_num
  rw [qOne, hsum, hprod, rising_two]

theorem G_twoSame (hθ : 0 < θ) (i : Fin K) :
    Gval θ π (twoSame i) = -(θ * Uval π i i) / (θ + 1) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθ1 : θ + 1 ≠ 0 := by positivity
  have hsum : (∑ k, ((Nat.choose (twoSame i k) 2 : ℕ) : F) * qOne θ π (decf (twoSame i) k))
      = π i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [twoSame_apply_self, decf_twoSame, qOne_eA hθ0]
      norm_num
    · intro k _ hk
      rw [twoSame_apply_of_ne hk]
      norm_num
  rw [Gval, hsum, qOne_twoSame, Uval, ite_eq_left rfl]
  field_simp
  ring

theorem G_twoDiff (hθ : 0 < θ) {i i' : Fin K} (h : i ≠ i') :
    Gval θ π (twoDiff i i') = -(θ * Uval π i i') / (θ + 1) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθ1 : θ + 1 ≠ 0 := by positivity
  have hsum : (∑ k, ((Nat.choose (twoDiff i i' k) 2 : ℕ) : F) * qOne θ π (decf (twoDiff i i') k))
      = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : k = i
    · subst h1; rw [twoDiff_apply_left h]; norm_num
    by_cases h2 : k = i'
    · subst h2; rw [twoDiff_apply_right h]; norm_num
    · rw [twoDiff_apply_of_ne h1 h2]; norm_num
  rw [Gval, hsum, qOne_twoDiff h, Uval, ite_eq_right h]
  field_simp
  ring

variable {θA θB ρ : F}

theorem G_mul_G (hθA : 0 < θA) (hθB : 0 < θB) (UA UB : F) :
    (-(θA * UA) / (θA + 1)) * (-(θB * UB) / (θB + 1))
      = θA * θB * (UA * UB) / ((θA + 1) * (θB + 1)) := by
  have h1 : θA + 1 ≠ 0 := by positivity
  have h2 : θB + 1 ≠ 0 := by positivity
  field_simp

def kappa (θA θB ρ : F) (t : ℕ) : F :=
  θA * θB * wn θA θB ρ t / (2 * ((θA + 1) * (θB + 1)) * Eblock θA θB ρ)

theorem kappa_mul (hθA : 0 < θA) (hθB : 0 < θB) (hE : Eblock θA θB ρ ≠ 0) (UA UB : F) (t : ℕ) :
    (θA * θB * (UA * UB) / ((θA + 1) * (θB + 1))) * gf θA θB ρ t = kappa θA θB ρ t * (UA * UB) := by
  have h1 : θA + 1 ≠ 0 := by positivity
  have h2 : θB + 1 ≠ 0 := by positivity
  rw [kappa, gf]
  field_simp

theorem kappa_zero (hθA : 0 < θA) (hθB : 0 < θB) (hE : Eblock θA θB ρ ≠ 0) :
    kappa θA θB ρ 0 = θA * θB * 8 / ((θA + 1) * (θB + 1) * Eblock θA θB ρ) := by
  have h1 : θA + 1 ≠ 0 := by positivity
  have h2 : θB + 1 ≠ 0 := by positivity
  rw [kappa, wn]
  field_simp
  ring

theorem kappa_one (hθA : 0 < θA) (hθB : 0 < θB) (hE : Eblock θA θB ρ ≠ 0) :
    kappa θA θB ρ 1
      = θA * θB * (2 * (θA + θB + 6)) / ((θA + 1) * (θB + 1) * Eblock θA θB ρ) := by
  have h1 : θA + 1 ≠ 0 := by positivity
  have h2 : θB + 1 ≠ 0 := by positivity
  rw [kappa, wn]
  field_simp
  ring

theorem kappa_two (hθA : 0 < θA) (hθB : 0 < θB) (hE : Eblock θA θB ρ ≠ 0) :
    kappa θA θB ρ 2
      = θA * θB * ((θA + θB + 2) * ρ + 2 * (θA + θB + 3) * (θA + θB + 6))
        / ((θA + 1) * (θB + 1) * Eblock θA θB ρ) := by
  have h1 : θA + 1 ≠ 0 := by positivity
  have h2 : θB + 1 ≠ 0 := by positivity
  rw [kappa, wn]
  field_simp
  ring

end Rhone.MarkovChain.ClosedForms
