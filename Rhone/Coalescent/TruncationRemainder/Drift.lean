/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.TruncationRemainder.Unbounded
public import Rhone.Coalescent.TwoLocusGenealogy.Bounds

/-! # Drift bound for the two-locus selection model and its truncation remainder -/

@[expose] public section

namespace Rhone.Coalescent.TruncationRemainder

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ}

section Constants

def Theta (θA θB pA pB : ℝ) : ℝ := θA * (1 - pA) + θB * (1 - pB)

def SigmaD (θA θB ρ : ℝ) : ℝ := θA + θB + ρ

def muTheta (θA θB : ℝ) : ℝ := min θA θB

noncomputable def deltaStar (θA θB ρ pA pB z : ℝ) : ℝ :=
  min (1 - 1 / z) ((Theta θA θB pA pB - ρ * (z - 1)) / SigmaD θA θB ρ)

noncomputable def cUconst (θA θB z : ℝ) : ℝ := (1 + z) / muTheta θA θB

noncomputable def rStar (θA θB ρ pA pB z : ℝ) : ℝ :=
  deltaStar θA θB ρ pA pB z * muTheta θA θB / (1 + z)

theorem rStar_eq_div (θA θB ρ pA pB z : ℝ) :
    rStar θA θB ρ pA pB z = deltaStar θA θB ρ pA pB z / cUconst θA θB z := by
  rw [rStar, cUconst, div_div_eq_mul_div]

def Vz (z : ℝ) (ξ : Config KA KB) : ℝ := z ^ ξ.n

theorem Vz_pos {z : ℝ} (hz : 0 < z) (ξ : Config KA KB) : 0 < Vz z ξ := pow_pos hz _

theorem Vz_nonneg {z : ℝ} (hz : 0 ≤ z) (ξ : Config KA KB) : 0 ≤ Vz z ξ := pow_nonneg hz _

end Constants

section PiStar

variable {K : ℕ} [Nonempty (Fin K)]

noncomputable def piStar (π : Fin K → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty π

theorem le_piStar (π : Fin K → ℝ) (i : Fin K) : π i ≤ piStar π :=
  Finset.le_sup' π (Finset.mem_univ i)

theorem piStar_le_one {π : Fin K → ℝ} (hπ : ∀ i, 0 ≤ π i) (hs : ∑ i, π i = 1) :
    piStar π ≤ 1 := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [← hs]
  exact Finset.single_le_sum (f := π) (fun j _ => hπ j) (Finset.mem_univ i)

end PiStar

section Levels

variable {θA θB ρ z : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} {ξ : Config KA KB} {m : ℕ}

private theorem Vz_dropA (hm : ξ.n = m + 1) {i : Fin KA} (h : ξ.a i ≠ 0) :
    Vz z (ξ.dropA i) = z ^ m := by
  have h1 := ξ.n_dropA i h
  have h2 : (ξ.dropA i).n = m := by omega
  simp only [Vz, h2]

private theorem Vz_dropB (hm : ξ.n = m + 1) {j : Fin KB} (h : ξ.b j ≠ 0) :
    Vz z (ξ.dropB j) = z ^ m := by
  have h1 := ξ.n_dropB j h
  have h2 : (ξ.dropB j).n = m := by omega
  simp only [Vz, h2]

private theorem Vz_dropC (hm : ξ.n = m + 1) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Vz z (ξ.dropC i j) = z ^ m := by
  have h1 := ξ.n_dropC i j h
  have h2 : (ξ.dropC i j).n = m := by omega
  simp only [Vz, h2]

private theorem Vz_mergeAB (hm : ξ.n = m + 1) {i : Fin KA} {j : Fin KB} (ha : ξ.a i ≠ 0)
    (hb : ξ.b j ≠ 0) : Vz z (ξ.mergeAB i j) = z ^ m := by
  have h1 := ξ.n_mergeAB i j ha hb
  have h2 : (ξ.mergeAB i j).n = m := by omega
  simp only [Vz, h2]

private theorem Vz_killA (hm : ξ.n = m + 1) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Vz z (ξ.killA i j) = z ^ (m + 1) := by
  have h1 := ξ.n_killA i j h
  have h2 : (ξ.killA i j).n = m + 1 := by omega
  simp only [Vz, h2]

private theorem Vz_killB (hm : ξ.n = m + 1) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Vz z (ξ.killB i j) = z ^ (m + 1) := by
  have h1 := ξ.n_killB i j h
  have h2 : (ξ.killB i j).n = m + 1 := by omega
  simp only [Vz, h2]

private theorem Vz_split (hm : ξ.n = m + 1) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Vz z (ξ.split i j) = z ^ (m + 2) := by
  have h1 := ξ.n_split i j h
  have h2 : (ξ.split i j).n = m + 2 := by omega
  simp only [Vz, h2]

theorem rhs_Vz_eq (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (z : ℝ)
    (ξ : Config KA KB) (m : ℕ) (hm : ξ.n = m + 1) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB (Vz z) ξ
      = (((∑ i, ξ.coalA i) + (∑ j, ξ.coalB j) + (∑ i, ∑ j, ξ.coalC i j)
            + (∑ i, ∑ j, ξ.coalAB i j) : ℕ) : ℝ) * z ^ m
        + θA * (∑ i, πA i * ((ξ.a i : ℕ) : ℝ)) * z ^ m
        + θB * (∑ j, πB j * ((ξ.b j : ℕ) : ℝ)) * z ^ m
        + θA * (∑ i, πA i * ((ξ.cRow i : ℕ) : ℝ)) * z ^ (m + 1)
        + θB * (∑ j, πB j * ((ξ.cCol j : ℕ) : ℝ)) * z ^ (m + 1)
        + ρ * ((ξ.t : ℕ) : ℝ) * z ^ (m + 2) := by
  have e1 : (∑ i, ((ξ.coalA i : ℕ) : ℝ) * Vz z (ξ.dropA i))
      = ((∑ i, ξ.coalA i : ℕ) : ℝ) * z ^ m := by
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ξ.a i = 0
    · rw [ξ.coalA_eq_zero_of h]; simp
    · rw [Vz_dropA hm h]
  have e2 : (∑ j, ((ξ.coalB j : ℕ) : ℝ) * Vz z (ξ.dropB j))
      = ((∑ j, ξ.coalB j : ℕ) : ℝ) * z ^ m := by
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ξ.b j = 0
    · rw [ξ.coalB_eq_zero_of h]; simp
    · rw [Vz_dropB hm h]
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * Vz z (ξ.dropC i j))
      = ((∑ i, ∑ j, ξ.coalC i j : ℕ) : ℝ) * z ^ m := by
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ξ.c i j = 0
    · rw [ξ.coalC_eq_zero_of h]; simp
    · rw [Vz_dropC hm h]
  have e4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * Vz z (ξ.mergeAB i j))
      = ((∑ i, ∑ j, ξ.coalAB i j : ℕ) : ℝ) * z ^ m := by
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases ha : ξ.a i = 0
    · rw [ξ.coalAB_eq_zero_left j ha]; simp
    · by_cases hb : ξ.b j = 0
      · rw [ξ.coalAB_eq_zero_right i hb]; simp
      · rw [Vz_mergeAB hm ha hb]
  have e5 : (∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * Vz z (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : ℝ) * Vz z (ξ.killA i j)))
      = (∑ i, πA i * ((ξ.a i : ℕ) : ℝ)) * z ^ m
        + (∑ i, πA i * ((ξ.cRow i : ℕ) : ℝ)) * z ^ (m + 1) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : ((ξ.a i : ℕ) : ℝ) * Vz z (ξ.dropA i) = ((ξ.a i : ℕ) : ℝ) * z ^ m := by
      by_cases h : ξ.a i = 0
      · rw [h]; simp
      · rw [Vz_dropA hm h]
    have hc : (∑ j, ((ξ.c i j : ℕ) : ℝ) * Vz z (ξ.killA i j))
        = ((ξ.cRow i : ℕ) : ℝ) * z ^ (m + 1) := by
      rw [Config.cRow, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : ξ.c i j = 0
      · rw [h]; simp
      · rw [Vz_killA hm h]
    rw [ha, hc]; ring
  have e6 : (∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * Vz z (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : ℝ) * Vz z (ξ.killB i j)))
      = (∑ j, πB j * ((ξ.b j : ℕ) : ℝ)) * z ^ m
        + (∑ j, πB j * ((ξ.cCol j : ℕ) : ℝ)) * z ^ (m + 1) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hb : ((ξ.b j : ℕ) : ℝ) * Vz z (ξ.dropB j) = ((ξ.b j : ℕ) : ℝ) * z ^ m := by
      by_cases h : ξ.b j = 0
      · rw [h]; simp
      · rw [Vz_dropB hm h]
    have hc : (∑ i, ((ξ.c i j : ℕ) : ℝ) * Vz z (ξ.killB i j))
        = ((ξ.cCol j : ℕ) : ℝ) * z ^ (m + 1) := by
      rw [Config.cCol, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : ξ.c i j = 0
      · rw [h]; simp
      · rw [Vz_killB hm h]
    rw [hb, hc]; ring
  have e7 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * Vz z (ξ.split i j))
      = ((ξ.t : ℕ) : ℝ) * z ^ (m + 2) := by
    rw [Config.t, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ξ.c i j = 0
    · rw [h]; simp
    · rw [Vz_split hm h]
  rw [LinearAlgebra.Recursion.rhs, e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring

end Levels

section Arith

theorem drift_arith {Q A B T z δ θA θB ρ pA pB : ℝ}
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 ≤ z) (hδz : δ * z ≤ z - 1)
    (hdS : δ * (θA + θB + ρ) ≤ θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1)) (m : ℕ) :
    (Q + θA * pA * A + θB * pB * B) * z ^ m
        + (θA * pA + θB * pB) * T * z ^ (m + 1) + ρ * T * z ^ (m + 2)
      ≤ (1 - δ) * (Q + θA * (A + T) + θB * (B + T) + ρ * T) * z ^ (m + 1) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hzm : (0 : ℝ) ≤ z ^ m := by positivity
  have t1 : δ * z * Q ≤ (z - 1) * Q := mul_le_mul_of_nonneg_right hδz hQ
  have t2 : δ * z * (θA * A) ≤ (z - pA) * (θA * A) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hθA hA)
  have t3 : δ * z * (θB * B) ≤ (z - pB) * (θB * B) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hθB hB)
  have t4 : δ * (θA + θB + ρ) * (z * T)
      ≤ (θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1)) * (z * T) :=
    mul_le_mul_of_nonneg_right hdS (mul_nonneg hz0.le hT)
  have hmain : Q + θA * pA * A + θB * pB * B + (θA * pA + θB * pB) * T * z + ρ * T * (z * z)
      ≤ (1 - δ) * (Q + θA * (A + T) + θB * (B + T) + ρ * T) * z := by linarith
  calc (Q + θA * pA * A + θB * pB * B) * z ^ m
        + (θA * pA + θB * pB) * T * z ^ (m + 1) + ρ * T * z ^ (m + 2)
      = z ^ m * (Q + θA * pA * A + θB * pB * B
          + (θA * pA + θB * pB) * T * z + ρ * T * (z * z)) := by ring
    _ ≤ z ^ m * ((1 - δ) * (Q + θA * (A + T) + θB * (B + T) + ρ * T) * z) :=
        mul_le_mul_of_nonneg_left hmain hzm
    _ = (1 - δ) * (Q + θA * (A + T) + θB * (B + T) + ρ * T) * z ^ (m + 1) := by ring

end Arith

section Drift

variable {θA θB ρ z δ pA pB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem diag_eq_groups (θA θB ρ : ℝ) (ξ : Config KA KB) :
    LinearAlgebra.Recursion.diag θA θB ρ ξ
      = ((ξ.n * (ξ.n - 1) : ℕ) : ℝ) + θA * (((ξ.sumA : ℕ) : ℝ) + ((ξ.t : ℕ) : ℝ))
        + θB * (((ξ.sumB : ℕ) : ℝ) + ((ξ.t : ℕ) : ℝ)) + ρ * ((ξ.t : ℕ) : ℝ) := by
  rw [LinearAlgebra.Recursion.diag, Config.nA, Config.nB]
  push_cast
  ring

theorem drift_le (hθA : 0 ≤ θA) (hθB : 0 ≤ θB)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 ≤ z) (hδz : δ * z ≤ z - 1)
    (hdS : δ * (θA + θB + ρ) ≤ θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1))
    (ξ : Config KA KB) (m : ℕ) (hm : ξ.n = m + 1) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB (Vz z) ξ ≤ (1 - δ) * LinearAlgebra.Recursion.diag θA
        θB ρ ξ * Vz z ξ := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hzm : (0 : ℝ) ≤ z ^ m := by positivity
  have hzm1 : (0 : ℝ) ≤ z ^ (m + 1) := by positivity
  have hV : Vz z ξ = z ^ (m + 1) := by simp only [Vz, hm]
  have b0 : (((∑ i, ξ.coalA i) + (∑ j, ξ.coalB j) + (∑ i, ∑ j, ξ.coalC i j)
      + (∑ i, ∑ j, ξ.coalAB i j) : ℕ) : ℝ) ≤ ((ξ.n * (ξ.n - 1) : ℕ) : ℝ) := by
    exact_mod_cast TwoLocusGenealogy.coal_total_le ξ
  have b1 : (∑ i, πA i * ((ξ.a i : ℕ) : ℝ)) ≤ pA * ((ξ.sumA : ℕ) : ℝ) := by
    calc (∑ i, πA i * ((ξ.a i : ℕ) : ℝ)) ≤ ∑ i, pA * ((ξ.a i : ℕ) : ℝ) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hπA i) (Nat.cast_nonneg _)
      _ = pA * ((ξ.sumA : ℕ) : ℝ) := by rw [← Finset.mul_sum, Config.sumA, Nat.cast_sum]
  have b2 : (∑ j, πB j * ((ξ.b j : ℕ) : ℝ)) ≤ pB * ((ξ.sumB : ℕ) : ℝ) := by
    calc (∑ j, πB j * ((ξ.b j : ℕ) : ℝ)) ≤ ∑ j, pB * ((ξ.b j : ℕ) : ℝ) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hπB j) (Nat.cast_nonneg _)
      _ = pB * ((ξ.sumB : ℕ) : ℝ) := by rw [← Finset.mul_sum, Config.sumB, Nat.cast_sum]
  have b3 : (∑ i, πA i * ((ξ.cRow i : ℕ) : ℝ)) ≤ pA * ((ξ.t : ℕ) : ℝ) := by
    calc (∑ i, πA i * ((ξ.cRow i : ℕ) : ℝ)) ≤ ∑ i, pA * ((ξ.cRow i : ℕ) : ℝ) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hπA i) (Nat.cast_nonneg _)
      _ = pA * ((ξ.t : ℕ) : ℝ) := by
          rw [← Finset.mul_sum, Config.t_eq_sum_cRow, Nat.cast_sum]
  have b4 : (∑ j, πB j * ((ξ.cCol j : ℕ) : ℝ)) ≤ pB * ((ξ.t : ℕ) : ℝ) := by
    calc (∑ j, πB j * ((ξ.cCol j : ℕ) : ℝ)) ≤ ∑ j, pB * ((ξ.cCol j : ℕ) : ℝ) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hπB j) (Nat.cast_nonneg _)
      _ = pB * ((ξ.t : ℕ) : ℝ) := by
          rw [← Finset.mul_sum, Config.t_eq_sum_cCol, Nat.cast_sum]
  rw [rhs_Vz_eq θA θB ρ πA πB z ξ m hm, diag_eq_groups, hV]
  have c0 := mul_le_mul_of_nonneg_right b0 hzm
  have c1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hθA) hzm
  have c2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hθB) hzm
  have c3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b3 hθA) hzm1
  have c4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b4 hθB) hzm1
  have hcore := drift_arith (Q := ((ξ.n * (ξ.n - 1) : ℕ) : ℝ)) (A := ((ξ.sumA : ℕ) : ℝ))
    (B := ((ξ.sumB : ℕ) : ℝ)) (T := ((ξ.t : ℕ) : ℝ)) (z := z) (δ := δ) (θA := θA) (θB := θB)
    (ρ := ρ) (pA := pA) (pB := pB) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hθA hθB hpA hpB hz hδz hdS m
  linarith

end Drift

section DeltaStar

variable {θA θB ρ z pA pB : ℝ}

theorem deltaStar_mul_le (hz : 1 < z) :
    deltaStar θA θB ρ pA pB z * z ≤ z - 1 := by
  have hz0 : (0 : ℝ) < z := by linarith
  have h : deltaStar θA θB ρ pA pB z ≤ 1 - 1 / z := min_le_left _ _
  have := mul_le_mul_of_nonneg_right h hz0.le
  have he : (1 - 1 / z) * z = z - 1 := by field_simp
  linarith [he ▸ this]

theorem deltaStar_mul_SigmaD_le (hSD : 0 < SigmaD θA θB ρ) :
    deltaStar θA θB ρ pA pB z * SigmaD θA θB ρ
      ≤ Theta θA θB pA pB - ρ * (z - 1) := by
  have h : deltaStar θA θB ρ pA pB z
      ≤ (Theta θA θB pA pB - ρ * (z - 1)) / SigmaD θA θB ρ := min_le_right _ _
  have := mul_le_mul_of_nonneg_right h hSD.le
  rwa [div_mul_cancel₀ _ (ne_of_gt hSD)] at this

theorem deltaStar_le_one (hz : 1 < z) : deltaStar θA θB ρ pA pB z ≤ 1 := by
  have hz0 : (0 : ℝ) < z := by linarith
  have h : deltaStar θA θB ρ pA pB z ≤ 1 - 1 / z := min_le_left _ _
  have : (0 : ℝ) < 1 / z := by positivity
  linarith

theorem deltaStar_pos (hz : 1 < z) (hSD : 0 < SigmaD θA θB ρ)
    (hadm : ρ * (z - 1) < Theta θA θB pA pB) : 0 < deltaStar θA θB ρ pA pB z := by
  have hz0 : (0 : ℝ) < z := by linarith
  refine lt_min ?_ ?_
  · have : 1 / z < 1 := by
      rw [div_lt_one hz0]; exact hz
    linarith
  · exact div_pos (by linarith) hSD

end DeltaStar

section Resolvent

variable {θA θB ρ z : ℝ}

theorem muTheta_mul_n_le_diag (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) : muTheta θA θB * ((ξ.n : ℕ) : ℝ) ≤ LinearAlgebra.Recursion.diag θA θB ρ ξ :=
        by
  have hμ0 : 0 ≤ muTheta θA θB := le_min hθA hθB
  have hμA : muTheta θA θB ≤ θA := min_le_left _ _
  have hμB : muTheta θA θB ≤ θB := min_le_right _ _
  have hnAB : ((ξ.n : ℕ) : ℝ) ≤ ((ξ.nA : ℕ) : ℝ) + ((ξ.nB : ℕ) : ℝ) := by
    have h := ξ.n_add_t
    have h' : ξ.n ≤ ξ.nA + ξ.nB := by omega
    exact_mod_cast h'
  have h1 : muTheta θA θB * ((ξ.nA : ℕ) : ℝ) ≤ θA * ((ξ.nA : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hμA (Nat.cast_nonneg _)
  have h2 : muTheta θA θB * ((ξ.nB : ℕ) : ℝ) ≤ θB * ((ξ.nB : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hμB (Nat.cast_nonneg _)
  have h3 : (0 : ℝ) ≤ ((ξ.n * (ξ.n - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ρ * ((ξ.t : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
  have h5 : muTheta θA θB * ((ξ.n : ℕ) : ℝ)
      ≤ muTheta θA θB * (((ξ.nA : ℕ) : ℝ) + ((ξ.nB : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hnAB hμ0
  rw [LinearAlgebra.Recursion.diag]
  linarith

theorem muTheta_le_diag (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB)
    (hn : 1 ≤ ξ.n) : muTheta θA θB ≤ LinearAlgebra.Recursion.diag θA θB ρ ξ := by
  have hμ0 : 0 ≤ muTheta θA θB := le_min hθA hθB
  have h := muTheta_mul_n_le_diag hθA hθB hρ ξ
  have h1 : (1 : ℝ) ≤ ((ξ.n : ℕ) : ℝ) := by exact_mod_cast hn
  nlinarith [h, h1, hμ0]

theorem diag_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB)
    (hn : 1 ≤ ξ.n) : 0 < LinearAlgebra.Recursion.diag θA θB ρ ξ :=
  lt_of_lt_of_le (lt_min hθA hθB) (muTheta_le_diag hθA.le hθB.le hρ ξ hn)

theorem diag_eA (θA θB ρ : ℝ) (i : Fin KA) :
    LinearAlgebra.Recursion.diag θA θB ρ (Config.eA i : Config KA KB) = θA := by
  have h1 : (Config.eA i : Config KA KB).n = 1 := Config.n_eA i
  have h2 : (Config.eA i : Config KA KB).nA = 1 := by
    simp [Config.nA, Config.sumA, Config.t, Config.eA, sum_incf]
  have h3 : (Config.eA i : Config KA KB).nB = 0 := by
    simp [Config.nB, Config.sumB, Config.t, Config.eA]
  have h4 : (Config.eA i : Config KA KB).t = 0 := by simp [Config.t, Config.eA]
  rw [LinearAlgebra.Recursion.diag, h1, h2, h3, h4]
  norm_num

theorem diag_eB (θA θB ρ : ℝ) (j : Fin KB) :
    LinearAlgebra.Recursion.diag θA θB ρ (Config.eB j : Config KA KB) = θB := by
  have h1 : (Config.eB j : Config KA KB).n = 1 := Config.n_eB j
  have h2 : (Config.eB j : Config KA KB).nA = 0 := by
    simp [Config.nA, Config.sumA, Config.t, Config.eB]
  have h3 : (Config.eB j : Config KA KB).nB = 1 := by
    simp [Config.nB, Config.sumB, Config.t, Config.eB, sum_incf]
  have h4 : (Config.eB j : Config KA KB).t = 0 := by simp [Config.t, Config.eB]
  rw [LinearAlgebra.Recursion.diag, h1, h2, h3, h4]
  norm_num

end Resolvent

section SelBound

variable {θA θB ρ z : ℝ}

theorem mA_add_sumB_le_n (ξ : Config KA KB) (i₀ : Fin KA) : ξ.mA i₀ + ξ.sumB ≤ ξ.n := by
  have h1 : ξ.a i₀ ≤ ξ.sumA := by
    rw [Config.sumA]
    exact Finset.single_le_sum (f := ξ.a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  have h2 : ξ.cRow i₀ ≤ ξ.t := by
    rw [Config.t_eq_sum_cRow]
    exact Finset.single_le_sum (f := ξ.cRow) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  simp only [Config.mA, Config.n]
  omega

theorem sel_ratio_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hz : 0 ≤ z)
    (i₀ : Fin KA) (ξ : Config KA KB) :
    ((ξ.mA i₀ : ℕ) : ℝ) + ((ξ.sumB : ℕ) : ℝ) + ((ξ.n : ℕ) : ℝ) * z
      ≤ cUconst θA θB z * LinearAlgebra.Recursion.diag θA θB ρ ξ := by
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  have h1 : ((ξ.mA i₀ : ℕ) : ℝ) + ((ξ.sumB : ℕ) : ℝ) ≤ ((ξ.n : ℕ) : ℝ) := by
    exact_mod_cast mA_add_sumB_le_n ξ i₀
  have h2 := muTheta_mul_n_le_diag hθA.le hθB.le hρ ξ
  have h3 : (0 : ℝ) ≤ 1 + z := by linarith
  rw [cUconst, div_mul_eq_mul_div, le_div_iff₀ hμ]
  calc (((ξ.mA i₀ : ℕ) : ℝ) + ((ξ.sumB : ℕ) : ℝ) + ((ξ.n : ℕ) : ℝ) * z) * muTheta θA θB
      ≤ (((ξ.n : ℕ) : ℝ) * (1 + z)) * muTheta θA θB := by
        refine mul_le_mul_of_nonneg_right ?_ hμ.le
        linarith [h1]
    _ = (1 + z) * (muTheta θA θB * ((ξ.n : ℕ) : ℝ)) := by ring
    _ ≤ (1 + z) * LinearAlgebra.Recursion.diag θA θB ρ ξ := mul_le_mul_of_nonneg_left h2 h3

theorem sel_ratio_eq_eA (hθA : 0 < θA) (h : θA ≤ θB) (i₀ : Fin KA) :
    (((Config.eA i₀ : Config KA KB).mA i₀ : ℕ) : ℝ)
        + (((Config.eA i₀ : Config KA KB).sumB : ℕ) : ℝ)
        + (((Config.eA i₀ : Config KA KB).n : ℕ) : ℝ) * z
      = cUconst θA θB z * LinearAlgebra.Recursion.diag θA θB ρ (Config.eA i₀ : Config KA KB) := by
  have hθ0 : θA ≠ 0 := ne_of_gt hθA
  have hm : ((Config.eA i₀ : Config KA KB).mA i₀) = 1 := by
    simp [Config.mA, Config.cRow, Config.eA, incf_self]
  have hs : ((Config.eA i₀ : Config KA KB).sumB) = 0 := by simp [Config.sumB, Config.eA]
  have hn : ((Config.eA i₀ : Config KA KB).n) = 1 := Config.n_eA i₀
  rw [hm, hs, hn, diag_eA, cUconst, muTheta, min_eq_left h]
  push_cast
  field_simp
  ring

theorem sel_ratio_eq_eB (hθB : 0 < θB) (h : θB ≤ θA) (i₀ : Fin KA) (j₀ : Fin KB) :
    (((Config.eB j₀ : Config KA KB).mA i₀ : ℕ) : ℝ)
        + (((Config.eB j₀ : Config KA KB).sumB : ℕ) : ℝ)
        + (((Config.eB j₀ : Config KA KB).n : ℕ) : ℝ) * z
      = cUconst θA θB z * LinearAlgebra.Recursion.diag θA θB ρ (Config.eB j₀ : Config KA KB) := by
  have hθ0 : θB ≠ 0 := ne_of_gt hθB
  have hm : ((Config.eB j₀ : Config KA KB).mA i₀) = 0 := by
    simp [Config.mA, Config.cRow, Config.eB]
  have hs : ((Config.eB j₀ : Config KA KB).sumB) = 1 := by
    simp [Config.sumB, Config.eB, sum_incf]
  have hn : ((Config.eB j₀ : Config KA KB).n) = 1 := Config.n_eB j₀
  rw [hm, hs, hn, diag_eB, cUconst, muTheta, min_eq_right h]
  push_cast
  field_simp
  ring

end SelBound

section Kernel

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

private theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (f g : ι → ℝ) (h : ∀ i, |f i| ≤ g i) : |∑ i, c i * f i| ≤ ∑ i, c i * g i := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (hc i)]
  exact mul_le_mul_of_nonneg_left (h i) (hc i)

private theorem abs_add7_le {a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : ℝ}
    (h1 : |a1| ≤ b1) (h2 : |a2| ≤ b2) (h3 : |a3| ≤ b3) (h4 : |a4| ≤ b4) (h5 : |a5| ≤ b5)
    (h6 : |a6| ≤ b6) (h7 : |a7| ≤ b7) :
    |a1 + a2 + a3 + a4 + a5 + a6 + a7| ≤ b1 + b2 + b3 + b4 + b5 + b6 + b7 := by
  obtain ⟨p1, q1⟩ := abs_le.mp h1
  obtain ⟨p2, q2⟩ := abs_le.mp h2
  obtain ⟨p3, q3⟩ := abs_le.mp h3
  obtain ⟨p4, q4⟩ := abs_le.mp h4
  obtain ⟨p5, q5⟩ := abs_le.mp h5
  obtain ⟨p6, q6⟩ := abs_le.mp h6
  obtain ⟨p7, q7⟩ := abs_le.mp h7
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_rhs_le (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {f g : Config KA KB → ℝ} (hfg : ∀ η, |f η| ≤ g η)
    (ξ : Config KA KB) :
    |LinearAlgebra.Recursion.rhs θA θB ρ πA πB f ξ| ≤ LinearAlgebra.Recursion.rhs θA θB ρ πA πB g
        ξ := by
  rw [LinearAlgebra.Recursion.rhs, LinearAlgebra.Recursion.rhs]
  refine abs_add7_le ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact abs_sum_mul_le (fun i => ((ξ.coalA i : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun i => f (ξ.dropA i)) (fun i => g (ξ.dropA i)) fun _ => hfg _
  · exact abs_sum_mul_le (fun j => ((ξ.coalB j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun j => f (ξ.dropB j)) (fun j => g (ξ.dropB j)) fun _ => hfg _
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact abs_sum_mul_le (fun j => ((ξ.coalC i j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun j => f (ξ.dropC i j)) (fun j => g (ξ.dropC i j)) fun _ => hfg _
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact abs_sum_mul_le (fun j => ((ξ.coalAB i j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun j => f (ξ.mergeAB i j)) (fun j => g (ξ.mergeAB i j)) fun _ => hfg _
  · rw [abs_mul, abs_of_nonneg hθA]
    refine mul_le_mul_of_nonneg_left ?_ hθA
    refine abs_sum_mul_le πA hπA _ _ fun i => ?_
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hfg _) (Nat.cast_nonneg _)
    · exact abs_sum_mul_le (fun j => ((ξ.c i j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
        (fun j => f (ξ.killA i j)) (fun j => g (ξ.killA i j)) fun _ => hfg _
  · rw [abs_mul, abs_of_nonneg hθB]
    refine mul_le_mul_of_nonneg_left ?_ hθB
    refine abs_sum_mul_le πB hπB _ _ fun j => ?_
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hfg _) (Nat.cast_nonneg _)
    · exact abs_sum_mul_le (fun i => ((ξ.c i j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
        (fun i => f (ξ.killB i j)) (fun i => g (ξ.killB i j)) fun _ => hfg _
  · rw [abs_mul, abs_of_nonneg hρ]
    refine mul_le_mul_of_nonneg_left ?_ hρ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact abs_sum_mul_le (fun j => ((ξ.c i j : ℕ) : ℝ)) (fun _ => Nat.cast_nonneg _)
      (fun j => f (ξ.split i j)) (fun j => g (ξ.split i j)) fun _ => hfg _

private theorem sum_mul_add {ι : Type*} [Fintype ι] (c f g : ι → ℝ) :
    (∑ i, c i * (f i + g i)) = (∑ i, c i * f i) + ∑ i, c i * g i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem sum_mul_smul {ι : Type*} [Fintype ι] (a : ℝ) (c f : ι → ℝ) :
    (∑ i, c i * (a * f i)) = a * ∑ i, c i * f i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem rhs_add (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (f g : Config KA KB → ℝ) (ξ : Config KA KB) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB (fun η => f η + g η) ξ
      = LinearAlgebra.Recursion.rhs θA θB ρ πA πB f ξ + LinearAlgebra.Recursion.rhs θA θB ρ πA πB g
          ξ := by
  have g1 := sum_mul_add (fun i => ((ξ.coalA i : ℕ) : ℝ)) (fun i => f (ξ.dropA i))
    (fun i => g (ξ.dropA i))
  have g2 := sum_mul_add (fun j => ((ξ.coalB j : ℕ) : ℝ)) (fun j => f (ξ.dropB j))
    (fun j => g (ξ.dropB j))
  have g3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * (f (ξ.dropC i j) + g (ξ.dropC i j)))
      = (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * f (ξ.dropC i j))
        + ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * g (ξ.dropC i j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      sum_mul_add (fun j => ((ξ.coalC i j : ℕ) : ℝ)) _ _
  have g4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * (f (ξ.mergeAB i j) + g (ξ.mergeAB i j)))
      = (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * f (ξ.mergeAB i j))
        + ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * g (ξ.mergeAB i j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      sum_mul_add (fun j => ((ξ.coalAB i j : ℕ) : ℝ)) _ _
  have g5 : (∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * (f (ξ.dropA i) + g (ξ.dropA i))
        + ∑ j, ((ξ.c i j : ℕ) : ℝ) * (f (ξ.killA i j) + g (ξ.killA i j))))
      = (∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * f (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : ℝ) * f (ξ.killA i j)))
        + ∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * g (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : ℝ) * g (ξ.killA i j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_mul_add (fun j => ((ξ.c i j : ℕ) : ℝ))]
    ring
  have g6 : (∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * (f (ξ.dropB j) + g (ξ.dropB j))
        + ∑ i, ((ξ.c i j : ℕ) : ℝ) * (f (ξ.killB i j) + g (ξ.killB i j))))
      = (∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * f (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : ℝ) * f (ξ.killB i j)))
        + ∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * g (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : ℝ) * g (ξ.killB i j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_mul_add (fun i => ((ξ.c i j : ℕ) : ℝ))]
    ring
  have g7 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * (f (ξ.split i j) + g (ξ.split i j)))
      = (∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * f (ξ.split i j))
        + ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * g (ξ.split i j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => sum_mul_add (fun j => ((ξ.c i j : ℕ) : ℝ)) _ _
  rw [LinearAlgebra.Recursion.rhs, LinearAlgebra.Recursion.rhs, LinearAlgebra.Recursion.rhs, g1, g2,
      g3, g4, g5, g6, g7]
  ring

theorem rhs_smul (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (a : ℝ)
    (f : Config KA KB → ℝ) (ξ : Config KA KB) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB (fun η => a * f η) ξ
      = a * LinearAlgebra.Recursion.rhs θA θB ρ πA πB f ξ := by
  have g1 := sum_mul_smul a (fun i => ((ξ.coalA i : ℕ) : ℝ)) (fun i => f (ξ.dropA i))
  have g2 := sum_mul_smul a (fun j => ((ξ.coalB j : ℕ) : ℝ)) (fun j => f (ξ.dropB j))
  have g3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * (a * f (ξ.dropC i j)))
      = a * ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * f (ξ.dropC i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => sum_mul_smul a (fun j => ((ξ.coalC i j : ℕ) : ℝ)) _
  have g4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * (a * f (ξ.mergeAB i j)))
      = a * ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * f (ξ.mergeAB i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => sum_mul_smul a (fun j => ((ξ.coalAB i j : ℕ) : ℝ)) _
  have g5 : (∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * (a * f (ξ.dropA i))
        + ∑ j, ((ξ.c i j : ℕ) : ℝ) * (a * f (ξ.killA i j))))
      = a * ∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * f (ξ.dropA i)
          + ∑ j, ((ξ.c i j : ℕ) : ℝ) * f (ξ.killA i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_mul_smul a (fun j => ((ξ.c i j : ℕ) : ℝ))]
    ring
  have g6 : (∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * (a * f (ξ.dropB j))
        + ∑ i, ((ξ.c i j : ℕ) : ℝ) * (a * f (ξ.killB i j))))
      = a * ∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * f (ξ.dropB j)
          + ∑ i, ((ξ.c i j : ℕ) : ℝ) * f (ξ.killB i j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_mul_smul a (fun i => ((ξ.c i j : ℕ) : ℝ))]
    ring
  have g7 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * (a * f (ξ.split i j)))
      = a * ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * f (ξ.split i j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => sum_mul_smul a (fun j => ((ξ.c i j : ℕ) : ℝ)) _
  rw [LinearAlgebra.Recursion.rhs, LinearAlgebra.Recursion.rhs, g1, g2, g3, g4, g5, g6, g7]
  ring

theorem rhs_eq_zero_of_n_zero (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (f : Config KA KB → ℝ) (ξ : Config KA KB) (hn : ξ.n = 0) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB f ξ = 0 := by
  have hA : ξ.sumA = 0 := by simp only [Config.n] at hn; omega
  have hB : ξ.sumB = 0 := by simp only [Config.n] at hn; omega
  have hT : ξ.t = 0 := by simp only [Config.n] at hn; omega
  have ha : ∀ i, ξ.a i = 0 := fun i => by
    have h1 : ξ.a i ≤ ξ.sumA := by
      rw [Config.sumA]
      exact Finset.single_le_sum (f := ξ.a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hb : ∀ j, ξ.b j = 0 := fun j => by
    have h1 : ξ.b j ≤ ξ.sumB := by
      rw [Config.sumB]
      exact Finset.single_le_sum (f := ξ.b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hc : ∀ i j, ξ.c i j = 0 := fun i j => by
    have h1 : ξ.c i j ≤ ξ.cRow i := ξ.le_cRow i j
    have h2 : ξ.cRow i ≤ ξ.t := by
      rw [Config.t_eq_sum_cRow]
      exact Finset.single_le_sum (f := ξ.cRow) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  simp [LinearAlgebra.Recursion.rhs, Config.coalA, Config.coalB, Config.coalC, Config.coalAB, ha,
      hb, hc]

end Kernel

section Operators

variable {θA θB ρ z δ pA pB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def Tfull (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (u : Config KA KB → ℝ) (ξ : Config KA KB) : ℝ :=
  LinearAlgebra.Recursion.rhs θA θB ρ πA πB u ξ / LinearAlgebra.Recursion.diag θA θB ρ ξ

def restr (u : Config KA KB → ℝ) : Config KA KB → ℝ := fun η => if η.n = 0 then 0 else u η

noncomputable def Tplus (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (u : Config KA KB → ℝ) (ξ : Config KA KB) : ℝ := Tfull θA θB ρ πA πB (restr u) ξ

noncomputable def vplus (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ξ : Config KA KB) : ℝ :=
  Tfull θA θB ρ πA πB (fun η => if η.n = 0 then 1 else 0) ξ

noncomputable def Umodel (θA θB ρ : ℝ) (i₀ : Fin KA) (u : Config KA KB → ℝ)
    (ξ : Config KA KB) : ℝ := Analysis.TruncationRemainder.sel i₀ u ξ / LinearAlgebra.Recursion.diag
        θA θB ρ ξ

theorem diag_mul_Umodel (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA)
    (u : Config KA KB → ℝ) (ξ : Config KA KB) (hn : 1 ≤ ξ.n) :
    LinearAlgebra.Recursion.diag θA θB ρ ξ * Umodel θA θB ρ i₀ u ξ =
        Analysis.TruncationRemainder.sel i₀ u ξ := by
  have hD : LinearAlgebra.Recursion.diag θA θB ρ ξ ≠ 0 := ne_of_gt (diag_pos hθA hθB hρ ξ hn)
  rw [Umodel]
  field_simp

theorem neutralOp_eq (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (u : Config KA KB → ℝ)
    (ξ : Config KA KB) (hn : 1 ≤ ξ.n) :
    Analysis.TruncationRemainder.neutralOp θA θB ρ πA πB u ξ
      = -(LinearAlgebra.Recursion.diag θA θB ρ ξ * (u ξ - Tfull θA θB ρ πA πB u ξ)) := by
  have hD : LinearAlgebra.Recursion.diag θA θB ρ ξ ≠ 0 := ne_of_gt (diag_pos hθA hθB hρ ξ hn)
  rw [Analysis.TruncationRemainder.neutralOp, Tfull]
  field_simp
  ring

theorem Tplus_add_vplus (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (u : Config KA KB → ℝ) (ξ : Config KA KB) :
    Tplus θA θB ρ πA πB u ξ + vplus θA θB ρ πA πB ξ
      = Tfull θA θB ρ πA πB (fun η => if η.n = 0 then 1 else u η) ξ := by
  have h : (fun η : Config KA KB => if η.n = 0 then (1 : ℝ) else u η)
      = fun η => restr u η + (if η.n = 0 then (1 : ℝ) else 0) := by
    funext η; by_cases hη : η.n = 0 <;> simp [restr, hη]
  rw [Tplus, vplus, Tfull, Tfull, Tfull, h, rhs_add, add_div]

theorem dominates_Tfull (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 ≤ z) (hδ1 : δ ≤ 1) (hδz : δ * z ≤ z - 1)
    (hdS : δ * (θA + θB + ρ) ≤ θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1)) :
    Analysis.TruncationRemainder.Dominates (Vz z) (Tfull θA θB ρ πA πB) δ := by
  have hz0 : (0 : ℝ) < z := by linarith
  intro u C hC hu ξ
  by_cases hn : ξ.n = 0
  · have h0 : Tfull θA θB ρ πA πB u ξ = 0 := by
      rw [Tfull, rhs_eq_zero_of_n_zero θA θB ρ πA πB u ξ hn, zero_div]
    rw [h0, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by linarith)) (Vz_nonneg hz0.le ξ)
  · have hn1 : 1 ≤ ξ.n := Nat.pos_of_ne_zero hn
    obtain ⟨m, hm⟩ : ∃ m, ξ.n = m + 1 := ⟨ξ.n - 1, by omega⟩
    have hD : 0 < LinearAlgebra.Recursion.diag θA θB ρ ξ := diag_pos hθA hθB hρ ξ hn1
    have h1 : |LinearAlgebra.Recursion.rhs θA θB ρ πA πB u ξ|
        ≤ LinearAlgebra.Recursion.rhs θA θB ρ πA πB (fun η => C * Vz z η) ξ :=
      abs_rhs_le hθA.le hθB.le hρ hπA0 hπB0 (fun η => hu η) ξ
    have h2 : LinearAlgebra.Recursion.rhs θA θB ρ πA πB (fun η => C * Vz z η) ξ
        = C * LinearAlgebra.Recursion.rhs θA θB ρ πA πB (Vz z) ξ := rhs_smul θA θB ρ πA πB C (Vz z)
            ξ
    have h3 := drift_le (πA := πA) (πB := πB) (pA := pA) (pB := pB) (δ := δ)
      hθA.le hθB.le hπA hπB hpA hpB hz hδz hdS ξ m hm
    rw [Tfull, abs_div, abs_of_pos hD, div_le_iff₀ hD]
    calc |LinearAlgebra.Recursion.rhs θA θB ρ πA πB u ξ|
        ≤ C * LinearAlgebra.Recursion.rhs θA θB ρ πA πB (Vz z) ξ := by rw [← h2]; exact h1
      _ ≤ C * ((1 - δ) * LinearAlgebra.Recursion.diag θA θB ρ ξ * Vz z ξ) :=
          mul_le_mul_of_nonneg_left h3 hC
      _ = C * (1 - δ) * Vz z ξ * LinearAlgebra.Recursion.diag θA θB ρ ξ := by ring

theorem dominates_Tplus (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 ≤ z) (hδ1 : δ ≤ 1) (hδz : δ * z ≤ z - 1)
    (hdS : δ * (θA + θB + ρ) ≤ θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1)) :
    Analysis.TruncationRemainder.Dominates (Vz z) (Tplus θA θB ρ πA πB) δ := by
  have hz0 : (0 : ℝ) < z := by linarith
  intro u C hC hu
  refine dominates_Tfull hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz hδ1 hδz hdS (restr u) C hC ?_
  intro η
  by_cases h : η.n = 0
  · rw [restr, ite_eq_left h, abs_zero]
    exact mul_nonneg hC (Vz_nonneg hz0.le η)
  · rw [restr, ite_eq_right h]
    exact hu η

theorem isLinear_Tfull (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    Analysis.TruncationRemainder.IsLinear (Tfull θA θB ρ πA πB) := by
  refine ⟨fun u w ξ => ?_, fun a u ξ => ?_⟩
  · rw [Tfull, Tfull, Tfull, rhs_add]; ring
  · rw [Tfull, Tfull, rhs_smul]; ring

theorem isLinear_Tplus (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    Analysis.TruncationRemainder.IsLinear (Tplus θA θB ρ πA πB) := by
  refine ⟨fun u w ξ => ?_, fun a u ξ => ?_⟩
  · have h : restr (fun j => u j + w j) = fun j => restr u j + restr w j := by
      funext j; by_cases hj : j.n = 0 <;> simp [restr, hj]
    rw [Tplus, Tplus, Tplus, h]
    exact (isLinear_Tfull θA θB ρ πA πB).map_add _ _ ξ
  · have h : restr (fun j => a * u j) = fun j => a * restr u j := by
      funext j; by_cases hj : j.n = 0 <;> simp [restr, hj]
    rw [Tplus, Tplus, h]
    exact (isLinear_Tfull θA θB ρ πA πB).map_smul _ _ ξ

theorem sel_add (i₀ : Fin KA) (u w : Config KA KB → ℝ) (ξ : Config KA KB) :
    Analysis.TruncationRemainder.sel i₀ (fun j => u j + w j) ξ = Analysis.TruncationRemainder.sel i₀
        u ξ + Analysis.TruncationRemainder.sel i₀ w ξ := by
  have h := sum_mul_add (fun j => ((ξ.b j : ℕ) : ℝ))
      (fun j => u (Analysis.TruncationRemainder.bToC ξ i₀ j))
    (fun j => w (Analysis.TruncationRemainder.bToC ξ i₀ j))
  simp only [Analysis.TruncationRemainder.sel]
  rw [h]
  ring

theorem sel_smul (i₀ : Fin KA) (a : ℝ) (u : Config KA KB → ℝ) (ξ : Config KA KB) :
    Analysis.TruncationRemainder.sel i₀ (fun j => a * u j) ξ = a * Analysis.TruncationRemainder.sel
        i₀ u ξ := by
  have h := sum_mul_smul a (fun j => ((ξ.b j : ℕ) : ℝ))
      (fun j => u (Analysis.TruncationRemainder.bToC ξ i₀ j))
  simp only [Analysis.TruncationRemainder.sel]
  rw [h]
  ring

theorem isLinear_Umodel (θA θB ρ : ℝ) (i₀ : Fin KA) :
    Analysis.TruncationRemainder.IsLinear
        (Umodel θA θB ρ i₀ : (Config KA KB → ℝ) → Config KA KB → ℝ) := by
  refine ⟨fun u w ξ => ?_, fun a u ξ => ?_⟩
  · rw [Umodel, Umodel, Umodel, sel_add]; ring
  · rw [Umodel, Umodel, sel_smul]; ring

theorem uBounded_Umodel (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hz : 1 ≤ z)
    (i₀ : Fin KA) :
    Analysis.TruncationRemainder.UBoundedBy (Vz z)
        (Umodel θA θB ρ i₀ : (Config KA KB → ℝ) → Config KA KB → ℝ)
      (cUconst θA θB z) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  have hcU0 : 0 ≤ cUconst θA θB z := by
    rw [cUconst]; positivity
  intro u C hC hu ξ
  by_cases hn : ξ.n = 0
  · have hA : ξ.sumA = 0 := by simp only [Config.n] at hn; omega
    have hB : ξ.sumB = 0 := by simp only [Config.n] at hn; omega
    have hT : ξ.t = 0 := by simp only [Config.n] at hn; omega
    have hmA : ξ.mA i₀ = 0 := by
      have h1 : ξ.a i₀ ≤ ξ.sumA := by
        rw [Config.sumA]
        exact Finset.single_le_sum (f := ξ.a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
      have h2 : ξ.cRow i₀ ≤ ξ.t := by
        rw [Config.t_eq_sum_cRow]
        exact Finset.single_le_sum (f := ξ.cRow) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i₀)
      simp only [Config.mA]; omega
    have hbj : ∀ j, ξ.b j = 0 := fun j => by
      have h1 : ξ.b j ≤ ξ.sumB := by
        rw [Config.sumB]
        exact Finset.single_le_sum (f := ξ.b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have h0 : Analysis.TruncationRemainder.sel i₀ u ξ = 0 := by
      simp [Analysis.TruncationRemainder.sel, hmA, hn, hbj]
    rw [Umodel, h0, zero_div, abs_zero]
    exact mul_nonneg (mul_nonneg hC hcU0) (Vz_nonneg hz0.le ξ)
  · have hn1 : 1 ≤ ξ.n := Nat.pos_of_ne_zero hn
    have hD : 0 < LinearAlgebra.Recursion.diag θA θB ρ ξ := diag_pos hθA hθB hρ ξ hn1
    have hVz : 0 ≤ C * Vz z ξ := mul_nonneg hC (Vz_nonneg hz0.le ξ)
    have h1 : |((ξ.mA i₀ : ℕ) : ℝ) * u ξ| ≤ ((ξ.mA i₀ : ℕ) : ℝ) * (C * Vz z ξ) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hu ξ) (Nat.cast_nonneg _)
    have h2 : |∑ j, ((ξ.b j : ℕ) : ℝ) * u (Analysis.TruncationRemainder.bToC ξ i₀ j)|
        ≤ ((ξ.sumB : ℕ) : ℝ) * (C * Vz z ξ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc (∑ j, |((ξ.b j : ℕ) : ℝ) * u (Analysis.TruncationRemainder.bToC ξ i₀ j)|)
          ≤ ∑ j, ((ξ.b j : ℕ) : ℝ) * (C * Vz z ξ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases h : ξ.b j = 0
            · rw [h]; simp
            · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              have hb := hu (Analysis.TruncationRemainder.bToC ξ i₀ j)
              have he : Vz z (Analysis.TruncationRemainder.bToC ξ i₀ j) = Vz z ξ := by
                simp only [Vz, Analysis.TruncationRemainder.n_bToC ξ i₀ h]
              rwa [he] at hb
        _ = ((ξ.sumB : ℕ) : ℝ) * (C * Vz z ξ) := by
            rw [← Finset.sum_mul, Config.sumB, Nat.cast_sum]
    have h3 : |((ξ.n : ℕ) : ℝ) * u (Analysis.TruncationRemainder.incA ξ i₀)| ≤ ((ξ.n : ℕ) : ℝ) *
        (C * Vz z ξ * z) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hb := hu (Analysis.TruncationRemainder.incA ξ i₀)
      have he : Vz z (Analysis.TruncationRemainder.incA ξ i₀) = Vz z ξ * z := by
        simp only [Vz, Analysis.TruncationRemainder.n_incA ξ i₀, pow_succ]
      rwa [he, ← mul_assoc] at hb
    obtain ⟨p1, q1⟩ := abs_le.mp h1
    obtain ⟨p2, q2⟩ := abs_le.mp h2
    obtain ⟨p3, q3⟩ := abs_le.mp h3
    have habs : |Analysis.TruncationRemainder.sel i₀ u ξ|
        ≤ C * Vz z ξ * (((ξ.mA i₀ : ℕ) : ℝ) + ((ξ.sumB : ℕ) : ℝ) + ((ξ.n : ℕ) : ℝ) * z) := by
      rw [Analysis.TruncationRemainder.sel]
      refine abs_le.mpr ⟨by linarith, by linarith⟩
    rw [Umodel, abs_div, abs_of_pos hD, div_le_iff₀ hD]
    calc |Analysis.TruncationRemainder.sel i₀ u ξ|
        ≤ C * Vz z ξ * (((ξ.mA i₀ : ℕ) : ℝ) + ((ξ.sumB : ℕ) : ℝ) + ((ξ.n : ℕ) : ℝ) * z) := habs
      _ ≤ C * Vz z ξ * (cUconst θA θB z * LinearAlgebra.Recursion.diag θA θB ρ ξ) :=
          mul_le_mul_of_nonneg_left (sel_ratio_le hθA hθB hρ hz0.le i₀ ξ) hVz
      _ = C * cUconst θA θB z * Vz z ξ * LinearAlgebra.Recursion.diag θA θB ρ ξ := by ring

end Operators

section Assembly

variable {θA θB ρ z pA pB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem abs_mul_cU_div_deltaStar (σ : ℝ) :
    |σ| * cUconst θA θB z / deltaStar θA θB ρ pA pB z = |σ| / rStar θA θB ρ pA pB z := by
  rw [rStar_eq_div, div_div_eq_mul_div]

theorem deltaStar_spec (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hz : 1 < z)
    (hadm : ρ * (z - 1) < Theta θA θB pA pB) :
    0 < deltaStar θA θB ρ pA pB z ∧ deltaStar θA θB ρ pA pB z ≤ 1
      ∧ deltaStar θA θB ρ pA pB z * z ≤ z - 1
      ∧ deltaStar θA θB ρ pA pB z * (θA + θB + ρ)
          ≤ θA * (1 - pA) + θB * (1 - pB) - ρ * (z - 1) := by
  have hSD : 0 < SigmaD θA θB ρ := by rw [SigmaD]; linarith
  refine ⟨deltaStar_pos hz hSD hadm, deltaStar_le_one hz, deltaStar_mul_le hz, ?_⟩
  have h := deltaStar_mul_SigmaD_le (θA := θA) (θB := θB) (ρ := ρ) (pA := pA) (pB := pB)
    (z := z) hSD
  rwa [SigmaD, Theta] at h

theorem coeff_bound_model (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 < z) (hadm : ρ * (z - 1) < Theta θA θB pA pB) (i₀ : Fin KA)
    {v : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : Analysis.TruncationRemainder.IsHierarchy (Vz z) (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀)
        v q)
    {P : ℝ} (hP : 0 ≤ P) (hq0 : Analysis.TruncationRemainder.BoundBy (Vz z) P (q 0)) (k : ℕ) :
    Analysis.TruncationRemainder.BoundBy (Vz z) (P * (rStar θA θB ρ pA pB z)⁻¹ ^ k) (q k) := by
  obtain ⟨hd0, hd1, hdz, hdS⟩ := deltaStar_spec hθA hθB hρ hz hadm
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  have hcU0 : 0 ≤ cUconst θA θB z := by rw [cUconst]; positivity
  exact Analysis.TruncationRemainder.coeff_bound_radius hd0 hd1 hcU0 (rStar_eq_div θA θB ρ pA pB z)
    (dominates_Tplus hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz.le hd1 hdz hdS)
    (uBounded_Umodel hθA hθB hρ hz.le i₀) hq hP hq0 k

theorem remainder_bound_model (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 < z) (hadm : ρ * (z - 1) < Theta θA θB pA pB) (i₀ : Fin KA)
    {v u : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : Analysis.TruncationRemainder.IsHierarchy (Vz z) (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀)
        v q)
    {σ Cu : ℝ} (hCu : 0 ≤ Cu)
    (hu : ∀ ξ, u ξ = Tplus θA θB ρ πA πB u ξ + σ * Umodel θA θB ρ i₀ u ξ + v ξ)
    (hubdd : Analysis.TruncationRemainder.BoundBy (Vz z) Cu u) (K : ℕ) :
    Analysis.TruncationRemainder.BoundBy (Vz z) (Cu * (|σ| / rStar θA θB ρ pA pB z) ^ K)
      (fun ξ => u ξ - Analysis.TruncationRemainder.partialSum σ q K ξ) := by
  obtain ⟨hd0, hd1, hdz, hdS⟩ := deltaStar_spec hθA hθB hρ hz hadm
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  have hcU0 : 0 ≤ cUconst θA θB z := by rw [cUconst]; positivity
  have hmain := Analysis.TruncationRemainder.remainder_bound hd0 hd1 hcU0
    (dominates_Tplus hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz.le hd1 hdz hdS)
    (uBounded_Umodel hθA hθB hρ hz.le i₀) (isLinear_Tplus θA θB ρ πA πB)
    (isLinear_Umodel θA θB ρ i₀) hq hCu hu hubdd K
  rwa [abs_mul_cU_div_deltaStar] at hmain

theorem exists_K_of_tol_model (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 < z) (hadm : ρ * (z - 1) < Theta θA θB pA pB) (i₀ : Fin KA)
    {v u : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : Analysis.TruncationRemainder.IsHierarchy (Vz z) (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀)
        v q)
    {σ Cu : ℝ} (hCu : 0 ≤ Cu)
    (hu : ∀ ξ, u ξ = Tplus θA θB ρ πA πB u ξ + σ * Umodel θA θB ρ i₀ u ξ + v ξ)
    (hubdd : Analysis.TruncationRemainder.BoundBy (Vz z) Cu u) (hσ : |σ| < rStar θA θB ρ pA pB z)
    {ε : ℝ} (hε : 0 < ε) (ξ : Config KA KB) :
    ∃ K, |u ξ - Analysis.TruncationRemainder.partialSum σ q K ξ| ≤ ε := by
  obtain ⟨hd0, hd1, hdz, hdS⟩ := deltaStar_spec hθA hθB hρ hz hadm
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  have hcU0 : 0 ≤ cUconst θA θB z := by rw [cUconst]; positivity
  have hrpos : 0 < rStar θA θB ρ pA pB z := by
    rw [rStar]
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have ht1 : |σ| * cUconst θA θB z / deltaStar θA θB ρ pA pB z < 1 := by
    rw [abs_mul_cU_div_deltaStar, div_lt_one hrpos]
    exact hσ
  exact Analysis.TruncationRemainder.exists_K_of_tol hd0 hd1 hcU0
    (dominates_Tplus hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz.le hd1 hdz hdS)
    (uBounded_Umodel hθA hθB hρ hz.le i₀) (isLinear_Tplus θA θB ρ πA πB)
    (isLinear_Umodel θA θB ρ i₀) hq hCu hu hubdd ht1 hε ξ

end Assembly

section Both

open Filter

open scoped Topology

variable {θA θB ρ z pA pB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem coeff_bound_scaled_model (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 < z) (hadm : ρ * (z - 1) < Theta θA θB pA pB) (i₀ : Fin KA)
    {v : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : Analysis.TruncationRemainder.IsHierarchy (Vz z) (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀)
        v q)
    {P σ : ℝ} (hP : 0 ≤ P) (hq0 : Analysis.TruncationRemainder.BoundBy (Vz z) P (q 0)) (k : ℕ) :
    Analysis.TruncationRemainder.BoundBy (Vz z) (P * (|σ| / rStar θA θB ρ pA pB z) ^ k)
        (fun ξ => σ ^ k * q k ξ) := by
  have h := coeff_bound_model hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz hadm i₀ hq hP hq0 k
  have h2 := h.const_mul (a := σ ^ k)
  have heq : |σ ^ k| * (P * (rStar θA θB ρ pA pB z)⁻¹ ^ k)
      = P * (|σ| / rStar θA θB ρ pA pB z) ^ k := by
    rw [abs_pow, div_eq_mul_inv, mul_pow]
    ring
  rwa [heq] at h2

theorem remainder_bound_min_model (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∀ i, πA i ≤ pA) (hπB : ∀ j, πB j ≤ pB) (hpA : pA ≤ 1) (hpB : pB ≤ 1)
    (hz : 1 < z) (hadm : ρ * (z - 1) < Theta θA θB pA pB) (i₀ : Fin KA)
    {v u : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : Analysis.TruncationRemainder.IsHierarchy (Vz z) (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀)
        v q)
    {σ Cu P : ℝ} (hCu : 0 ≤ Cu) (hP : 0 ≤ P)
        (hq0 : Analysis.TruncationRemainder.BoundBy (Vz z) P (q 0))
    (hu : ∀ ξ, u ξ = Tplus θA θB ρ πA πB u ξ + σ * Umodel θA θB ρ i₀ u ξ + v ξ)
    (hubdd : Analysis.TruncationRemainder.BoundBy (Vz z) Cu u) (hσ : |σ| < rStar θA θB ρ pA pB z)
    (hconv : ∀ ξ, Tendsto (fun K => Analysis.TruncationRemainder.partialSum σ q K ξ) atTop
        (𝓝 (u ξ))) (K : ℕ) :
    Analysis.TruncationRemainder.BoundBy (Vz z)
      (min (Cu * (|σ| / rStar θA θB ρ pA pB z) ^ K)
        (P * (|σ| / rStar θA θB ρ pA pB z) ^ K / (1 - |σ| / rStar θA θB ρ pA pB z)))
      (fun ξ => u ξ - Analysis.TruncationRemainder.partialSum σ q K ξ) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hμ : 0 < muTheta θA θB := lt_min hθA hθB
  obtain ⟨hd0, _, _, _⟩ := deltaStar_spec hθA hθB hρ hz hadm
  have hrpos : 0 < rStar θA θB ρ pA pB z := by
    rw [rStar]
    have h1 : (0 : ℝ) < 1 + z := by linarith
    positivity
  have ht0 : 0 ≤ |σ| / rStar θA θB ρ pA pB z := div_nonneg (abs_nonneg σ) hrpos.le
  have ht1 : |σ| / rStar θA θB ρ pA pB z < 1 := by rw [div_lt_one hrpos]; exact hσ
  refine (remainder_bound_model hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz hadm i₀ hq hCu hu
    hubdd K).min_of ?_
  exact Analysis.TruncationRemainder.tail_bound (fun ξ => Vz_nonneg hz0.le ξ) hP ht0 ht1
    (fun k => coeff_bound_scaled_model hθA hθB hρ hπA0 hπB0 hπA hπB hpA hpB hz hadm i₀ hq hP
      hq0 k) hconv K

end Both

end Rhone.Coalescent.TruncationRemainder
