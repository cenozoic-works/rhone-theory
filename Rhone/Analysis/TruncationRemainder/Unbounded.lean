/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.TruncationRemainder.Comparison
public import Rhone.LinearAlgebra.Recursion.Config
public import Rhone.LinearAlgebra.Recursion.Defs

/-! # No weighted sup-norm bounds the selection operator -/

@[expose] public section

namespace Rhone.Analysis.TruncationRemainder

open Finset LinearAlgebra.Recursion

section Abstract

variable {ι : Type*} [DecidableEq ι]

def pointMass (W : ι → ℝ) (i₀ : ι) : ι → ℝ := fun j => if j = i₀ then W i₀ else 0

@[simp] theorem pointMass_self (W : ι → ℝ) (i₀ : ι) : pointMass W i₀ i₀ = W i₀ := by
  simp [pointMass]

theorem pointMass_of_ne (W : ι → ℝ) {i₀ j : ι} (h : j ≠ i₀) : pointMass W i₀ j = 0 := by
  simp [pointMass, h]

theorem pointMass_boundBy (W : ι → ℝ) (hW : ∀ i, 0 ≤ W i) (i₀ : ι) :
    BoundBy W 1 (pointMass W i₀) := by
  intro j
  by_cases h : j = i₀
  · subst h; rw [pointMass_self, one_mul, abs_of_nonneg (hW j)]
  · rw [pointMass_of_ne W h]; simpa using hW j

omit [DecidableEq ι] in
theorem opNorm_ge_of_diag (W : ι → ℝ) (hW : ∀ i, 0 < W i) (L : (ι → ℝ) → ι → ℝ) (m : ι → ℝ)
    (ξ : ι) (hL : ∀ u : ι → ℝ, (∀ j, j ≠ ξ → u j = 0) → L u ξ = m ξ * u ξ) :
    ∃ u : ι → ℝ, BoundBy W 1 u ∧ |m ξ| * W ξ = |L u ξ| := by
  classical
  refine ⟨pointMass W ξ, pointMass_boundBy W (fun i => (hW i).le) ξ, ?_⟩
  rw [hL _ fun j hj => pointMass_of_ne W hj, pointMass_self, abs_mul,
    abs_of_nonneg (hW ξ).le]

end Abstract

variable {KA KB : ℕ}

def incA (ξ : Config KA KB) (i₀ : Fin KA) : Config KA KB := ⟨incf ξ.a i₀, ξ.b, ξ.c⟩

def bToC (ξ : Config KA KB) (i₀ : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, decf ξ.b j, Config.incC ξ.c i₀ j⟩

@[simp] theorem sumA_incA (ξ : Config KA KB) (i₀ : Fin KA) :
    (incA ξ i₀).sumA = ξ.sumA + 1 := sum_incf _ _

@[simp] theorem sumB_incA (ξ : Config KA KB) (i₀ : Fin KA) : (incA ξ i₀).sumB = ξ.sumB := rfl

@[simp] theorem t_incA (ξ : Config KA KB) (i₀ : Fin KA) : (incA ξ i₀).t = ξ.t := rfl

theorem n_incA (ξ : Config KA KB) (i₀ : Fin KA) : (incA ξ i₀).n = ξ.n + 1 := by
  simp only [Config.n, sumA_incA, sumB_incA, t_incA]; omega

@[simp] theorem sumA_bToC (ξ : Config KA KB) (i₀ : Fin KA) (j : Fin KB) :
    (bToC ξ i₀ j).sumA = ξ.sumA := rfl

theorem sumB_bToC (ξ : Config KA KB) (i₀ : Fin KA) {j : Fin KB} (h : ξ.b j ≠ 0) :
    (bToC ξ i₀ j).sumB + 1 = ξ.sumB := sum_decf h

@[simp] theorem t_bToC (ξ : Config KA KB) (i₀ : Fin KA) (j : Fin KB) :
    (bToC ξ i₀ j).t = ξ.t + 1 := Config.sum_incC _ _ _

theorem n_bToC (ξ : Config KA KB) (i₀ : Fin KA) {j : Fin KB} (h : ξ.b j ≠ 0) :
    (bToC ξ i₀ j).n = ξ.n := by
  have h1 := sumB_bToC ξ i₀ h
  simp only [Config.n, sumA_bToC, t_bToC]; omega

def sel (i₀ : Fin KA) (u : Config KA KB → ℝ) (ξ : Config KA KB) : ℝ :=
  ((ξ.mA i₀ : ℕ) : ℝ) * u ξ + (∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j))
    - ((ξ.n : ℕ) : ℝ) * u (incA ξ i₀)

def neutralOp (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (u : Config KA KB → ℝ)
    (ξ : Config KA KB) : ℝ :=
  LinearAlgebra.Recursion.rhs θA θB ρ πA πB u ξ - LinearAlgebra.Recursion.diag θA θB ρ ξ * u ξ

def xiN (i₀ : Fin KA) (N : ℕ) : Config KA KB :=
  ⟨fun i => if i = i₀ then N else 0, fun _ => 0, fun _ _ => 0⟩

@[simp] theorem xiN_b (i₀ : Fin KA) (N : ℕ) (j : Fin KB) :
    (xiN i₀ N : Config KA KB).b j = 0 := rfl

@[simp] theorem xiN_c (i₀ : Fin KA) (N : ℕ) (i : Fin KA) (j : Fin KB) :
    (xiN i₀ N : Config KA KB).c i j = 0 := rfl

@[simp] theorem xiN_a (i₀ : Fin KA) (N : ℕ) (i : Fin KA) :
    (xiN i₀ N : Config KA KB).a i = if i = i₀ then N else 0 := rfl

@[simp] theorem xiN_sumB (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).sumB = 0 := by
  simp [Config.sumB]

@[simp] theorem xiN_t (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).t = 0 := by
  simp [Config.t]

@[simp] theorem xiN_cRow (i₀ : Fin KA) (N : ℕ) (i : Fin KA) :
    (xiN i₀ N : Config KA KB).cRow i = 0 := by simp [Config.cRow]

@[simp] theorem xiN_sumA (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).sumA = N := by
  simp [Config.sumA]

@[simp] theorem xiN_n (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).n = N := by
  simp [Config.n]

@[simp] theorem xiN_nA (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).nA = N := by
  simp [Config.nA]

@[simp] theorem xiN_nB (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).nB = 0 := by
  simp [Config.nB]

@[simp] theorem xiN_mA (i₀ : Fin KA) (N : ℕ) : (xiN i₀ N : Config KA KB).mA i₀ = N := by
  simp [Config.mA]

theorem incA_ne (ξ : Config KA KB) (i₀ : Fin KA) : incA ξ i₀ ≠ ξ := by
  intro h
  have := n_incA ξ i₀
  rw [h] at this
  omega

theorem sel_of_pointSupported (i₀ : Fin KA) (ξ : Config KA KB) (hb : ∀ j, ξ.b j = 0)
    (u : Config KA KB → ℝ) (hu : ∀ η, η ≠ ξ → u η = 0) :
    sel i₀ u ξ = ((ξ.mA i₀ : ℕ) : ℝ) * u ξ := by
  have h1 : (∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hb j]; simp
  rw [sel, h1, hu _ (incA_ne ξ i₀)]
  ring

theorem sel_opNorm_ge (W : Config KA KB → ℝ) (hW : ∀ ξ, 0 < W ξ) (i₀ : Fin KA) (N : ℕ) :
    ∃ u : Config KA KB → ℝ,
      BoundBy W 1 u ∧ (N : ℝ) * W (xiN i₀ N) = |sel i₀ u (xiN i₀ N)| := by
  obtain ⟨u, hu1, hu2⟩ :=
    opNorm_ge_of_diag W hW (sel i₀) (fun η => ((η.mA i₀ : ℕ) : ℝ)) (xiN i₀ N)
      (fun u hu => sel_of_pointSupported i₀ _ (fun j => rfl) u hu)
  refine ⟨u, hu1, ?_⟩
  rw [← hu2, xiN_mA, abs_of_nonneg (Nat.cast_nonneg N)]

theorem sel_not_bounded (W : Config KA KB → ℝ) (hW : ∀ ξ, 0 < W ξ) (i₀ : Fin KA) (c : ℝ) :
    ∃ (u : Config KA KB → ℝ) (ξ : Config KA KB), BoundBy W 1 u ∧ c * W ξ < |sel i₀ u ξ| := by
  obtain ⟨N, hN⟩ := exists_nat_gt c
  obtain ⟨u, hu1, hu2⟩ := sel_opNorm_ge W hW i₀ N
  exact ⟨u, xiN i₀ N, hu1, by rw [← hu2]; exact mul_lt_mul_of_pos_right hN (hW _)⟩

theorem rhs_eq_zero_of_pointSupported (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ξ : Config KA KB) (hb : ∀ j, ξ.b j = 0) (hc : ∀ i j, ξ.c i j = 0)
    (u : Config KA KB → ℝ) (hu : ∀ η, η ≠ ξ → u η = 0) :
    LinearAlgebra.Recursion.rhs θA θB ρ πA πB u ξ = 0 := by
  have hdrop : ∀ i, ξ.a i ≠ 0 → u (ξ.dropA i) = 0 := by
    intro i hi
    refine hu _ fun hcon => ?_
    have h := ξ.n_dropA i hi
    rw [hcon] at h
    omega
  have h1 : ∀ i : Fin KA, ((ξ.coalA i : ℕ) : ℝ) * u (ξ.dropA i) = 0 := by
    intro i
    by_cases h : ξ.a i = 0
    · rw [ξ.coalA_eq_zero_of h]; simp
    · rw [hdrop i h, mul_zero]
  have h2 : ∀ i : Fin KA, ((ξ.a i : ℕ) : ℝ) * u (ξ.dropA i) = 0 := by
    intro i
    by_cases h : ξ.a i = 0
    · rw [h]; simp
    · rw [hdrop i h, mul_zero]
  have g1 : (∑ i, ((ξ.coalA i : ℕ) : ℝ) * u (ξ.dropA i)) = 0 :=
    Finset.sum_eq_zero fun i _ => h1 i
  have g2 : (∑ j, ((ξ.coalB j : ℕ) : ℝ) * u (ξ.dropB j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [ξ.coalB_eq_zero_of (hb j)]; simp
  have g3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * u (ξ.dropC i j)) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => by rw [ξ.coalC_eq_zero_of (hc i j)]; simp
  have g4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * u (ξ.mergeAB i j)) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => by rw [ξ.coalAB_eq_zero_right i (hb j)]; simp
  have g5 : (∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * u (ξ.dropA i)
      + ∑ j, ((ξ.c i j : ℕ) : ℝ) * u (ξ.killA i j))) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [h2 i, Finset.sum_eq_zero fun j _ => by rw [hc i j]; simp]
      ring
  have g6 : (∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * u (ξ.dropB j)
      + ∑ i, ((ξ.c i j : ℕ) : ℝ) * u (ξ.killB i j))) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hb j, Finset.sum_eq_zero fun i _ => by rw [hc i j]; simp]
      simp
  have g7 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * u (ξ.split i j)) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => by rw [hc i j]; simp
  rw [LinearAlgebra.Recursion.rhs, g1, g2, g3, g4, g5, g6, g7]
  ring

theorem diag_xiN (θA θB ρ : ℝ) (i₀ : Fin KA) (N : ℕ) :
    LinearAlgebra.Recursion.diag θA θB ρ (xiN i₀ N : Config KA KB) = ((N * (N - 1) : ℕ) : ℝ) + θA *
        N := by
  simp [LinearAlgebra.Recursion.diag]

theorem neutral_not_bounded (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 ≤ θA)
    (W : Config KA KB → ℝ) (hW : ∀ ξ, 0 < W ξ) (i₀ : Fin KA) (c : ℝ) :
    ∃ (u : Config KA KB → ℝ) (ξ : Config KA KB),
      BoundBy W 1 u ∧ c * W ξ < |neutralOp θA θB ρ πA πB u ξ| := by
  obtain ⟨M, hM⟩ := exists_nat_gt c
  set N := M + 1 with hN
  obtain ⟨u, hu1, hu2⟩ :=
    opNorm_ge_of_diag W hW (neutralOp θA θB ρ πA πB)
      (fun η => -LinearAlgebra.Recursion.diag θA θB ρ η) (xiN i₀ N)
      (fun u hu => by
        rw [neutralOp,
          rhs_eq_zero_of_pointSupported θA θB ρ πA πB _ (fun j => rfl) (fun i j => rfl) u hu]
        ring)
  refine ⟨u, xiN i₀ N, hu1, ?_⟩
  rw [← hu2]
  refine mul_lt_mul_of_pos_right ?_ (hW _)
  have hd : |(-LinearAlgebra.Recursion.diag θA θB ρ (xiN i₀ N : Config KA KB))|
      = ((N * (N - 1) : ℕ) : ℝ) + θA * N := by
    rw [abs_neg, diag_xiN, abs_of_nonneg]
    positivity
  rw [hd]
  have h1 : (M : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by
    have hNM : N * (N - 1) = (M + 1) * M := by rw [hN]; simp
    have hle : M ≤ (M + 1) * M := Nat.le_mul_of_pos_left M (Nat.succ_pos M)
    rw [hNM]
    exact_mod_cast hle
  have h2 : (0 : ℝ) ≤ θA * N := mul_nonneg hθA (Nat.cast_nonneg N)
  linarith

end Rhone.Analysis.TruncationRemainder
