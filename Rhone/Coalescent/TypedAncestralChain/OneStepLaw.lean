/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Types

/-! # The one-step law of the type-carrying chain, and its transition matrix -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def stepT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (g : TSt n KA KB → ℝ)
    (s : TSt n KA KB) : ℝ :=
  (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g (coalL s.1 p q, s.2.1, s.2.2))
    + θA * (∑ p ∈ carA s.1, ∑ i, πA i * g (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2))
    + θB * (∑ p ∈ carB s.1, ∑ j, πB j * g (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j))
    + ρ * (∑ p ∈ carC s.1, g (recL s.1 p, s.2.1, s.2.2))

theorem stepT_one (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (s : TSt n KA KB) :
    stepT θA θB ρ πA πB (fun _ => (1 : ℝ)) s = dtot θA θB ρ s.1 := by
  rw [← stepU_one (θA := θA) (θB := θB) (ρ := ρ) s.1, stepT, stepU]
  simp only [mul_one, hsA, hsB]

theorem stepT_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {g : TSt n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) (s : TSt n KA KB) :
    0 ≤ stepT θA θB ρ πA πB g s := by
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _
  · exact mul_nonneg hθA (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (hπA i) (hg _))
  · exact mul_nonneg hθB (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hπB j) (hg _))
  · exact mul_nonneg hρ (Finset.sum_nonneg fun _ _ => hg _)

theorem stepT_mono (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {g₁ g₂ : TSt n KA KB → ℝ} (h : ∀ t, g₁ t ≤ g₂ t) (s : TSt n KA KB) :
    stepT θA θB ρ πA πB g₁ s ≤ stepT θA θB ρ πA πB g₂ s := by
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => h _
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ =>
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) (hπA i)) hθA
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ =>
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h _) (hπB j)) hθB
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => h _) hρ

theorem stepT_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → TSt n KA KB → ℝ)
    (s : TSt n KA KB) :
    (∑ x, c x * stepT θA θB ρ πA πB (g x) s)
      = stepT θA θB ρ πA πB (fun t => ∑ x, c x * g x t) s := by
  have key : ∀ (θ : ℝ) (X : ι → ℝ), (∑ x, c x * (θ * X x)) = θ * ∑ x, c x * X x := by
    intro θ X
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hA : (∑ x, c x * ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g x (coalL s.1 p q, s.2.1, s.2.2))
      = ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, ∑ x, c x * g x (coalL s.1 p q, s.2.1, s.2.2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hB : (∑ x, c x * ∑ p ∈ carA s.1, ∑ i, πA i * g x (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2))
      = ∑ p ∈ carA s.1, ∑ i, πA i * ∑ x, c x * g x (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  have hC : (∑ x, c x * ∑ p ∈ carB s.1, ∑ j, πB j * g x (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j))
      = ∑ p ∈ carB s.1, ∑ j, πB j * ∑ x, c x * g x (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  have hD : (∑ x, c x * ∑ p ∈ carC s.1, g x (recL s.1 p, s.2.1, s.2.2))
      = ∑ p ∈ carC s.1, ∑ x, c x * g x (recL s.1 p, s.2.1, s.2.2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [stepT, mul_add, Finset.sum_add_distrib, key, hA, hB, hC, hD]

theorem stepT_of_fst (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (f : Finset (Lin n) → ℝ)
    (s : TSt n KA KB) :
    stepT θA θB ρ πA πB (fun t => f t.1) s = stepU θA θB ρ f s.1 := by
  have hA : ∀ p : Lin n, (∑ _i : Fin KA, πA _i * f (mutAL s.1 p)) = f (mutAL s.1 p) := by
    intro p
    rw [← Finset.sum_mul, hsA, one_mul]
  have hB : ∀ p : Lin n, (∑ _j : Fin KB, πB _j * f (mutBL s.1 p)) = f (mutBL s.1 p) := by
    intro p
    rw [← Finset.sum_mul, hsB, one_mul]
  rw [stepT, stepU]
  simp only [hA, hB]

noncomputable def transT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (s t : TSt n KA KB) : ℝ :=
  if 0 < dtot θA θB ρ s.1 then
    stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s / dtot θA θB ρ s.1
  else if t = s then 1 else 0

theorem transT_of_dtot_pos {s t : TSt n KA KB} (h : 0 < dtot θA θB ρ s.1) :
    transT θA θB ρ πA πB s t
      = stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s / dtot θA θB ρ s.1 := by
  rw [transT, ite_eq_left h]

theorem transT_of_dtot_nonpos {s t : TSt n KA KB} (h : ¬ 0 < dtot θA θB ρ s.1) :
    transT θA θB ρ πA πB s t = if t = s then 1 else 0 := by
  rw [transT, ite_eq_right h]

theorem transT_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (s t : TSt n KA KB) : 0 ≤ transT θA θB ρ πA πB s t := by
  rw [transT]
  split_ifs with hd
  · exact div_nonneg (stepT_nonneg hθA hθB hρ hπA hπB (fun _ => by positivity) s) hd.le
  · norm_num
  · norm_num

theorem sum_transT (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (s : TSt n KA KB) :
    (∑ t, transT θA θB ρ πA πB s t) = 1 := by
  by_cases hd : 0 < dtot θA θB ρ s.1
  · have hone : (fun t' : TSt n KA KB => ∑ t : TSt n KA KB, 1 * if t' = t then (1 : ℝ) else 0)
        = fun _ => (1 : ℝ) := by
      funext t'
      simp
    calc (∑ t, transT θA θB ρ πA πB s t)
        = ∑ t : TSt n KA KB,
            1 * stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s
              / dtot θA θB ρ s.1 := by
          exact Finset.sum_congr rfl fun t _ => by rw [transT_of_dtot_pos hd, one_mul]
      _ = (∑ t : TSt n KA KB,
            1 * stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s)
              / dtot θA θB ρ s.1 := by
          rw [Finset.sum_div]
      _ = 1 := by
          rw [stepT_sum, hone, stepT_one hsA hsB, div_self hd.ne']
  · calc (∑ t, transT θA θB ρ πA πB s t)
        = ∑ t : TSt n KA KB, if t = s then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun t _ => transT_of_dtot_nonpos hd
      _ = 1 := by
          rw [Finset.sum_ite_eq' Finset.univ s (fun _ => (1 : ℝ)), ite_eq_left (Finset.mem_univ s)]

end Rhone.Coalescent.TypedAncestralChain
