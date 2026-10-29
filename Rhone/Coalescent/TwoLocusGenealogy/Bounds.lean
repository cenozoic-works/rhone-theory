/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.FirstStep
public import Rhone.LinearAlgebra.Recursion.Degenerate

/-! # The recursion is sub-stochastic: `rhs 1 ≤ diag` -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ}

theorem nat_mul_pred_add (a : ℕ) : a * (a - 1) + a = a * a := by
  cases a with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

theorem sum_sq_le {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    ∑ i, f i * f i ≤ (∑ i, f i) * (∑ i, f i) := by
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun j => f i * f j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem sum_sq_le₂ (m : Fin KA → Fin KB → ℕ) :
    (∑ i, ∑ j, m i j * m i j) ≤ (∑ i, ∑ j, m i j) * (∑ i, ∑ j, m i j) := by
  have key := sum_sq_le (ι := Fin KA × Fin KB) fun ij => m ij.1 ij.2
  simpa [Fintype.sum_prod_type] using key

theorem sum_a_mul_cRow_le (ξ : Config KA KB) : (∑ i, ξ.a i * ξ.cRow i) ≤ ξ.sumA * ξ.t := by
  rw [Config.sumA, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ ?_
  rw [Config.t_eq_sum_cRow]
  exact Finset.single_le_sum (f := fun i' => ξ.cRow i') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

theorem sum_b_mul_cCol_le (ξ : Config KA KB) : (∑ j, ξ.b j * ξ.cCol j) ≤ ξ.sumB * ξ.t := by
  rw [Config.sumB, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ ?_
  rw [Config.t_eq_sum_cCol]
  exact Finset.single_le_sum (f := fun j' => ξ.cCol j') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)

theorem sum_coalA_eq (ξ : Config KA KB) :
    (∑ i, ξ.coalA i) = (∑ i, ξ.a i * (ξ.a i - 1)) + 2 * ∑ i, ξ.a i * ξ.cRow i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Config.coalA]; ring

theorem sum_coalB_eq (ξ : Config KA KB) :
    (∑ j, ξ.coalB j) = (∑ j, ξ.b j * (ξ.b j - 1)) + 2 * ∑ j, ξ.b j * ξ.cCol j := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp only [Config.coalB]; ring

theorem sum_a_sq_eq (ξ : Config KA KB) :
    (∑ i, ξ.a i * (ξ.a i - 1)) + ξ.sumA = ∑ i, ξ.a i * ξ.a i := by
  rw [Config.sumA, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => nat_mul_pred_add _

theorem sum_b_sq_eq (ξ : Config KA KB) :
    (∑ j, ξ.b j * (ξ.b j - 1)) + ξ.sumB = ∑ j, ξ.b j * ξ.b j := by
  rw [Config.sumB, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => nat_mul_pred_add _

theorem sum_c_sq_eq (ξ : Config KA KB) :
    (∑ i, ∑ j, ξ.coalC i j) + ξ.t = ∑ i, ∑ j, ξ.c i j * ξ.c i j := by
  rw [Config.t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => nat_mul_pred_add _

theorem coal_total_le (ξ : Config KA KB) :
    (∑ i, ξ.coalA i) + (∑ j, ξ.coalB j) + (∑ i, ∑ j, ξ.coalC i j)
        + (∑ i, ∑ j, ξ.coalAB i j) ≤ ξ.n * (ξ.n - 1) := by
  have hn := nat_mul_pred_add ξ.n
  have hkey : ((∑ i, ξ.coalA i) + (∑ j, ξ.coalB j) + (∑ i, ∑ j, ξ.coalC i j)
      + (∑ i, ∑ j, ξ.coalAB i j)) + ξ.n ≤ ξ.n * ξ.n := by
    have b1 : (∑ i, ξ.a i * ξ.a i) ≤ ξ.sumA * ξ.sumA := by
      rw [Config.sumA]; exact sum_sq_le _
    have b2 : (∑ j, ξ.b j * ξ.b j) ≤ ξ.sumB * ξ.sumB := by
      rw [Config.sumB]; exact sum_sq_le _
    have b3 : (∑ i, ∑ j, ξ.c i j * ξ.c i j) ≤ ξ.t * ξ.t := by
      rw [Config.t]; exact sum_sq_le₂ _
    have b4 := sum_a_mul_cRow_le ξ
    have b5 := sum_b_mul_cCol_le ξ
    calc ((∑ i, ξ.coalA i) + (∑ j, ξ.coalB j) + (∑ i, ∑ j, ξ.coalC i j)
            + (∑ i, ∑ j, ξ.coalAB i j)) + ξ.n
        = ((∑ i, ξ.a i * (ξ.a i - 1)) + ξ.sumA) + ((∑ j, ξ.b j * (ξ.b j - 1)) + ξ.sumB)
            + ((∑ i, ∑ j, ξ.coalC i j) + ξ.t)
            + 2 * (∑ i, ξ.a i * ξ.cRow i) + 2 * (∑ j, ξ.b j * ξ.cCol j)
            + 2 * (ξ.sumA * ξ.sumB) := by
          rw [sum_coalA_eq, sum_coalB_eq, Config.sum_coalAB, Config.n]; ring
      _ = (∑ i, ξ.a i * ξ.a i) + (∑ j, ξ.b j * ξ.b j) + (∑ i, ∑ j, ξ.c i j * ξ.c i j)
            + 2 * (∑ i, ξ.a i * ξ.cRow i) + 2 * (∑ j, ξ.b j * ξ.cCol j)
            + 2 * (ξ.sumA * ξ.sumB) := by
          rw [sum_a_sq_eq, sum_b_sq_eq, sum_c_sq_eq]
      _ ≤ ξ.sumA * ξ.sumA + ξ.sumB * ξ.sumB + ξ.t * ξ.t
            + 2 * (ξ.sumA * ξ.t) + 2 * (ξ.sumB * ξ.t) + 2 * (ξ.sumA * ξ.sumB) := by
          gcongr
      _ = ξ.n * ξ.n := by rw [Config.n]; ring
  rw [← hn] at hkey
  exact Nat.le_of_add_le_add_right hkey

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem mA_le_nA (ξ : Config KA KB) (i : Fin KA) : ξ.mA i ≤ ξ.nA := by
  rw [← ξ.sum_mA]
  exact Finset.single_le_sum (f := fun i' => ξ.mA i') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

theorem mB_le_nB (ξ : Config KA KB) (j : Fin KB) : ξ.mB j ≤ ξ.nB := by
  rw [← ξ.sum_mB]
  exact Finset.single_le_sum (f := fun j' => ξ.mB j') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)

theorem sum_pi_mA_le (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (ξ : Config KA KB) :
    (∑ i, πA i * ((ξ.mA i : ℕ) : F)) ≤ ((ξ.nA : ℕ) : F) := by
  calc (∑ i, πA i * ((ξ.mA i : ℕ) : F))
      ≤ ∑ i, πA i * ((ξ.nA : ℕ) : F) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hπA i)
        exact_mod_cast mA_le_nA ξ i
    _ = ((ξ.nA : ℕ) : F) := by rw [← Finset.sum_mul, hsA, one_mul]

theorem sum_pi_mB_le (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    (∑ j, πB j * ((ξ.mB j : ℕ) : F)) ≤ ((ξ.nB : ℕ) : F) := by
  calc (∑ j, πB j * ((ξ.mB j : ℕ) : F))
      ≤ ∑ j, πB j * ((ξ.nB : ℕ) : F) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hπB j)
        exact_mod_cast mB_le_nB ξ j
    _ = ((ξ.nB : ℕ) : F) := by rw [← Finset.sum_mul, hsB, one_mul]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem rhs_one (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun _ => (1 : F)) ξ
      = (∑ i, ((ξ.coalA i : ℕ) : F)) + (∑ j, ((ξ.coalB j : ℕ) : F))
        + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F)) + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F))
        + θA * (∑ i, πA i * ((ξ.mA i : ℕ) : F)) + θB * (∑ j, πB j * ((ξ.mB j : ℕ) : F))
        + ρ * ((ξ.t : ℕ) : F) := by
  have hA : ∀ i : Fin KA, ((ξ.a i : ℕ) : F) + ∑ j, ((ξ.c i j : ℕ) : F)
      = ((ξ.mA i : ℕ) : F) := by
    intro i; rw [Config.mA, Config.cRow]; push_cast; ring
  have hB : ∀ j : Fin KB, ((ξ.b j : ℕ) : F) + ∑ i, ((ξ.c i j : ℕ) : F)
      = ((ξ.mB j : ℕ) : F) := by
    intro j; rw [Config.mB, Config.cCol]; push_cast; ring
  have ht : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F)) = ((ξ.t : ℕ) : F) := by
    rw [Config.t]; push_cast; ring
  simp only [rhs, mul_one, hA, hB, ht]

theorem rhs_one_le_diag (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun _ => (1 : F)) ξ ≤ LinearAlgebra.Recursion.diag θA θB ρ ξ := by
  have h1 : (∑ i, ((ξ.coalA i : ℕ) : F)) + (∑ j, ((ξ.coalB j : ℕ) : F))
      + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F)) + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F))
        ≤ ((ξ.n * (ξ.n - 1) : ℕ) : F) := by
    exact_mod_cast coal_total_le ξ
  have h2 : θA * (∑ i, πA i * ((ξ.mA i : ℕ) : F)) ≤ θA * ((ξ.nA : ℕ) : F) :=
    mul_le_mul_of_nonneg_left (sum_pi_mA_le hπA hsA ξ) hθA
  have h3 : θB * (∑ j, πB j * ((ξ.mB j : ℕ) : F)) ≤ θB * ((ξ.nB : ℕ) : F) :=
    mul_le_mul_of_nonneg_left (sum_pi_mB_le hπB hsB ξ) hθB
  rw [rhs_one, LinearAlgebra.Recursion.diag]
  linarith

end Rhone.Coalescent.TwoLocusGenealogy
