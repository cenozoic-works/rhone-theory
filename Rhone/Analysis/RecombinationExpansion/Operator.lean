/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Block
public import Rhone.LinearAlgebra.Recursion.OneLocus
public import Rhone.LinearAlgebra.Recursion.Bookkeeping

/-! # The recursion operator `L`, and the split `L = L₀ + ρ L₁` -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem cast_sum_c (ξ : Config KA KB) :
    (∑ i, ∑ j, ((ξ.c i j : ℕ) : F)) = ((ξ.t : ℕ) : F) := by
  simp only [Config.t, Nat.cast_sum]

theorem cast_sum_cRow (ξ : Config KA KB) (i : Fin KA) :
    (∑ j, ((ξ.c i j : ℕ) : F)) = ((ξ.cRow i : ℕ) : F) := (Nat.cast_sum _ _).symm

theorem cast_sum_cCol (ξ : Config KA KB) (j : Fin KB) :
    (∑ i, ((ξ.c i j : ℕ) : F)) = ((ξ.cCol j : ℕ) : F) := (Nat.cast_sum _ _).symm

theorem cast_sum_coalAB (ξ : Config KA KB) :
    (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F)) = 2 * ((ξ.sumA * ξ.sumB : ℕ) : F) := by
  have h : ((∑ i, ∑ j, ξ.coalAB i j : ℕ) : F) = ((2 * (ξ.sumA * ξ.sumB) : ℕ) : F) := by
    rw [sum_coalAB ξ]
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h

def Lop (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (f : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  diag θA θB ρ ξ * f ξ - rhs θA θB ρ πA πB f ξ

def L0 (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (f : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  Lop θA θB 0 πA πB f ξ

def L1 (f : Config KA KB → F) (ξ : Config KA KB) : F :=
  ((ξ.t : ℕ) : F) * f ξ - ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * f (ξ.split i j)

theorem Lop_split (f : Config KA KB → F) (ξ : Config KA KB) :
    Lop θA θB ρ πA πB f ξ = L0 θA θB πA πB f ξ + ρ * L1 f ξ := by
  simp only [Lop, L0, L1, diag, rhs]
  ring

theorem Lop_eq_zero_of_isSolution {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    Lop θA θB ρ πA πB q ξ = 0 :=
  sub_eq_zero_of_eq (hq.recursion ξ hn)

theorem Lop_sub (f g : Config KA KB → F) (ξ : Config KA KB) :
    Lop θA θB ρ πA πB (fun η => f η - g η) ξ
      = Lop θA θB ρ πA πB f ξ - Lop θA θB ρ πA πB g ξ := by
  simp only [Lop, rhs_sub, mul_sub]
  ring

theorem L1_sub (f g : Config KA KB → F) (ξ : Config KA KB) :
    L1 (fun η => f η - g η) ξ = L1 f ξ - L1 g ξ := by
  simp only [L1, mul_sub, Finset.sum_sub_distrib]
  ring

theorem L1_add (f g : Config KA KB → F) (ξ : Config KA KB) :
    L1 (fun η => f η + g η) ξ = L1 f ξ + L1 g ξ := by
  simp only [L1, mul_add, Finset.sum_add_distrib]
  ring

theorem Lop_zero (ξ : Config KA KB) : Lop θA θB ρ πA πB (fun _ => (0 : F)) ξ = 0 := by
  rw [Lop, rhs_zero, mul_zero, sub_zero]

theorem Lop_add (f g : Config KA KB → F) (ξ : Config KA KB) :
    Lop θA θB ρ πA πB (fun η => f η + g η) ξ
      = Lop θA θB ρ πA πB f ξ + Lop θA θB ρ πA πB g ξ := by
  simp only [Lop, rhs_add, mul_add]
  ring

theorem Lop_smul (c : F) (f : Config KA KB → F) (ξ : Config KA KB) :
    Lop θA θB ρ πA πB (fun η => c * f η) ξ = c * Lop θA θB ρ πA πB f ξ := by
  simp only [Lop, rhs_smul]
  ring

theorem L1_zero (ξ : Config KA KB) : L1 (fun _ => (0 : F)) ξ = 0 := by
  simp [L1]

theorem L1_smul (c : F) (f : Config KA KB → F) (ξ : Config KA KB) :
    L1 (fun η => c * f η) ξ = c * L1 f ξ := by
  have h : ∀ i : Fin KA, (∑ j, ((ξ.c i j : ℕ) : F) * (c * f (ξ.split i j)))
      = c * ∑ j, ((ξ.c i j : ℕ) : F) * f (ξ.split i j) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [L1]
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum]
  ring

theorem Lop_sum_range (f : ℕ → Config KA KB → F) (ξ : Config KA KB) (K : ℕ) :
    Lop θA θB ρ πA πB (fun η => ∑ k ∈ Finset.range K, f k η) ξ
      = ∑ k ∈ Finset.range K, Lop θA θB ρ πA πB (f k) ξ := by
  induction K with
  | zero => simpa using Lop_zero (θA := θA) (θB := θB) (ρ := ρ) (πA := πA) (πB := πB) ξ
  | succ n ih =>
    have hfun : (fun η => ∑ k ∈ Finset.range (n + 1), f k η)
        = fun η => (∑ k ∈ Finset.range n, f k η) + f n η := by
      funext η
      rw [Finset.sum_range_succ]
    rw [hfun, Lop_add, ih, Finset.sum_range_succ]

theorem L1_sum_range (f : ℕ → Config KA KB → F) (ξ : Config KA KB) (K : ℕ) :
    L1 (fun η => ∑ k ∈ Finset.range K, f k η) ξ = ∑ k ∈ Finset.range K, L1 (f k) ξ := by
  induction K with
  | zero => simpa using L1_zero (F := F) ξ
  | succ n ih =>
    have hfun : (fun η => ∑ k ∈ Finset.range (n + 1), f k η)
        = fun η => (∑ k ∈ Finset.range n, f k η) + f n η := by
      funext η
      rw [Finset.sum_range_succ]
    rw [hfun, L1_add, ih, Finset.sum_range_succ]

theorem L1_of_sector_const {f : Config KA KB → F} (ξ : Config KA KB)
    (h : ∀ i j, ξ.c i j ≠ 0 → f (ξ.split i j) = f ξ) : L1 f ξ = 0 := by
  have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
      ((ξ.c i j : ℕ) : F) * f (ξ.split i j) = ((ξ.c i j : ℕ) : F) * f ξ := by
    intro i j
    by_cases hc : ξ.c i j = 0
    · rw [hc]; simp
    · rw [h i j hc]
  simp only [L1]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  simp only [← Finset.sum_mul, ← Finset.sum_mul]
  rw [show (∑ i, ∑ j, ((ξ.c i j : ℕ) : F)) = ((ξ.t : ℕ) : F) from cast_sum_c ξ]
  ring

theorem L1_const (v : F) (ξ : Config KA KB) : L1 (fun _ => v) ξ = 0 :=
  L1_of_sector_const ξ fun _ _ _ => rfl

theorem L1_of_t_eq_zero (f : Config KA KB → F) {ξ : Config KA KB} (h : ξ.t = 0) :
    L1 f ξ = 0 := by
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t h
  simp only [L1, h, hc]
  simp

theorem L1_sector (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (h : ξ.c i j ≠ 0) :
    (ξ.split i j).mA = ξ.mA ∧ (ξ.split i j).mB = ξ.mB :=
  ⟨ξ.mA_split h, ξ.mB_split h⟩

theorem L1_level (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (h : ξ.c i j ≠ 0) :
    (ξ.split i j).t + 1 = ξ.t := ξ.t_split i j h

end Rhone.Analysis.RecombinationExpansion
