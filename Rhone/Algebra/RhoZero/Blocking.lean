/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZero.PartialFraction
public import Rhone.Algebra.ClosedForms.Rho0

/-! # Additivity of blocking, and cancellation of the three-move family -/

@[expose] public section

namespace Rhone.Algebra.RhoZero

open Finset LinearAlgebra.Recursion Config ClosedForms

inductive MoveClass
  | M1
  | M2
  | M3
  | M4
  | M5
  | M6

def delta {F : Type*} [CommRing F] (θA θB : F) (k : ℕ) : MoveClass → F
  | .M1 => -(2 * ((k : F) - 1)) - θA
  | .M2 => -(2 * ((k : F) - 1)) - θB
  | .M3 => -(2 * ((k : F) - 1)) - θA - θB
  | .M4 => -(2 * ((k : F) - 1))
  | .M5 => -θA
  | .M6 => -θB

variable {F : Type*} [CommRing F]

private theorem dval_level_pred (θA θB : F) (na nb e : ℕ) :
    dval θA θB na nb e = dval θA θB na nb (e + 1) - 2 * ((e : F) + 1 - 1) := by
  have h2 : ((e * (e - 1) : ℕ) : F) + 2 * (e : F) = (((e + 1) * (e + 1 - 1) : ℕ) : F) := by
    cases e with
    | zero => simp
    | succ f =>
      rw [show f + 1 - 1 = f from by omega, show f + 1 + 1 - 1 = f + 1 from by omega]
      push_cast
      ring
  simp only [dval]
  linear_combination h2

theorem delta_M1 (θA θB : F) (na nb e : ℕ) :
    dval θA θB na nb e = dval θA θB (na + 1) nb (e + 1) + delta θA θB (e + 1) MoveClass.M1 := by
  rw [dval_level_pred θA θB na nb e]
  simp only [dval, delta]
  push_cast
  ring

theorem delta_M2 (θA θB : F) (na nb e : ℕ) :
    dval θA θB na nb e = dval θA θB na (nb + 1) (e + 1) + delta θA θB (e + 1) MoveClass.M2 := by
  rw [dval_level_pred θA θB na nb e]
  simp only [dval, delta]
  push_cast
  ring

theorem delta_M3 (θA θB : F) (na nb e : ℕ) :
    dval θA θB na nb e
      = dval θA θB (na + 1) (nb + 1) (e + 1) + delta θA θB (e + 1) MoveClass.M3 := by
  rw [dval_level_pred θA θB na nb e]
  simp only [dval, delta]
  push_cast
  ring

theorem delta_M4 (θA θB : F) (na nb e : ℕ) :
    dval θA θB na nb e = dval θA θB na nb (e + 1) + delta θA θB (e + 1) MoveClass.M4 := by
  rw [dval_level_pred θA θB na nb e]
  simp only [dval, delta]
  push_cast
  ring

theorem delta_M5 (θA θB : F) (na nb k : ℕ) :
    dval θA θB na nb k = dval θA θB (na + 1) nb k + delta θA θB k MoveClass.M5 := by
  simp only [dval, delta]
  push_cast
  ring

theorem delta_M6 (θA θB : F) (na nb k : ℕ) :
    dval θA θB na nb k = dval θA θB na (nb + 1) k + delta θA θB k MoveClass.M6 := by
  simp only [dval, delta]
  push_cast
  ring

variable {KA KB : ℕ}

theorem diag_dropA (θA θB : F) (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i ≠ 0) :
    dval θA θB (ξ.dropA i).nA (ξ.dropA i).nB (ξ.dropA i).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M1 := by
  have key := delta_M1 θA θB (ξ.dropA i).nA (ξ.dropA i).nB (ξ.dropA i).n
  rw [ξ.nA_dropA i h, ξ.n_dropA i h, ξ.nB_dropA i] at key
  exact key

theorem diag_dropB (θA θB : F) (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j ≠ 0) :
    dval θA θB (ξ.dropB j).nA (ξ.dropB j).nB (ξ.dropB j).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M2 := by
  have key := delta_M2 θA θB (ξ.dropB j).nA (ξ.dropB j).nB (ξ.dropB j).n
  rw [ξ.nB_dropB j h, ξ.n_dropB j h, ξ.nA_dropB j] at key
  exact key

theorem diag_dropC (θA θB : F) (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    dval θA θB (ξ.dropC i j).nA (ξ.dropC i j).nB (ξ.dropC i j).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M3 := by
  have key := delta_M3 θA θB (ξ.dropC i j).nA (ξ.dropC i j).nB (ξ.dropC i j).n
  rw [ξ.nA_dropC i j h, ξ.nB_dropC i j h, ξ.n_dropC i j h] at key
  exact key

theorem diag_mergeAB (θA θB : F) (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (ha : ξ.a i ≠ 0)
    (hb : ξ.b j ≠ 0) :
    dval θA θB (ξ.mergeAB i j).nA (ξ.mergeAB i j).nB (ξ.mergeAB i j).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M4 := by
  have key := delta_M4 θA θB ξ.nA ξ.nB (ξ.mergeAB i j).n
  rw [ξ.n_mergeAB i j ha hb] at key
  rw [ξ.nA_mergeAB i j ha, ξ.nB_mergeAB i j hb]
  exact key

theorem diag_killA (θA θB : F) (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    dval θA θB (ξ.killA i j).nA (ξ.killA i j).nB (ξ.killA i j).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M5 := by
  have key := delta_M5 θA θB (ξ.killA i j).nA ξ.nB ξ.n
  rw [ξ.nA_killA i j h] at key
  rw [ξ.nB_killA i j h, ξ.n_killA i j h]
  exact key

theorem diag_killB (θA θB : F) (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    dval θA θB (ξ.killB i j).nA (ξ.killB i j).nB (ξ.killB i j).n
      = dval θA θB ξ.nA ξ.nB ξ.n + delta θA θB ξ.n MoveClass.M6 := by
  have key := delta_M6 θA θB ξ.nA (ξ.killB i j).nB ξ.n
  rw [ξ.nB_killB i j h] at key
  rw [ξ.nA_killB i j h, ξ.n_killB i j h]
  exact key

theorem sum_delta_eq_sub (θA θB : F) (k N : ℕ) (D : ℕ → F) (mv : ℕ → MoveClass)
    (hstep : ∀ r, r < N → D (r + 1) = D r + delta θA θB k (mv r)) :
    D N = D 0 + ∑ r ∈ Finset.range N, delta θA θB k (mv r) := by
  induction N with
  | zero => simp
  | succ m IH =>
    rw [Finset.sum_range_succ, hstep m (by omega), IH (fun r hr => hstep r (by omega))]
    ring

theorem sum_delta_eq_zero (θA θB : F) (k N : ℕ) (D : ℕ → F) (mv : ℕ → MoveClass)
    (hstep : ∀ r, r < N → D (r + 1) = D r + delta θA θB k (mv r))
    (h0 : D 0 = 0) (hN : D N = 0) :
    ∑ r ∈ Finset.range N, delta θA θB k (mv r) = 0 := by
  have := sum_delta_eq_sub θA θB k N D mv hstep
  rw [h0, hN, zero_add] at this
  exact this.symm

theorem familyA_delta_sum_zero (θA θB : F) (k : ℕ) (hu : (k : F) - 1 = -(θA + θB)) :
    delta θA θB k MoveClass.M3 + delta θA θB k MoveClass.M5 + delta θA θB k MoveClass.M6 = 0 := by
  simp only [delta]
  rw [hu]
  ring

theorem delta_M3_of_fullyTyped (θA θB : F) (k : ℕ) (hu : (k : F) - 1 = -(θA + θB)) :
    delta θA θB k MoveClass.M3 = θA + θB := by
  simp only [delta]
  rw [hu]
  ring

variable {K : Type*} [Field K]

def familyASum (x y z N₀ N₁ N₂ N₃ N₄ N₅ : K) : K :=
  N₀ * (x * (x + y))⁻¹ + N₁ * (x * (x + z))⁻¹ + N₂ * (y * (y + x))⁻¹
    + N₃ * (y * (y + z))⁻¹ + N₄ * (z * (z + x))⁻¹ + N₅ * (z * (z + y))⁻¹

theorem familyASum_one (x y z : K) :
    familyASum x y z 1 1 1 1 1 1
      = (x * (x + y))⁻¹ + (x * (x + z))⁻¹ + (y * (y + x))⁻¹ + (y * (y + z))⁻¹
          + (z * (z + x))⁻¹ + (z * (z + y))⁻¹ := by
  simp only [familyASum, one_mul]

theorem familyASum_eq {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (N₀ N₁ N₂ N₃ N₄ N₅ : K) :
    familyASum x y z N₀ N₁ N₂ N₃ N₄ N₅
      = -(((N₀ + N₅) * y + (N₁ + N₃) * z + (N₂ + N₄) * x) * (x * y * z)⁻¹) := by
  have hxy : x + y = -z := by linear_combination hsum
  have hxz : x + z = -y := by linear_combination hsum
  have hyx : y + x = -z := by linear_combination hsum
  have hyz : y + z = -x := by linear_combination hsum
  have hzx : z + x = -y := by linear_combination hsum
  have hzy : z + y = -x := by linear_combination hsum
  simp only [familyASum, hxy, hxz, hyx, hyz, hzx, hzy]
  field_simp
  ring

theorem familyASum_const {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (c : K) : familyASum x y z c c c c c c = 0 := by
  rw [familyASum_eq hx hy hz hsum]
  have : (c + c) * y + (c + c) * z + (c + c) * x = 0 := by linear_combination (c + c) * hsum
  rw [this, zero_mul, neg_zero]

theorem familyASum_blocks {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (c₁ c₂ : K) : familyASum x y z c₁ c₁ c₂ c₂ c₁ c₂ = 0 := by
  rw [familyASum_eq hx hy hz hsum]
  have : (c₁ + c₂) * y + (c₁ + c₂) * z + (c₂ + c₁) * x = 0 := by
    linear_combination (c₁ + c₂) * hsum
  rw [this, zero_mul, neg_zero]

theorem familyASum_blocks' {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (c₁ c₂ : K) : familyASum x y z c₁ c₁ c₁ c₂ c₂ c₂ = 0 := by
  rw [familyASum_eq hx hy hz hsum]
  have : (c₁ + c₂) * y + (c₁ + c₂) * z + (c₁ + c₂) * x = 0 := by
    linear_combination (c₁ + c₂) * hsum
  rw [this, zero_mul, neg_zero]

theorem familyASum_coincident {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0) (n₁ n₃ n₄ : K) (hcount : n₁ + n₄ = 2 * n₃) :
    familyASum x y z n₁ n₁ n₃ n₄ n₃ n₄ = 0 := by
  rw [familyASum_eq hx hy hz hsum]
  have : (n₁ + n₄) * y + (n₁ + n₄) * z + (n₃ + n₃) * x = 0 := by
    linear_combination (n₁ + n₄) * hsum - x * hcount
  rw [this, zero_mul, neg_zero]

theorem counting_identity (c : ℕ) :
    c * (c - 1) * (c - 1) * (c - 2) + c * (c - 1) * ((c - 2) * (c - 3))
      = 2 * (c * ((c - 1) * (c - 2)) * (c - 2)) := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | e + 3 =>
    rw [show e + 3 - 1 = e + 2 from by omega, show e + 3 - 2 = e + 1 from by omega,
      show e + 3 - 3 = e from by omega]
    ring

end Rhone.Algebra.RhoZero
