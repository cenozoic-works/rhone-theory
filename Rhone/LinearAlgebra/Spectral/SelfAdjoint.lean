/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Balance
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Complex.Basic

/-! # Self-adjointness in the `W`-metric, and reality of the spectrum -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

variable {i j : ℕ} {θA θB ρ : ℝ}

noncomputable def innerW (i j : ℕ) (x : ℝ) (u v : Fin (min i j + 1) → ℝ) : ℝ :=
  ∑ t, u t * v t / W i j x (t : ℕ)

theorem innerW_comm (u v : Fin (min i j + 1) → ℝ) : innerW i j ρ u v = innerW i j ρ v u := by
  unfold innerW
  exact Finset.sum_congr rfl fun t _ => by ring

theorem innerW_nonneg (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) : 0 ≤ innerW i j ρ u u := by
  unfold innerW
  refine Finset.sum_nonneg fun t _ => ?_
  exact div_nonneg (mul_self_nonneg _) (W_pos hρ _).le

theorem innerW_pos (hρ : 0 < ρ) {u : Fin (min i j + 1) → ℝ} (hu : u ≠ 0) :
    0 < innerW i j ρ u u := by
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hu
  unfold innerW
  refine Finset.sum_pos' (fun s _ => div_nonneg (mul_self_nonneg _) (W_pos hρ _).le)
    ⟨t, Finset.mem_univ t, ?_⟩
  have hut : u t ≠ 0 := by simpa using ht
  exact div_pos (mul_self_pos.2 hut) (W_pos hρ _)

theorem innerW_selfAdjoint (hρ : 0 < ρ) (u v : Fin (min i j + 1) → ℝ) :
    innerW i j ρ ((T i j θA θB ρ) *ᵥ u) v = innerW i j ρ u ((T i j θA θB ρ) *ᵥ v) := by
  have hW : ∀ t : Fin (min i j + 1), W i j ρ (t : ℕ) ≠ 0 := fun _ => ne_of_gt (W_pos hρ _)
  unfold innerW
  have hL : ∀ t : Fin (min i j + 1),
      ((T i j θA θB ρ) *ᵥ u) t * v t / W i j ρ (t : ℕ)
        = ∑ s, T i j θA θB ρ t s * u s * v t / W i j ρ (t : ℕ) := by
    intro t
    rw [mulVec_apply, Finset.sum_mul, Finset.sum_div]
  have hR : ∀ t : Fin (min i j + 1),
      u t * ((T i j θA θB ρ) *ᵥ v) t / W i j ρ (t : ℕ)
        = ∑ s, T i j θA θB ρ t s * u t * v s / W i j ρ (t : ℕ) := by
    intro t
    rw [mulVec_apply, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  have hdb := detailed_balance (i := i) (j := j) (θA := θA) (θB := θB) (ρ := ρ) t s
  rw [div_eq_div_iff (hW s) (hW t)]
  linear_combination (-(u t * v s)) * hdb

noncomputable def symT (i j : ℕ) (θA θB ρ : ℝ) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ := fun t s =>
  T i j θA θB ρ t s * Real.sqrt (W i j ρ (s : ℕ) / W i j ρ (t : ℕ))

theorem symT_eq_conj (hρ : 0 < ρ) :
    symT i j θA θB ρ
      = Matrix.diagonal (fun t : Fin (min i j + 1) => (Real.sqrt (W i j ρ (t : ℕ)))⁻¹)
          * T i j θA θB ρ * Matrix.diagonal (fun s : Fin (min i j + 1) =>
            Real.sqrt (W i j ρ (s : ℕ))) := by
  ext t s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, symT,
    Real.sqrt_div (W_pos hρ (s : ℕ)).le]
  ring

theorem symT_isSymm (hρ : 0 < ρ) : (symT i j θA θB ρ).IsSymm := by
  ext t s
  rw [Matrix.transpose_apply, symT, symT]
  have hWt : 0 < W i j ρ (t : ℕ) := W_pos hρ _
  have hWs : 0 < W i j ρ (s : ℕ) := W_pos hρ _
  have hdb := detailed_balance (i := i) (j := j) (θA := θA) (θB := θB) (ρ := ρ) t s
  have hts : T i j θA θB ρ s t = T i j θA θB ρ t s * W i j ρ (s : ℕ) / W i j ρ (t : ℕ) := by
    field_simp
    linear_combination -hdb
  have hsqrt : Real.sqrt (W i j ρ (t : ℕ) / W i j ρ (s : ℕ))
      = W i j ρ (t : ℕ) / W i j ρ (s : ℕ) * Real.sqrt (W i j ρ (s : ℕ) / W i j ρ (t : ℕ)) := by
    rw [Real.sqrt_div hWt.le, Real.sqrt_div hWs.le]
    have h1 : (0 : ℝ) < Real.sqrt (W i j ρ (t : ℕ)) := Real.sqrt_pos.2 hWt
    have h2 : (0 : ℝ) < Real.sqrt (W i j ρ (s : ℕ)) := Real.sqrt_pos.2 hWs
    have e1 : Real.sqrt (W i j ρ (t : ℕ)) * Real.sqrt (W i j ρ (t : ℕ)) = W i j ρ (t : ℕ) :=
      Real.mul_self_sqrt hWt.le
    have e2 : Real.sqrt (W i j ρ (s : ℕ)) * Real.sqrt (W i j ρ (s : ℕ)) = W i j ρ (s : ℕ) :=
      Real.mul_self_sqrt hWs.le
    have h1' : Real.sqrt (W i j ρ (t : ℕ)) ≠ 0 := ne_of_gt h1
    have h2' : Real.sqrt (W i j ρ (s : ℕ)) ≠ 0 := ne_of_gt h2
    have hWt' : W i j ρ (t : ℕ) ≠ 0 := ne_of_gt hWt
    have hWs' : W i j ρ (s : ℕ) ≠ 0 := ne_of_gt hWs
    field_simp
    nlinarith [e1, e2]
  have hWt' : W i j ρ (t : ℕ) ≠ 0 := ne_of_gt hWt
  have hWs' : W i j ρ (s : ℕ) ≠ 0 := ne_of_gt hWs
  rw [hts, hsqrt]
  field_simp

theorem eigen_im_eq_zero (hρ : 0 < ρ) {z : ℂ} {v : Fin (min i j + 1) → ℂ} (hv : v ≠ 0)
    (heig : ∀ t, ∑ s, ((T i j θA θB ρ t s : ℝ) : ℂ) * v s = z * v t) :
    z.im = 0 := by
  classical
  have hWpos : ∀ t : Fin (min i j + 1), 0 < W i j ρ (t : ℕ) := fun _ => W_pos hρ _
  have hWne : ∀ t : Fin (min i j + 1), ((W i j ρ (t : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro t
    simpa using ne_of_gt (hWpos t)
  set f : Fin (min i j + 1) → Fin (min i j + 1) → ℂ := fun t s =>
    ((T i j θA θB ρ t s : ℝ) : ℂ) * v s * (starRingEnd ℂ) (v t)
      / ((W i j ρ (t : ℕ) : ℝ) : ℂ) with hf
  set N : ℝ := ∑ t, Complex.normSq (v t) / W i j ρ (t : ℕ) with hNdef
  have hNpos : 0 < N := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hv
    have hvt : v t ≠ 0 := by simpa using ht
    exact Finset.sum_pos' (fun s _ => div_nonneg (Complex.normSq_nonneg _) (hWpos s).le)
      ⟨t, Finset.mem_univ t, div_pos (Complex.normSq_pos.2 hvt) (hWpos t)⟩
  have hB1 : ∑ t, ∑ s, f t s = z * (N : ℂ) := by
    have hrow : ∀ t, ∑ s, f t s = z * ((Complex.normSq (v t) / W i j ρ (t : ℕ) : ℝ) : ℂ) := by
      intro t
      have hsplit : ∑ s, f t s
          = (∑ s, ((T i j θA θB ρ t s : ℝ) : ℂ) * v s) * (starRingEnd ℂ) (v t)
              / ((W i j ρ (t : ℕ) : ℝ) : ℂ) := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [hsplit, heig t, mul_assoc, Complex.mul_conj]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun t _ => hrow t, ← Finset.mul_sum, hNdef]
    push_cast
    ring
  have hconjf : ∀ t s, (starRingEnd ℂ) (f t s) = f s t := by
    intro t s
    rw [hf]
    simp only [map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [div_eq_div_iff (hWne t) (hWne s)]
    have hdb : ((T i j θA θB ρ t s * W i j ρ (s : ℕ) : ℝ) : ℂ)
        = ((T i j θA θB ρ s t * W i j ρ (t : ℕ) : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ))
        (detailed_balance (i := i) (j := j) (θA := θA) (θB := θB) (ρ := ρ) t s)
    push_cast at hdb
    linear_combination (v t * (starRingEnd ℂ) (v s)) * hdb
  have hB2 : (starRingEnd ℂ) (∑ t, ∑ s, f t s) = ∑ t, ∑ s, f t s := by
    simp only [map_sum, hconjf]
    exact Finset.sum_comm
  rw [hB1, map_mul, Complex.conj_ofReal] at hB2
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hNpos
  have hzz : (starRingEnd ℂ) z = z := mul_right_cancel₀ hNne hB2
  exact Complex.conj_eq_iff_im.1 hzz

end Rhone.LinearAlgebra.Spectral
