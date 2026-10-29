/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Semigroup

/-! # Duality of finite chains with respect to a function -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset NormedSpace Matrix

variable {S T : Type*} [Fintype S] [Fintype T]

namespace FinChain

structure MomentDuality [DecidableEq S] [DecidableEq T] (C : FinChain S) (D : FinChain T)
    (H : Matrix S T ℝ) : Prop where
  expectN_eq : ∀ (n : ℕ) (x : S) (y : T),
    C.expectN n (fun s => H s y) x = D.expectN n (fun r => H x r) y

variable [DecidableEq S] [DecidableEq T] {C : FinChain S} {D : FinChain T} {H : Matrix S T ℝ}

omit [Fintype T] [DecidableEq T] in
theorem expectN_col (C : FinChain S) (H : Matrix S T ℝ) (n : ℕ) (x : S) (y : T) :
    C.expectN n (fun s => H s y) x = (C.stepN n * H) x y := by
  rw [expectN_apply, Matrix.mul_apply]

omit [Fintype S] [DecidableEq S] in
theorem expectN_row (D : FinChain T) (H : Matrix S T ℝ) (n : ℕ) (x : S) (y : T) :
    D.expectN n (fun r => H x r) y = (H * (D.stepN n)ᵀ) x y := by
  rw [expectN_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun r _ => by rw [Matrix.transpose_apply, mul_comm]

theorem MomentDuality.stepN_mul (h : C.MomentDuality D H) (n : ℕ) :
    C.stepN n * H = H * (D.stepN n)ᵀ := by
  ext x y
  rw [← expectN_col, ← expectN_row, h.expectN_eq]

theorem MomentDuality.step (h : C.MomentDuality D H) : C.P * H = H * D.Pᵀ := by
  have := h.stepN_mul 1
  rwa [stepN_one, stepN_one] at this

theorem MomentDuality.of_step (h : C.P * H = H * D.Pᵀ) : C.MomentDuality D H := by
  refine ⟨fun n x y => ?_⟩
  rw [expectN_col, expectN_row]
  have hn : C.stepN n * H = H * (D.stepN n)ᵀ := by
    induction n with
    | zero => simp [stepN_zero]
    | succ n ih =>
      rw [stepN_succ', Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← Matrix.transpose_mul, ← stepN_succ]
  rw [hn]

theorem momentDuality_iff_step : C.MomentDuality D H ↔ C.P * H = H * D.Pᵀ :=
  ⟨MomentDuality.step, MomentDuality.of_step⟩

end FinChain

namespace RateChain

private theorem hasSum_exp [DecidableEq S] (A : Matrix S S ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) (exp A) := by
  open scoped Matrix.Norms.Operator in
  exact exp_series_hasSum_exp' (𝕂 := ℝ) A

theorem exp_mul_eq_mul_exp [DecidableEq S] [DecidableEq T] {A : Matrix S S ℝ}
    {B : Matrix T T ℝ} {H : Matrix S T ℝ} (h : A * H = H * B) : exp A * H = H * exp B := by
  have hpow : ∀ n : ℕ, A ^ n * H = H * B ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← pow_succ]
  let L : Matrix S S ℝ →+ Matrix S T ℝ :=
    { toFun := fun M => M * H
      map_zero' := Matrix.zero_mul _
      map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let L' : Matrix T T ℝ →+ Matrix S T ℝ :=
    { toFun := fun M => H * M
      map_zero' := Matrix.mul_zero _
      map_add' := fun _ _ => Matrix.mul_add _ _ _ }
  have hL : Continuous L := continuous_id.matrix_mul continuous_const
  have hL' : Continuous L' := continuous_const.matrix_mul continuous_id
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (A ^ n * H)) (exp A * H) := by
    have hs := (hasSum_exp A).map L hL
    have e : (L ∘ fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) =
        fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (A ^ n * H) :=
      funext fun n => Matrix.smul_mul _ _ _
    rw [e] at hs
    exact hs
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (A ^ n * H)) (H * exp B) := by
    have hs := (hasSum_exp B).map L' hL'
    have e : (L' ∘ fun n : ℕ => ((n.factorial : ℝ)⁻¹) • B ^ n) =
        fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (A ^ n * H) := funext fun n => by
      change H * (((n.factorial : ℝ)⁻¹) • B ^ n) = _
      rw [Matrix.mul_smul, hpow]
    rw [e] at hs
    exact hs
  exact h1.unique h2

structure MomentDuality [DecidableEq S] [DecidableEq T] (R : RateChain S) (R' : RateChain T)
    (H : Matrix S T ℝ) : Prop where
  semigroup_mul : ∀ t : ℝ, R.semigroup t * H = H * (R'.semigroup t)ᵀ

variable [DecidableEq S] [DecidableEq T] {R : RateChain S} {R' : RateChain T}
  {H : Matrix S T ℝ}

theorem MomentDuality.of_generator (h : R.Q * H = H * R'.Qᵀ) : R.MomentDuality R' H := by
  refine ⟨fun t => ?_⟩
  have ht : (t • R.Q) * H = H * (t • R'.Qᵀ) := by rw [Matrix.smul_mul, Matrix.mul_smul, h]
  rw [semigroup, semigroup, exp_mul_eq_mul_exp ht, ← Matrix.transpose_smul,
    Matrix.exp_transpose]

theorem MomentDuality.semigroup_apply (h : R.MomentDuality R' H) (t : ℝ) (x : S) (y : T) :
    ∑ s, R.semigroup t x s * H s y = ∑ r, R'.semigroup t y r * H x r := by
  have := congrFun (congrFun (h.semigroup_mul t) x) y
  rw [Matrix.mul_apply, Matrix.mul_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun r _ => by rw [Matrix.transpose_apply, mul_comm]

theorem MomentDuality.semigroupChain (h : R.MomentDuality R' H) (t : ℝ) (ht : 0 ≤ t) :
    (R.semigroupChain t ht).MomentDuality (R'.semigroupChain t ht) H :=
  FinChain.MomentDuality.of_step (h.semigroup_mul t)

end RateChain

end Rhone.MarkovChain
