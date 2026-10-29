/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationIdealTransform
public import Rhone.Statistics.Identifiability.MutationMomentSurjectivity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Smooth positive pulse coordinates and the exact limiting moment map -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationMomentCoordinates
open MutationPulseKernel MutationIdealTransform
open MutationMomentSurjectivity

noncomputable def coord (L k : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-Real.log x.1, -Real.log (1 - x.2 / L) / k)

noncomputable def idealVector (r k : ℝ) (p : ℝ × ℝ) : Fin 5 → ℝ :=
  NormedSpace.exp (p.1 • C) *ᵥ
    (NormedSpace.exp (p.2 • B 0 r k) *ᵥ (fun _ => 1))

theorem residual_mem_Ioo {L : ℝ} (hL : 0 < L) {x : ℝ × ℝ}
    (hx : x ∈ parameterDomain L) : 0 < 1 - x.2 / L ∧ 1 - x.2 / L < 1 := by
  constructor
  · exact sub_pos.mpr ((div_lt_one hL).2 hx.2.2.2)
  · exact sub_lt_self _ (div_pos hx.2.2.1 hL)

theorem coord_pos {L k : ℝ} (hL : 0 < L) (hk : 0 < k) {x : ℝ × ℝ}
    (hx : x ∈ parameterDomain L) : 0 < (coord L k x).1 ∧ 0 < (coord L k x).2 := by
  have hq := residual_mem_Ioo hL hx
  exact ⟨neg_pos.mpr (Real.log_neg hx.1 hx.2.1),
    div_pos (neg_pos.mpr (Real.log_neg hq.1 hq.2)) hk⟩

theorem contDiffOn_coord {L : ℝ} (hL : 0 < L) (k : ℝ) :
    ContDiffOn ℝ ∞ (coord L k) (parameterDomain L) := by
  have hf : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => -Real.log x.1) (parameterDomain L) :=
    (contDiff_fst.contDiffOn.log fun x hx => ne_of_gt hx.1).neg
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => -Real.log (1 - x.2 / L) / k)
      (parameterDomain L) :=
    (((contDiffOn_const.sub (contDiff_snd.contDiffOn.div_const L)).log
      fun x hx => ne_of_gt (residual_mem_Ioo hL hx).1).neg).div_const k
  exact hf.prodMk hg

@[simp] theorem exp_neg_coord_fst {L : ℝ} (k : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ parameterDomain L) : Real.exp (-(coord L k x).1) = x.1 := by
  simpa [coord] using Real.exp_log hx.1

@[simp] theorem exp_discount_coord_snd {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    Real.exp (-k * (coord L k x).2) = 1 - x.2 / L := by
  have he : -k * (coord L k x).2 = Real.log (1 - x.2 / L) := by
    dsimp [coord]
    field_simp
  rw [he, Real.exp_log (residual_mem_Ioo hL hx).1]

@[simp] theorem exp_double_discount_coord_snd {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    Real.exp (-2 * k * (coord L k x).2) = (1 - x.2 / L) ^ 2 := by
  have he : -2 * k * (coord L k x).2 =
      -k * (coord L k x).2 + -k * (coord L k x).2 := by ring
  rw [he, Real.exp_add, exp_discount_coord_snd hL hk hx]
  ring

theorem ideal_one_coord {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (r : ℝ)
    {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    idealVector r k (coord L k x) 3 = 1 - x.1 + x.1 * (1 - x.2 / L) := by
  have h := ideal_one_locus_transform (coord L k x).1 (coord L k x).2 r k
  rw [exp_neg_coord_fst k hx, exp_discount_coord_snd hL hk hx] at h
  exact h

theorem ideal_two_coord {L k : ℝ} (hL : 0 < L) (hk : 0 < k) (r : ℝ)
    {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    idealVector r k (coord L k x) 0 = 1 - x.1 + x.1 * (1 - x.2 / L) ^ 2 := by
  rw [idealVector, ideal_two_locus_transform, exp_neg_coord_fst k hx,
    exp_double_discount_coord_snd hL hk hx]

def momentExtract (L : ℝ) (v : Fin 5 → ℝ) : ℝ × ℝ :=
  (L * (1 - v 3), L ^ 2 * (1 - 2 * v 3 + v 0))

theorem ideal_extraction_eq_momentMap {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    (r : ℝ) {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    momentExtract L (idealVector r k (coord L k x)) = momentMap x := by
  unfold momentExtract
  rw [ideal_one_coord hL hk r hx, ideal_two_coord hL hk r hx]
  ext <;> dsimp [momentMap] <;> field_simp <;> ring

end Rhone.Statistics.Identifiability.MutationMomentCoordinates
