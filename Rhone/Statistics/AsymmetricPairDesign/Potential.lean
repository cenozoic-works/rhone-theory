/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AsymmetricPairDesign.Generator
public import Mathlib.Tactic.Ring

/-! # Rational resolvent potentials of the asymmetric absorption generator -/

@[expose] public section

open scoped Matrix
namespace Rhone.Statistics.AsymmetricPairDesign

noncomputable def denominator (a b c d k : ℝ) : ℝ :=
  k ^ 3 + (3 * a + 3 * b + c + d) * k ^ 2 + 
    (2 * a ^ 2 + 4 * a * b + a * c + 3 * a * d + 2 * b ^ 2 + 3 * b * c + b * d + c * d) * k + 
    meanDenominator a b c d

noncomputable def potential (a b c d k : ℝ) : Fin 3 → ℝ :=
  ![(c * (k * k + k * (a + 3 * b + d) + a * d + b * d + 2 * b * b) + 2 * a * a * d) /
      denominator a b c d k,
    (b * c * (k + d + 2 * b) + a * d * (k + c + 2 * a)) / denominator a b c d k,
    (d * (k * k + k * (3 * a + b + c) + a * c + b * c + 2 * a * a) + 2 * b * b * c) /
      denominator a b c d k]

theorem denominator_pos {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) : 0 < denominator a b c d k := by
  have hD := mean_denominator_pos ha hb hc hd
  unfold denominator
  positivity

theorem potential_pos {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) (i : Fin 3) :
    0 < potential a b c d k i := by
  have hD := denominator_pos ha hb hc hd hk
  fin_cases i <;> change 0 < _ / _ <;> exact div_pos (by positivity) hD

theorem potential_equation {a b c d k : ℝ} (hD : denominator a b c d k ≠ 0) :
    (generator a b c d - k • 1) *ᵥ potential a b c d k = -rate c d := by
  ext i
  fin_cases i <;>
    simp [generator, potential, rate, Matrix.mulVec, Matrix.one_apply, dotProduct,
      Fin.sum_univ_succ] <;>
    field_simp [hD] <;> simp only [denominator, meanDenominator] <;> ring

theorem potential_balance {a b c d k : ℝ} (hD : denominator a b c d k ≠ 0) :
    (k + a + b) * potential a b c d k 1 =
      b * potential a b c d k 0 + a * potential a b c d k 2 := by
  have h := congrFun (potential_equation hD) 1
  simp [generator, rate, Matrix.mulVec, Matrix.one_apply, dotProduct,
    Fin.sum_univ_succ] at h
  nlinarith

end Rhone.Statistics.AsymmetricPairDesign
