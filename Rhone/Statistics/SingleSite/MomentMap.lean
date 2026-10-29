/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ScalarPostZeroOnset

/-! # Algebraic two-epoch candidate moment map -/

@[expose] public section

noncomputable section
open scoped Topology
namespace Rhone.Statistics.SingleSite

def pairMoment (k x : ℝ) : ℝ := x / (x + k)
def tripleMoment (k x : ℝ) : ℝ := 2 * x ^ 2 / ((2 * x + k) * (x + k))
def ePair (k τ x : ℝ) : ℝ := Real.exp (-(x + k) * τ)
def eTriple (k τ x : ℝ) : ℝ := Real.exp (-(3 * x + 3 * k / 2) * τ)
def crossFactor (k τ x : ℝ) : ℝ :=
  3 * x * (ePair k τ x - eTriple k τ x) / (2 * x + k / 2)
def firstCoordinate (k τ x y : ℝ) : ℝ :=
  pairMoment k x + ePair k τ x * (pairMoment k y - pairMoment k x)
def secondCoordinate (k τ x y : ℝ) : ℝ :=
  tripleMoment k x + eTriple k τ x * (tripleMoment k y - tripleMoment k x) +
    (pairMoment k y - pairMoment k x) * crossFactor k τ x

def pairDerivative (k : ℝ) : ℝ := k / (1 + k) ^ 2
def tripleDerivative (k : ℝ) : ℝ := 2 * k * (3 + 2 * k) / ((1 + k) ^ 2 * (2 + k) ^ 2)
def determinantExpression (k τ : ℝ) : ℝ :=
  (pairDerivative k * (1 - ePair k τ 1)) *
      (tripleDerivative k * eTriple k τ 1 + pairDerivative k * crossFactor k τ 1) -
    (pairDerivative k * ePair k τ 1) *
      (tripleDerivative k * (1 - eTriple k τ 1) - pairDerivative k * crossFactor k τ 1)

lemma derivative_gap {k : ℝ} (hk : 0 < k) :
    3 * pairDerivative k / (2 + k / 2) - tripleDerivative k =
      2 * k ^ 2 / ((1 + k) * (2 + k) ^ 2 * (4 + k)) := by
  have h1 : 1 + k ≠ 0 := by positivity
  have h2 : 2 + k ≠ 0 := by positivity
  have h4 : 4 + k ≠ 0 := by positivity
  have hd : 2 + k / 2 ≠ 0 := by positivity
  unfold pairDerivative tripleDerivative
  field_simp
  ring

lemma determinant_formula {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    determinantExpression k τ =
      2 * k ^ 3 * (ePair k τ 1 - eTriple k τ 1) /
        ((1 + k) ^ 3 * (2 + k) ^ 2 * (4 + k)) := by
  have he : determinantExpression k τ =
      pairDerivative k * (ePair k τ 1 - eTriple k τ 1) *
        (3 * pairDerivative k / (2 + k / 2) - tripleDerivative k) := by
    unfold determinantExpression crossFactor
    ring
  rw [he, derivative_gap hk]
  unfold pairDerivative
  have h1 : 1 + k ≠ 0 := by positivity
  have h2 : 2 + k ≠ 0 := by positivity
  have h4 : 4 + k ≠ 0 := by positivity
  field_simp

lemma determinant_positive {k τ : ℝ} (hk : 0 < k) (hτ : 0 < τ) :
    0 < determinantExpression k τ := by
  rw [determinant_formula hk]
  have hE : eTriple k τ 1 < ePair k τ 1 := by
    unfold eTriple ePair
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact div_pos (mul_pos (by positivity) (sub_pos.mpr hE)) (by positivity)

end Rhone.Statistics.SingleSite
