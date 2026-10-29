/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairLaplaceTransform
public import Rhone.Statistics.Identifiability.IslandThreeFirstMarginal
public import Rhone.Statistics.ThreeSiteSeparator.SourceAlgebra

/-! # Explicit discounted reward potentials for the literal two-island source -/

@[expose] public section

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability

def preDenominator (m a : ℝ) : ℝ := (a+3)*(a+1)+(4*a+6)*m

def prePotential (m a w0 w1 : ℝ) : Fin 3 → ℝ :=
  ![(3*(a+1+m)*w0+3*m*w1)/preDenominator m a,
    (3*m*w0+(a+3+3*m)*w1)/preDenominator m a,
    6*m*(3*m*w0+(a+3+3*m)*w1)/(preDenominator m a*(a+6*m))]

lemma preDenominator_pos {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) :
    0 < preDenominator m a := by unfold preDenominator; positivity

lemma prePotential_equation {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (w0 w1 : ℝ) :
    (threeGenerator 0 1 m - a • 1)*ᵥ prePotential m a w0 w1 = -![3*w0,w1,0] := by
  have hd : preDenominator m a ≠ 0 := (preDenominator_pos hm ha).ne'
  have he : a+6*m ≠ 0 := by positivity
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;>
    simp [threeGenerator, totalMigration, prePotential, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.sub_apply, smul_eq_mul] <;>
    field_simp <;> simp only [preDenominator] <;> ring

lemma firstRate_basis_zero :
    (fun i => IslandThreeTimes.firstRate 1 i 0) = (![3,0,0] : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> norm_num [IslandThreeTimes.firstRate]

lemma firstRate_basis_one :
    (fun i => IslandThreeTimes.firstRate 1 i 1) = (![0,1,0] : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> norm_num [IslandThreeTimes.firstRate]

end Rhone.Statistics.ThreeSiteSeparator
