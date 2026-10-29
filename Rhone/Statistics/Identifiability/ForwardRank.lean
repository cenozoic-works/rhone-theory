/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExit
public import Rhone.Statistics.Identifiability.IntervalRank

/-! # The two surviving-pair starting states give independent time densities -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Set
namespace Rhone.Statistics.Identifiability

noncomputable def forwardDensity (k : Nat) (c q : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
      (MarkovChain.Identifiability.pairDensity c) 0 t

noncomputable def forwardDensityD (k : Nat) (c q : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
      (MarkovChain.Identifiability.pairGenerator k c q *ᵥ MarkovChain.Identifiability.pairDensity c)
      0 t

theorem forwardDensity_hasDerivAt (k : Nat) (c q : ℝ) (i : Fin 2) (t : ℝ) :
    HasDerivAt (forwardDensity k c q i) (forwardDensityD k c q i t) t :=
  flowOutput_hasDerivAt_right _ _ _ _

theorem forward_wronskian (k : Nat) (c q t : ℝ) :
    forwardDensity k c q 0 t * forwardDensityD k c q 1 t -
    forwardDensity k c q 1 t * forwardDensityD k c q 0 t =
    2*q*c^2 * (NormedSpace.exp (t • MarkovChain.Identifiability.pairGenerator k c q)).det := by
  simp only [forwardDensity, forwardDensityD, flowOutput, pow_zero, Matrix.one_mul]
  simp [Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, MarkovChain.Identifiability.pairDensity,
        MarkovChain.Identifiability.pairGenerator, Matrix.det_fin_two]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem forward_wronskian_ne_zero (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) (t : ℝ) :
    forwardDensity k c q 0 t * forwardDensityD k c q 1 t -
    forwardDensity k c q 1 t * forwardDensityD k c q 0 t ≠ 0 := by
  rw [forward_wronskian]
  have hdet : (NormedSpace.exp (t • MarkovChain.Identifiability.pairGenerator k c q)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
        (NormedSpace.isUnit_exp (t • MarkovChain.Identifiability.pairGenerator k c q))).ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq) (pow_ne_zero _ hc)) hdet

theorem forward_rank_two (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    ∃ t ∈ Icc (1 : ℝ) 2,
      forwardDensity k c q 0 1 * forwardDensity k c q 1 t -
      forwardDensity k c q 1 1 * forwardDensity k c q 0 t ≠ 0 :=
  column_rank_two_of_wronskian _ _ (by norm_num)
    (forwardDensity_hasDerivAt k c q 0 1) (forwardDensity_hasDerivAt k c q 1 1)
    (forward_wronskian_ne_zero k hc hq 1)

end Rhone.Statistics.Identifiability
