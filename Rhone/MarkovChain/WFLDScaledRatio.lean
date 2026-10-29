/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationaryRatio
public import Mathlib.Tactic.FunProp

/-!
# Scaled exact finite-chain LD ratio in the rare-mutation large-population regime

Source: ohta_kimura1971_ld, eq. (9), p. 574. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Filter
open scoped Topology

def ldRetentionSlope (t v : ℝ) : ℝ := -8*v+24*t*v^2-32*t^2*v^3+16*t^3*v^4

def ldMixedSlope (t R v : ℝ) : ℝ :=
  ldRetentionSlope t v-R/2-(R/2)*t*ldRetentionSlope t v

def ldSquareSlope (t R v : ℝ) : ℝ :=
  ldRetentionSlope t v-R+(R^2/4)*t-R*t*ldRetentionSlope t v+
    (R^2/4)*t^2*ldRetentionSlope t v

def ldScaledNumerator (t R v : ℝ) : ℝ :=
  -((-5+8*t-4*t^2)+ldMixedSlope t R v+t*(-5+8*t-4*t^2)*ldMixedSlope t R v)

def ldScaledDenominator (t R v : ℝ) : ℝ :=
  let b := -((-3+4*t-4*t^2)+ldSquareSlope t R v+t*(-3+4*t-4*t^2)*ldSquareSlope t R v)
  (1-t)*(ldScaledNumerator t R v*b-
    4*(1-t)^2*(1-2*t)^2*(1+t*ldMixedSlope t R v)*(1+t*ldSquareSlope t R v))

theorem ld_sigma_scaled_factors (m R v : ℝ) (hm : m ≠ 0) :
    ldSigmaNumerator m (R/(2*m)) (v/m) = m^5*ldScaledNumerator (1/m) R v ∧
    ldSigmaDenominator m (R/(2*m)) (v/m) = m^5*ldScaledDenominator (1/m) R v := by
  constructor
  · unfold ldSigmaNumerator ldScaledNumerator ldMixedSlope ldRetentionSlope
    field_simp [hm]
    ring
  · unfold ldSigmaDenominator ldScaledDenominator ldScaledNumerator
      ldMixedSlope ldSquareSlope ldRetentionSlope
    dsimp only
    field_simp [hm]
    ring

/-- Source: ohta_kimura1971_ld, eq. (9), p. 574. -/
theorem ld_scaled_ratio_limit (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun z : ℝ × ℝ => ldScaledNumerator z.1 R z.2 / ldScaledDenominator z.1 R z.2)
      (𝓝 (0,0)) (𝓝 ((10+R)/(22+13*R+R^2))) := by
  have hd : ldScaledDenominator 0 R 0 ≠ 0 := by
    have hp : 0 < 11+13*R/2+R^2/2 := by positivity
    convert hp.ne' using 1
    unfold ldScaledDenominator ldScaledNumerator ldMixedSlope ldSquareSlope ldRetentionSlope
    ring
  have hn : Continuous (fun z : ℝ × ℝ => ldScaledNumerator z.1 R z.2) := by
    unfold ldScaledNumerator ldMixedSlope ldRetentionSlope
    fun_prop
  have he : Continuous (fun z : ℝ × ℝ => ldScaledDenominator z.1 R z.2) := by
    unfold ldScaledDenominator ldScaledNumerator ldMixedSlope ldSquareSlope ldRetentionSlope
    dsimp only
    fun_prop
  have hh : ContinuousAt (fun z : ℝ × ℝ =>
      ldScaledNumerator z.1 R z.2 / ldScaledDenominator z.1 R z.2) (0,0) :=
    hn.continuousAt.div he.continuousAt hd
  have hv : ldScaledNumerator 0 R 0 / ldScaledDenominator 0 R 0 =
      (10+R)/(22+13*R+R^2) := by
    have hz : 22+13*R+R^2 ≠ 0 := by positivity
    apply (div_eq_div_iff hd hz).2
    unfold ldScaledDenominator ldScaledNumerator ldMixedSlope ldSquareSlope ldRetentionSlope
    dsimp only
    ring
  simpa only [hv] using hh.tendsto

end Rhone.MarkovChain.WFAllocationLD
