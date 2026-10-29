/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.HudsonCovariance
public import Rhone.Computation.OhtaKimuraProof
public import Rhone.Coalescent.TwoLocusLD
public import Rhone.Coalescent.FullARGTwoSampleCovariance
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable two-locus pair-time covariance equals the specification

Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; griffiths1991_two_locus_graph,
p. 103; mcvean2002, eq. (9)–(12), pp. 988–989; wilton_carmi_hobolth2015, eq. (5). -/

@[expose] public section
namespace Rhone.Computation.HudsonCovariance
open MeasureTheory ProbabilityTheory Coalescent MarkovChain Coalescent.IntervalProcess
    MarkovChain.IntervalProcess
open scoped ENNReal

theorem denom_eq (ρ : Rat) :
    ((denom ρ : Rat) : ℝ) = (ρ : ℝ) ^ 2 + 13 * (ρ : ℝ) + 18 := by
  simp [denom]

theorem chainValue_eq (ρ : Rat) (k : Nat) :
    ((chainValue ρ k : Rat) : ℝ) = twoLocusValue (ρ : ℝ) k := by
  match k with
  | 0 => simp [chainValue, twoLocusValue, denom]
  | 1 => simp [chainValue, twoLocusValue, denom]
  | 2 => simp [chainValue, twoLocusValue, denom]
  | k + 3 => simp [chainValue, twoLocusValue]

theorem pairTimeCovariance_eq_chainValue (ρ : Rat) :
    pairTimeCovariance ρ = chainValue ρ 2 := rfl

theorem pairTimeCovariance_eq (R : Rat) (hR : 0 ≤ R) (x y : GenomicProbe)
    (hxy : x.val < y.val) :
    cov[fun G : Genealogy 2 => (G x 0 1).toReal, fun G : Genealogy 2 => (G y 0 1).toReal;
        fullARGGenealogyLaw 2 (R : ℝ)] =
      ((pairTimeCovariance (R * (y.val - x.val)) : Rat) : ℝ) := by
  rw [fullARG_two_sample_pairTime_covariance (R : ℝ) (by exact_mod_cast hR) x y hxy]
  simp [pairTimeCovariance, denom]

theorem pairTimeProduct_eq (R : Rat) (hR : 0 ≤ R) (x y : GenomicProbe)
    (hxy : x.val < y.val) :
    ∫⁻ G, G x 0 1 * G y 0 1 ∂fullARGGenealogyLaw 2 (R : ℝ) =
      ENNReal.ofReal ((pairTimeProduct (R * (y.val - x.val)) : Rat) : ℝ) := by
  rw [fullARG_two_sample_pairTime_mul_lintegral (R : ℝ) (by exact_mod_cast hR) x y hxy]
  simp [pairTimeProduct, pairTimeCovariance, denom]

theorem sigmaCombination_eq_limit (ρ : Rat) (hρ : 0 ≤ ρ) :
    sigmaCombination ρ = OhtaKimura.ldSigmaLimit ρ := by
  have h : ((sigmaCombination ρ : Rat) : ℝ) = ((OhtaKimura.ldSigmaLimit ρ : Rat) : ℝ) := by
    have hρ' : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    have := Rhone.Coalescent.twoLocusValue_sigma (ρ : ℝ) hρ'
    rw [OhtaKimura.ldSigmaLimit_eq, ← this]
    simp only [sigmaCombination, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_one, Rat.cast_ofNat, chainValue_eq]
  exact_mod_cast h

end Rhone.Computation.HudsonCovariance
