/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGCommonSector
public import Rhone.Coalescent.SmcPrimeOneSectorDomination
public import Rhone.Coalescent.SmcPrimeSpatialSectors
public import Rhone.Probability.ProbabilityTotalVariation

/-!
# Total-variation bounds between the full ARG and SMC′ genealogy laws

Source: marjoram_wall2006, Methods, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcBound MarkovChain Probability MeasureTheory

theorem fewSplitARGGenealogySector_le_smcPrime (N : ℕ) (hN : 0 < N)
    (R : ℝ) (hR : 0 ≤ R) :
    fewSplitARGGenealogySector N R ≤ smcPrimeGenealogyLaw N R := by
  unfold fewSplitARGGenealogySector
  calc
    zeroSplitARGGenealogySector N R + oneSplitARGGenealogySector N R ≤
        zeroProposalGenealogySector N R + oneProposalGenealogySector N R :=
      add_le_add (le_of_eq (zeroSplitARGGenealogySector_eq N R hR))
        (oneSplitARGGenealogySector_le_oneProposal N hN R hR)
    _ ≤ smcPrimeGenealogyLaw N R := spatial_zero_one_sectors_le N R

theorem fullARG_smcPrime_tv_bound (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGGenealogyLaw N R) (smcPrimeGenealogyLaw N R) ≤
      ENNReal.ofReal (doubleBound R (N - 1)) ∧
    doubleBound R (N - 1) ≤ min 1 (R ^ 2 * quadraticCoefficient (N - 1)) := by
  have hpos : 0 < N := by omega
  constructor
  · calc
      eventTV (fullARGGenealogyLaw N R) (smcPrimeGenealogyLaw N R) ≤
          ENNReal.ofReal (1 - (fewSplitARGGenealogySector N R).real Set.univ) :=
        eventTV_le_sub_common_mass _ _ _ (fewSplitARGGenealogySector_le N hpos R)
          (fewSplitARGGenealogySector_le_smcPrime N hpos R hR)
      _ ≤ ENNReal.ofReal (doubleBound R (N - 1)) :=
        ENNReal.ofReal_le_ofReal (fewSplitARGGenealogySector_mass_defect N hpos R hR)
  · exact doubleBound_le_min R hR (N - 1)

theorem fullARG_smcPrime_tv_quadratic (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGGenealogyLaw N R) (smcPrimeGenealogyLaw N R) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (N - 1))) := by
  have h := fullARG_smcPrime_tv_bound N hN R hR
  exact h.1.trans (ENNReal.ofReal_le_ofReal h.2)

theorem fullARG_smcPrime_tv_one_sample (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGGenealogyLaw 1 R) (smcPrimeGenealogyLaw 1 R) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [Nat.sub_self, doubleBound, ENNReal.ofReal_zero] using
    (fullARG_smcPrime_tv_bound 1 (by omega) R hR).1

theorem fullARG_smcPrime_tv_zero_recombination (N : ℕ) (hN : 1 ≤ N) :
    eventTV (fullARGGenealogyLaw N 0) (smcPrimeGenealogyLaw N 0) = 0 := by
  apply le_antisymm _ zero_le
  simpa only [zero_pow (by omega : 2 ≠ 0), zero_mul, min_eq_right zero_le_one,
    ENNReal.ofReal_zero] using
    fullARG_smcPrime_tv_quadratic N hN 0 (by norm_num)

end Rhone.Coalescent.SmcPrime
