/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusArgSampler
public import Rhone.Probability.ExpNegMomentUnique

/-!
# The two MRCA times of the general ancestral recombination graph and the labelled chain

Source: griffiths1991_two_locus_graph, pp. 103, 106–108. -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy IntervalProcess
  MarkovChain.IntervalProcess Analysis.ExpNegMoment Probability.ExpNegMoment
open scoped ENNReal

theorem measurable_timeBefore {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (Rc : RateChain S) (A : Finset S) :
    Measurable (Rc.timeBefore A) := by
  unfold RateChain.timeBefore RateChain.costBefore RateChain.holdTime
  refine Measurable.tsum fun k => ?_
  have h1 : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  have h2 : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.2 k :=
    (measurable_pi_apply k).comp measurable_snd
  refine Measurable.ite (h1 (MeasurableSet.of_discrete (s := (A : Set S)))) measurable_const ?_
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul
    (h2.div ((Measurable.of_discrete (f := Rc.rate)).comp h1)))

open MeasureTheory Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy Coalescent.IntervalProcess
    MarkovChain.IntervalProcess in
open scoped ENNReal in
theorem fullARG_mrcaTimes_law_eq_argRateChain (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (qx qy : GenomicProbe) (hxy : qx < qy) :
    (fullARGGenealogyLaw N R).map
        (fun g => ((⨆ i, ⨆ j, g qx i j : ℝ≥0∞), (⨆ i, ⨆ j, g qy i j : ℝ≥0∞))) =
      ((argRateChain (n := N) 0 0 (R * (((qy : ℚ) : ℝ) - ((qx : ℚ) : ℝ)))
          le_rfl le_rfl (mul_nonneg hR (sub_nonneg.mpr (Rat.cast_le.mpr hxy.le)))).jumpHoldLaw
          (Finset.univ.image fun i : Fin N => (({i} : Finset (Fin N)), ({i} : Finset (Fin N))))).map
        (fun p =>
          ((argRateChain (n := N) 0 0 (R * (((qy : ℚ) : ℝ) - ((qx : ℚ) : ℝ)))
              le_rfl le_rfl (mul_nonneg hR (sub_nonneg.mpr (Rat.cast_le.mpr hxy.le)))).timeBefore
              (Finset.univ.filter fun L : ASt N => (carA (n := N) L).card ≤ 1) p,
            (argRateChain (n := N) 0 0 (R * (((qy : ℚ) : ℝ) - ((qx : ℚ) : ℝ)))
              le_rfl le_rfl (mul_nonneg hR (sub_nonneg.mpr (Rat.cast_le.mpr hxy.le)))).timeBefore
              (Finset.univ.filter fun L : ASt N => (carB (n := N) L).card ≤ 1) p)) := by
  have hρ : 0 ≤ R * (((qy : ℚ) : ℝ) - ((qx : ℚ) : ℝ)) :=
    mul_nonneg hR (sub_nonneg.mpr (Rat.cast_le.mpr hxy.le))
  apply eq_of_lintegral_expNeg_pow_eq
  intro m n
  have hF : Measurable fun p : ℝ≥0∞ × ℝ≥0∞ => expNeg p.1 ^ m * expNeg p.2 ^ n :=
    ((measurable_expNeg.comp measurable_fst).pow_const m).mul
      ((measurable_expNeg.comp measurable_snd).pow_const n)
  have hM : Measurable fun g : Genealogy N =>
      ((⨆ i, ⨆ j, g qx i j : ℝ≥0∞), (⨆ i, ⨆ j, g qy i j : ℝ≥0∞)) :=
    (Measurable.iSup fun i => Measurable.iSup fun j =>
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply qx))).prodMk
      (Measurable.iSup fun i => Measurable.iSup fun j =>
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply qy)))
  set C := argRateChain (n := N) 0 0 (R * (((qy : ℚ) : ℝ) - ((qx : ℚ) : ℝ))) le_rfl le_rfl hρ
    with hC
  have hT : Measurable fun p : (ℕ → ASt N) × (ℕ → ℝ) =>
      (C.timeBefore (IntervalCounts.lowA N) p, C.timeBefore (IntervalCounts.lowB N) p) :=
    (measurable_timeBefore C _).prodMk (measurable_timeBefore C _)
  rw [lintegral_map hF hM, fullARGGenealogyLaw]
  refine (lintegral_map (hF.comp hM) (genealogyObservation_measurable N)).trans
    (Eq.trans ?_ (lintegral_map hF hT).symm)
  exact (IntervalCounts.lintegral_expNeg_mrca R hR qx qy hxy hρ N m n).trans
    (IntervalCounts.lintegral_expNeg_timeBefore_startState _ hρ m n).symm

end Rhone.Coalescent
