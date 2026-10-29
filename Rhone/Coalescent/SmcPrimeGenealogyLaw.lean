/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialProcess
public import Rhone.Coalescent.SmcPrimeKingmanTreeLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Observed genealogies of the full sequential SMC′ process -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess
open scoped ENNReal

noncomputable def treePairMRCA {N : ℕ} (T : Tree N) (i j : Fin N) : ℝ≥0∞ :=
  if i = j then 0 else
  ENNReal.ofReal (rootHeight T) ⊓ ⨅ b : Fin T.1,
    if i ∈ (T.2 b).1 ∧ j ∈ (T.2 b).1 ∧ 0 < branchLength (T.2 b)
    then ENNReal.ofReal (T.2 b).2.1 else ⊤

noncomputable def spatialGenealogyObservation (N : ℕ)
    (ω : ℕ → SpatialState N) : Genealogy N :=
  fun q i j => ⨅ k : ℕ,
    if (ω k).1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k + 1)).1
    then treePairMRCA (ω k).2 i j else ⊤

noncomputable def spatialInitialLaw (N : ℕ) : Measure (SpatialState N) :=
  (kingmanTreeLaw N).map (fun T => (0, T))

instance spatialInitialLaw_probability (N : ℕ) : IsProbabilityMeasure (spatialInitialLaw N) := by
  unfold spatialInitialLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_const.prodMk measurable_id).aemeasurable).mpr inferInstance

instance spatialProcess_law_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure ((spatialProcess N R).law (spatialInitialLaw N)) := by
  unfold Rhone.MarkovChain.DiscreteProcess.law
  apply MeasureTheory.isProbabilityMeasure_bind (ProbabilityTheory.Kernel.measurable _).aemeasurable
  exact Filter.Eventually.of_forall (fun _ => inferInstance)

theorem treePairMRCA_measurable (N : ℕ) (i j : Fin N) :
    Measurable (fun T : Tree N => treePairMRCA T i j) := by
  classical
  apply measurable_sigma_of_fibers
  intro m
  change Measurable (fun f : Fin m → Branch N => treePairMRCA ⟨m, f⟩ i j)
  by_cases hij : i = j
  · simpa only [treePairMRCA, hij, ite_eq_left] using
      (measurable_const : Measurable (fun _ : Fin m → Branch N => (0 : ℝ≥0∞)))
  · simp only [treePairMRCA, hij]
    apply (ENNReal.measurable_ofReal.comp (rootHeightFiber_measurable N m)).inf
    apply Measurable.iInf
    intro b
    have hb : Measurable (fun f : Fin m → Branch N => f b) := measurable_pi_apply b
    have hm : MeasurableSet {f : Fin m → Branch N |
        i ∈ (f b).1 ∧ j ∈ (f b).1 ∧ 0 < branchLength (f b)} := by
      have hi : MeasurableSet {c : Finset (Fin N) | i ∈ c} := Set.to_countable _ |>.measurableSet
      have hj : MeasurableSet {c : Finset (Fin N) | j ∈ c} := Set.to_countable _ |>.measurableSet
      exact (hi.preimage hb.fst).inter ((hj.preimage hb.fst).inter
        (measurableSet_lt measurable_const ((branchLength_measurable N).comp hb)))
    exact (ENNReal.measurable_ofReal.comp hb.snd.fst).piecewise hm measurable_const

theorem spatialGenealogyObservation_measurable (N : ℕ) :
    Measurable (spatialGenealogyObservation N) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.iInf
  intro k
  have hk : Measurable (fun ω : ℕ → SpatialState N => ω k) := measurable_pi_apply k
  have hnext : Measurable (fun ω : ℕ → SpatialState N => ω (k + 1)) :=
    measurable_pi_apply (k + 1)
  have hq : Measurable (fun _ : ℕ → SpatialState N => (q.val : ℝ)) := measurable_const
  have hinterval : MeasurableSet {ω : ℕ → SpatialState N |
      (ω k).1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k + 1)).1} := by
    convert (measurableSet_le hk.fst hq).inter (measurableSet_lt hq hnext.fst) using 1
    ext ω
    rfl
  exact ((treePairMRCA_measurable N i j).comp hk.snd).piecewise
    hinterval measurable_const

end Rhone.Coalescent.SmcPrime
namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory SmcPrime

noncomputable def smcPrimeGenealogyLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((spatialProcess N R).law (spatialInitialLaw N)).map (spatialGenealogyObservation N)

instance smcPrimeGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (smcPrimeGenealogyLaw N R) := by
  unfold smcPrimeGenealogyLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (spatialGenealogyObservation_measurable N).aemeasurable).mpr inferInstance

end Rhone.Coalescent.IntervalProcess
