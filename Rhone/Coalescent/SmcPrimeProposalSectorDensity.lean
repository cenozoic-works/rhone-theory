/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeAcceptedProposalDensity
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Densities of the zero- and one-proposal sources

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem oneSplitReferenceFiber_ae_treeLength (N : ℕ) (h : KingmanHistory N) :
    ∀ᵐ s ∂oneSplitReferenceFiber N h,
      treeLength (metricTreeFromHistory N s.1) = treeLength (metricTreeFromHistory N h) := by
  rw [oneSplitReferenceFiber_source]
  apply Measure.ae_smul_measure
  apply (ae_map_iff (oneSplitReferenceSourceMap_measurable N h).aemeasurable
    (measurableSet_eq_fun ((treeLength_joint_measurable N).comp
      ((metricTreeFromHistory_measurable N).comp measurable_fst)) measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem oneProposalSkeletonFiber_density (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (hR : 0 ≤ R) :
    oneProposalSkeletonFiber N R h =
      (oneSplitReferenceFiber N h).withDensity (oneProposalDensity N R) := by
  by_cases hRp : 0 < R
  · by_cases hL : 0 < treeLength (metricTreeFromHistory N h)
    · rw [oneProposalSkeletonFiber_stop_factor N R h hRp hL,
        indexedProposal_accepted_density N R h hRp hL]
      have hf : Measurable (fun s : OneSplitSkeleton N => ENNReal.ofReal
          (R / 2 * Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h)) *
            s.2.2.2.1))) := by fun_prop
      rw [← withDensity_mul _ hf (oneSplitStopDensity_measurable N R)]
      apply withDensity_congr_ae
      filter_upwards [oneSplitReferenceFiber_ae_treeLength N h] with s hs
      simp only [Pi.mul_apply, oneSplitStopDensity, oneProposalDensity, hs,
        ← ENNReal.ofReal_mul (mul_nonneg (by linarith : 0 ≤ R / 2) (Real.exp_pos _).le),
        mul_assoc, ← Real.exp_add]
      apply congrArg ENNReal.ofReal
      apply congrArg (fun x : ℝ => R / 2 * Real.exp x)
      ring
    · have hz : treeLength (metricTreeFromHistory N h) = 0 :=
        le_antisymm (le_of_not_gt hL) (treeLength_nonneg _)
      rw [oneSplitReferenceFiber_source]
      simp only [hz, ENNReal.ofReal_zero, zero_smul, withDensity_zero_left]
      simp [oneProposalSkeletonFiber, spatialStep, hz]
  · have hz : R = 0 := le_antisymm (le_of_not_gt hRp) hR
    subst R
    rw [oneProposalDensity_zero, withDensity_zero]
    simp [oneProposalSkeletonFiber, spatialStep]
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem oneProposalSkeletonSource_density (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    oneProposalSkeletonSource N R =
      (oneSplitReferenceMeasure N).withDensity (oneProposalDensity N R) := by
  let : MeasurableSpace (KingmanHistory N × OneSplitSkeleton N) :=
    @Prod.instMeasurableSpace (KingmanHistory N) (OneSplitSkeleton N) inferInstance inferInstance
  let P := KingmanHistory N × (ProposalNoise × ProposalNoise)
  let Z (p : P) := spatialStep N R (0, metricTreeFromHistory N p.1) p.2.1
  let F (p : P) := indexedProposal N R p.1 p.2.1
  have hZ : Measurable Z := (spatialStep_measurable N R).comp
    ((measurable_const.prodMk ((metricTreeFromHistory_measurable N).comp measurable_fst)).prodMk
      measurable_snd.fst)
  have hF : Measurable F := (indexedProposal_measurable N R).comp
    (measurable_fst.prodMk measurable_snd.fst)
  have hg : Measurable (fun p : P => spatialStep N R (Z p) p.2.2) :=
    (spatialStep_measurable N R).comp (hZ.prodMk measurable_snd.snd)
  have hevent : MeasurableSet {p : P | (Z p).1 < 1 ∧
      (spatialStep N R (Z p) p.2.2).1 = 1} :=
    (measurableSet_lt hZ.fst measurable_const).inter
      (measurableSet_eq_fun hg.fst measurable_const)
  have href : oneSplitReferenceMeasure N = oneSplitReferenceKernel N ∘ₘ kingmanHistoryLaw N := by
    unfold oneSplitReferenceMeasure
    congr 1
    funext h
    exact (oneSplitReferenceKernel_apply N h).symm
  rw [href, Measure.withDensity_comp (oneProposalDensity_measurable N R)]
  ext s hs
  unfold oneProposalSkeletonSource
  change (((kingmanHistoryLaw N).prod (proposalNoiseLaw.prod proposalNoiseLaw)).restrict
    {p | (Z p).1 < 1 ∧ (spatialStep N R (Z p) p.2.2).1 = 1}).map F s = _
  rw [Measure.map_apply hF hs, Measure.restrict_apply (hs.preimage hF),
    Measure.prod_apply ((hs.preimage hF).inter hevent),
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro h
  rw [Kernel.withDensity_apply (oneSplitReferenceKernel N)
    (show Measurable (Function.uncurry (fun (_ : KingmanHistory N) (s : OneSplitSkeleton N) =>
      oneProposalDensity N R s)) from
        (oneProposalDensity_measurable N R).comp measurable_snd),
    oneSplitReferenceKernel_apply, ← oneProposalSkeletonFiber_density N R h hR]
  unfold oneProposalSkeletonFiber
  have hFp : Measurable (fun p : ProposalNoise × ProposalNoise =>
      indexedProposal N R h p.1) :=
    (indexedProposal_measurable N R).comp
      (measurable_const.prodMk measurable_fst)
  rw [Measure.map_apply hFp hs, Measure.restrict_apply (hs.preimage hFp)]
  rfl
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

noncomputable def zeroProposalHistorySource (N : ℕ) (R : ℝ) :
    Measure (KingmanHistory N) :=
  (((kingmanHistoryLaw N).prod proposalNoiseLaw).restrict
    {p | (spatialStep N R (0, metricTreeFromHistory N p.1) p.2).1 = 1}).map Prod.fst

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–2. -/
theorem zeroProposalHistorySource_density (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    zeroProposalHistorySource N R = (kingmanHistoryLaw N).withDensity
      (fun h => ENNReal.ofReal
        (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h))))) := by
  let g (p : KingmanHistory N × ProposalNoise) :=
    spatialStep N R (0, metricTreeFromHistory N p.1) p.2
  have hg : Measurable g := (spatialStep_measurable N R).comp
    ((measurable_const.prodMk ((metricTreeFromHistory_measurable N).comp measurable_fst)).prodMk
      measurable_snd)
  have hstop : MeasurableSet {p : KingmanHistory N × ProposalNoise | (g p).1 = 1} :=
    measurableSet_eq_fun hg.fst measurable_const
  let f (h : KingmanHistory N) := ENNReal.ofReal
    (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h))))
  have hf : Measurable f := (Real.measurable_exp.comp
    (measurable_const.mul ((treeLength_joint_measurable N).comp
      (metricTreeFromHistory_measurable N))).neg).ennreal_ofReal
  ext s hs
  unfold zeroProposalHistorySource
  rw [Measure.map_apply measurable_fst hs, Measure.restrict_apply (hs.preimage measurable_fst),
    Measure.prod_apply ((hs.preimage measurable_fst).inter hstop), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  change (∫⁻ h, proposalNoiseLaw {u | h ∈ s ∧ (g (h, u)).1 = 1} ∂kingmanHistoryLaw N) =
    ∫⁻ h, s.indicator f h ∂kingmanHistoryLaw N
  apply lintegral_congr
  intro h
  by_cases hm : h ∈ s
  · simp only [hm, true_and, Set.indicator_of_mem hm]
    have he := spatial_kernel_stop_mass R hR (0, metricTreeFromHistory N h) (by norm_num)
    rw [spatialKernel_apply, Measure.map_apply
      (show Measurable (fun u : ProposalNoise =>
        spatialStep N R (0, metricTreeFromHistory N h) u) from
        (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id))
      (show MeasurableSet {y : SpatialState N | y.1 = 1} from
        measurableSet_eq_fun measurable_fst measurable_const)] at he
    simpa only [Set.preimage_ofPred_eq, g, f, sub_zero, mul_one] using he
  · simp [hm]
end Rhone.Coalescent.SmcPrime
