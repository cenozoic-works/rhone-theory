/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeProposalKernel

/-! # Full spatial sampler implementing the SMC′ proposals -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

abbrev SpatialState (N : ℕ) := ℝ × Tree N

noncomputable def spatialStep (N : ℕ) (R : ℝ)
    (z : SpatialState N) (u : ProposalNoise) : SpatialState N :=
  if 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0 then (1, z.2)
  else let p := proposal R z.2 u
       if z.1 + p.1 < 1 then (z.1 + p.1, p.2.2) else (1, z.2)

theorem spatialStep_measurable (N : ℕ) (R : ℝ) :
    Measurable (fun p : SpatialState N × ProposalNoise => spatialStep N R p.1 p.2) := by
  have hx : Measurable (fun p : SpatialState N × ProposalNoise => p.1.1) :=
    measurable_fst.fst
  have ht : Measurable (fun p : SpatialState N × ProposalNoise => p.1.2) :=
    measurable_fst.snd
  have hp := (proposal_measurable N R).comp (ht.prodMk measurable_snd)
  have hd := hx.add hp.fst
  have hlen : Measurable (fun T : Tree N => treeLength T) := by
    apply measurable_sigma_of_fibers
    intro m
    exact treeLengthFiber_measurable N m
  have hz : MeasurableSet {p : SpatialState N × ProposalNoise |
      1 ≤ p.1.1 ∨ R ≤ 0 ∨ treeLength p.1.2 ≤ 0} :=
    by
      by_cases hR : R ≤ 0
      · simp only [hR, true_or, or_true]
        exact MeasurableSet.univ
      · have hone : Measurable (fun _ : SpatialState N × ProposalNoise => (1 : ℝ)) :=
          measurable_const
        have hzero : Measurable (fun _ : SpatialState N × ProposalNoise => (0 : ℝ)) :=
          measurable_const
        convert (measurableSet_le hone hx).union
          (measurableSet_le (hlen.comp ht) hzero) using 1
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_union, Function.comp_def, hR, false_or]
  exact (measurable_const.prodMk ht).piecewise hz
    ((hd.prodMk hp.snd.snd).piecewise (measurableSet_lt hd measurable_const)
      (measurable_const.prodMk ht))

noncomputable def spatialKernel (N : ℕ) (R : ℝ) :
    Kernel (SpatialState N) (SpatialState N) :=
  (Kernel.id.prod (Kernel.const (SpatialState N) proposalNoiseLaw)).map
    (fun p => spatialStep N R p.1 p.2)

instance spatialKernel_markov (N : ℕ) (R : ℝ) :
    IsMarkovKernel (spatialKernel N R) := by
  unfold spatialKernel
  exact Kernel.IsMarkovKernel.map _ (spatialStep_measurable N R)

noncomputable def spatialProcess (N : ℕ) (R : ℝ) :
    Rhone.MarkovChain.DiscreteProcess (SpatialState N) := ⟨spatialKernel N R⟩

end Rhone.Coalescent.SmcPrime
