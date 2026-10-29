/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeChronologyMeas
public import Rhone.Coalescent.SmcPrimeSpatialLengthMean
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative

/-!
# Tree geometry of the full SMC′ spatial kernel

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem spatial_kernel_tree_geometry {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) :
    ∀ᵐ y ∂spatialKernel N R z, TreeNormalized y.2 ∧ TreeNonnegative y.2 ∧
      TreeChronology y.2 ∧ TreeTemporalCover y.2 := by
  have hstep : Measurable (fun u : ProposalNoise => spatialStep N R z u) :=
    (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id)
  have hgood : MeasurableSet {y : SpatialState N | TreeNormalized y.2 ∧
      TreeNonnegative y.2 ∧ TreeChronology y.2} :=
    ((TreeNormalized_measurable N).preimage measurable_snd).inter
      (((TreeNonnegative_measurable N).preimage measurable_snd).inter
        ((TreeChronology_measurable N).preimage measurable_snd))
  have ha : ∀ᵐ y ∂spatialKernel N R z, TreeNormalized y.2 ∧
      TreeNonnegative y.2 ∧ TreeChronology y.2 := by
    rw [spatialKernel_apply]
    apply (ae_map_iff hstep.aemeasurable hgood).mpr
    filter_upwards [proposalNoiseLaw_ae_marks] with u hu
    have hg := spatial_step_tree_geometry R z u hN hnorm hnonneg hchron hu
    exact ⟨hg.1, hg.2.1, hg.2.2.1⟩
  filter_upwards [ha] with y hy
  exact ⟨hy.1, hy.2.1, hy.2.2, tree_chronology_temporal_cover y.2 hN hy.2.2⟩

end Rhone.Coalescent.SmcPrime
