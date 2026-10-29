/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialGeometry
public import Rhone.Coalescent.SmcPrimeProposalLengthMean

/-!
# Full spatial kernel length drift, including stopped and rejected proposals

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory ProbabilityTheory

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem spatialKernel_apply (N : ℕ) (R : ℝ) (z : SpatialState N) :
    spatialKernel N R z = proposalNoiseLaw.map (fun u => spatialStep N R z u) := by
  rw [spatialKernel, Kernel.map_apply _ (spatialStep_measurable N R),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (spatialStep_measurable N R) measurable_prodMk_left]
  rfl

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem spatial_step_mean_length_le {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) :
    (∫⁻ u, ENNReal.ofReal (treeLength (spatialStep N R z u).2) ∂proposalNoiseLaw) ≤
      ENNReal.ofReal (treeLength z.2 + 2) := by
  have hnoiseMean : (∫⁻ u, ENNReal.ofReal (-Real.log (u 3)) ∂proposalNoiseLaw) = 1 := by
    have heval := (measurePreserving_eval (fun _ : Fin 5 => unitUniform) (3 : Fin 5)).map_eq
    rw [← inverse_log_budget_mean, ← heval, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (treeLength z.2) + 2 * ENNReal.ofReal (-Real.log (u 3))
        ∂proposalNoiseLaw := by
      apply lintegral_mono_ae
      filter_upwards [proposalNoiseLaw_ae_marks] with u hu
      have hgeom := spatial_step_tree_geometry R z u hN hnorm hnonneg hchron hu
      have he : 0 ≤ -Real.log (u 3) :=
        neg_nonneg.mpr (Real.log_nonpos (hu 3).1.le (hu 3).2.le)
      have hb := ENNReal.ofReal_le_ofReal hgeom.2.2.2.2
      simpa only [ENNReal.ofReal_add (treeLength_nonneg z.2)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hb
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ (by fun_prop),
        hnoiseMean, lintegral_const]
      simp [ENNReal.ofReal_add (treeLength_nonneg z.2) (by norm_num : (0 : ℝ) ≤ 2)]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem spatial_kernel_mean_length_le {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) :
    (∫⁻ y, ENNReal.ofReal (treeLength y.2) ∂spatialKernel N R z) ≤
      ENNReal.ofReal (treeLength z.2 + 2) := by
  have hlen : Measurable (fun T : Tree N => treeLength T) := by
    apply measurable_sigma_of_fibers
    intro m
    exact treeLengthFiber_measurable N m
  have hstep : Measurable (fun u : ProposalNoise => spatialStep N R z u) :=
    (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun y : SpatialState N => ENNReal.ofReal (treeLength y.2)) :=
    ENNReal.measurable_ofReal.comp (hlen.comp measurable_snd)
  rw [spatialKernel_apply, lintegral_map hf hstep]
  exact spatial_step_mean_length_le R z hN hnorm hnonneg hchron

end Rhone.Coalescent.SmcPrime
