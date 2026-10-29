/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeProposalGeometry
public import Rhone.Coalescent.SmcPrimeProposalKernel

/-!
# Expected length drift of the SMC′ proposal

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem proposalNoiseLaw_ae_marks :
    ∀ᵐ u ∂proposalNoiseLaw, ∀ i : Fin 5, 0 < u i ∧ u i < 1 := by
  have hu : ∀ᵐ v ∂unitUniform, v ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin 5 => unitUniform) i).quasiMeasurePreserving.ae hu

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem proposal_mean_length_le {N : ℕ} (R : ℝ) (T : Tree N)
    (hN : 0 < N) (hL : 0 < treeLength T)
    (hnorm : TreeNormalized T) (hnonneg : TreeNonnegative T) (hchron : TreeChronology T) :
    (∫⁻ u, ENNReal.ofReal (treeLength (proposal R T u).2.2) ∂proposalNoiseLaw) ≤
      ENNReal.ofReal (treeLength T + 2) := by
  have hnoiseMean : (∫⁻ u, ENNReal.ofReal (-Real.log (u 3)) ∂proposalNoiseLaw) = 1 := by
    have heval := (measurePreserving_eval (fun _ : Fin 5 => unitUniform) (3 : Fin 5)).map_eq
    rw [← inverse_log_budget_mean, ← heval, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (treeLength T) + 2 * ENNReal.ofReal (-Real.log (u 3))
        ∂proposalNoiseLaw := by
      apply lintegral_mono_ae
      filter_upwards [proposalNoiseLaw_ae_marks] with u hu
      have hgeom := proposal_geometry R T u hN hL hnorm hnonneg hchron
        ⟨(hu 1).1.le, (hu 1).2⟩ ⟨(hu 2).1.le, (hu 2).2⟩ (hu 3)
        ⟨(hu 4).1.le, (hu 4).2⟩
      have he : 0 ≤ -Real.log (u 3) :=
        neg_nonneg.mpr (Real.log_nonpos (hu 3).1.le (hu 3).2.le)
      have hb := ENNReal.ofReal_le_ofReal hgeom.2.2.2
      simpa only [ENNReal.ofReal_add (treeLength_nonneg T)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat] using hb
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ (by fun_prop),
        hnoiseMean, lintegral_const]
      simp [ENNReal.ofReal_add (treeLength_nonneg T) (by norm_num : (0 : ℝ) ≤ 2)]

end Rhone.Coalescent.SmcPrime
