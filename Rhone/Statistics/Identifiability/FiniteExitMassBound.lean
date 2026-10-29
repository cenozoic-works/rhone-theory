/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.WeightedFirstExit
public import Rhone.Statistics.Identifiability.FlowJetNormBound
public import Rhone.Statistics.Identifiability.ACFluxMassBound

/-! # Finite-state exit subprobability bounds without proper conditional tails -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability

lemma finite_exit_shifted_mass_bound {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin n) (s : ℝ) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (flowOutput Q i (exitRate Q) 0 (t - s))) ≤ 1 := by
  have hd (t : ℝ) : HasDerivAt (fun u => flowOutput Q i (fun _ => 1) 0 (u-s))
      (-flowOutput Q i (exitRate Q) 0 (t - s)) t := by
    convert! (survival_hasDerivAt_exit Q i (t - s)).comp t
      ((hasDerivAt_id t).sub_const s) using 1
    simp
  have hac : ContDiff ℝ 1 (fun t => flowOutput Q i (fun _ => 1) 0 (t - s)) :=
    (flowOutput_contDiff_nat Q i (fun _ => 1) 0 1).comp (contDiff_id.sub contDiff_const)
  have hm : Continuous (fun t => flowOutput Q i (exitRate Q) 0 (t - s)) :=
    (flowOutput_continuous Q i (exitRate Q) 0).comp (continuous_id.sub continuous_const)
  have he := ac_flux_lintegral_le_initial
    (fun _ _ => hac.contDiffOn.absolutelyContinuousOnInterval)
    (fun t ht => survival_nonneg Q hQ i (sub_nonneg.mpr ht))
    (ae_of_all _ (fun t _ => hd t))
    (ae_of_all _ (fun t ht => firstExit_density_nonneg Q hQ hrow i (sub_nonneg.mpr ht)))
    hm.measurable.aemeasurable.restrict
  simpa using he

namespace WeightedExit
lemma survival_contDiff {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) :
    ContDiff ℝ 1 (survival Q α) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (flowOutput_contDiff_nat Q i (fun _ => 1) 0 1)

lemma law_mass_le_one {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) : law Q α univ ≤ 1 := by
  have hs : ∀ t, 0 ≤ t → 0 ≤ survival Q α t := by
    intro t ht
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (survival_nonneg Q hQ i ht)
  have he := ac_flux_lintegral_le_initial
    (fun _ _ => (survival_contDiff Q α).contDiffOn.absolutelyContinuousOnInterval) hs
    (ae_of_all _ (fun t _ => survival_derivative Q α t))
    (ae_of_all _ (fun t ht => density_nonnegative Q α hQ hrow hα ht))
    (density_continuous Q α).measurable.aemeasurable.restrict
  simpa [law, survival, hαsum, withDensity_apply _ MeasurableSet.univ] using he

end WeightedExit
end Rhone.Statistics.Identifiability
