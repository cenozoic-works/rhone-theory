/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ACComparisonBounds
public import Rhone.Statistics.Identifiability.IntegrableClockCalculus
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Nonnegative AC survival bounds total exit mass without a proper-tail hypothesis -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

theorem ac_flux_lintegral_le_initial {F g : ℝ → ℝ} {a : ℝ}
    (hac : ∀ b, a ≤ b → AbsolutelyContinuousOnInterval F a b)
    (hF : ∀ t, a ≤ t → 0 ≤ F t)
    (hd : ∀ᵐ t, a ≤ t → HasDerivAt F (-g t) t)
    (hg : ∀ᵐ t, a ≤ t → 0 ≤ g t)
    (hm : AEMeasurable g (volume.restrict (Ioi a))) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (g t)) ≤ ENNReal.ofReal (F a) := by
  have hanti : Antitone (fun t => F (max t a)) := by
    intro s t hst
    have hab : max s a ≤ max t a := max_le_max hst le_rfl
    have hsub : uIcc (max s a) (max t a) ⊆ uIcc a (max t a) := by
      rw [uIcc_of_le hab, uIcc_of_le (le_max_right t a)]
      exact Icc_subset_Icc (le_max_right s a) le_rfl
    apply ac_endpoint_le_of_ae_hasDerivAt_nonpos hab
      ((hac (max t a) (le_max_right t a)).mono hsub)
    · filter_upwards [hd] with u hu hmem
      exact hu ((le_max_right s a).trans (uIcc_of_le hab ▸ hmem).1)
    · filter_upwards [hg] with u hu hmem
      exact neg_nonpos.mpr (hu ((le_max_right s a).trans (uIcc_of_le hab ▸ hmem).1))
  have hbound : BddBelow (range (fun t => F (max t a))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hF _ (le_max_right t a)
  let L := ⨅ t, F (max t a)
  have hL : 0 ≤ L := le_ciInf fun t => hF _ (le_max_right t a)
  have htail : Tendsto F atTop (𝓝 L) := by
    apply (tendsto_atTop_ciInf hanti hbound).congr'
    filter_upwards [eventually_ge_atTop a] with t ht
    rw [max_eq_left ht]
  rw [ac_flux_lintegral_Ioi hac hd hg hm htail]
  exact ENNReal.ofReal_le_ofReal (sub_le_self _ hL)

end Rhone.Statistics.Identifiability
