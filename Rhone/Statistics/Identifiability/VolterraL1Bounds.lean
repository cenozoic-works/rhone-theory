/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
public import Rhone.Statistics.Identifiability.VolterraReflection

/-! # Compact `L¹` bounds for Volterra series terms -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Nat
namespace Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_term_le_compact_mass {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) {T : ℝ} (hT : 0 ≤ T)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖PeanoBaker.term A x n t‖ ≤
      (∫ s in (-T)..T, ‖A s‖)^n / (n.factorial : ℝ) * ‖x‖ := by
  have hi := intervalIntegrable_of_locallyIntegrable (norm_locallyIntegrable hA) (-T) T
  by_cases ht0 : 0 ≤ t
  · refine (norm_term_le_of_nonneg hA x n ht0).trans ?_
    have hm : accumulatedNorm A t ≤ ∫ s in (-T)..T, ‖A s‖ := by
      exact intervalIntegral.integral_mono_interval (by linarith) ht0 ht.2
        (Filter.Eventually.of_forall fun s => norm_nonneg (A s)) hi
    gcongr
    exact accumulatedNorm_nonneg A ht0
  · have htn : 0 ≤ -t := by linarith
    have hb := PeanoBaker.locallyIntegrable_reflection A hA
    have hbnd := norm_term_le_of_nonneg hb x n htn
    rw [PeanoBaker.term_reflection, neg_neg] at hbnd
    refine hbnd.trans ?_
    have hm : accumulatedNorm (fun s => -A (-s)) (-t) ≤ ∫ s in (-T)..T, ‖A s‖ := by
      simp only [accumulatedNorm, norm_neg]
      rw [intervalIntegral.integral_comp_neg (fun s => ‖A s‖), neg_neg, neg_zero]
      exact intervalIntegral.integral_mono_interval ht.1 (by linarith) hT
        (Filter.Eventually.of_forall fun s => norm_nonneg (A s)) hi
    gcongr
    exact accumulatedNorm_nonneg (fun s => -A (-s)) htn

theorem exists_summable_compact_bound {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (a b : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n t, t ∈ uIcc a b → ‖PeanoBaker.term A x n t‖ ≤ u n := by
  let T : ℝ := |a| + |b|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let K : ℝ := ∫ s in (-T)..T, ‖A s‖
  refine ⟨fun n => K^n / (n.factorial : ℝ) * ‖x‖,
    (Real.summable_pow_div_factorial K).mul_right ‖x‖, ?_⟩
  intro n t ht
  apply norm_term_le_compact_mass hA x hT n
  apply uIcc_subset_Icc _ _ ht
  · constructor <;> dsimp [T] <;> linarith [neg_abs_le a, le_abs_self a, abs_nonneg b]
  · constructor <;> dsimp [T] <;> linarith [neg_abs_le b, le_abs_self b, abs_nonneg a]

variable [CompleteSpace E]

theorem term_summable {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (t : ℝ) :
    Summable (fun n => PeanoBaker.term A x n t) := by
  obtain ⟨u, hu, hub⟩ := exists_summable_compact_bound hA x t t
  exact hu.of_norm_bounded fun n => hub n t (by simp)

end Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
