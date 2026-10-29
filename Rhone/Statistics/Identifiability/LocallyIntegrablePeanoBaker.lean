/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PeanoBaker
public import Rhone.Statistics.Identifiability.IntegratedNormPower
public import Rhone.Statistics.Identifiability.VectorPrimitiveAC
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! # Peano–Baker series for locally integrable coefficients: norm bounds and continuity -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Nat
namespace Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem intervalIntegrable_of_locallyIntegrable {F : Type*} [NormedAddCommGroup F]
    {f : ℝ → F} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

omit [CompleteSpace E] in
theorem locallyIntegrable_apply {A : ℝ → E →L[ℝ] E} {X : ℝ → E}
    (hA : LocallyIntegrable A volume) (hX : Continuous X) :
    LocallyIntegrable (fun t => A t (X t)) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hX.continuousOn
  have hm : AEStronglyMeasurable (fun t => A t (X t)) volume :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂
      hA.aestronglyMeasurable hX.aestronglyMeasurable
  apply Integrable.mono' ((hA.integrableOn_isCompact hK).norm.mul_const C) hm.restrict
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _))

omit [CompleteSpace E] in
theorem continuous_primitive {f : ℝ → E} (hf : LocallyIntegrable f volume) (a : ℝ) :
    Continuous (fun t => ∫ s in a..t, f s) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_of_locallyIntegrable hf) a

omit [CompleteSpace E] in
theorem term_continuous {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (n : ℕ) :
    Continuous (PeanoBaker.term A x n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_primitive (locallyIntegrable_apply hA ih) 0

omit [CompleteSpace E] in
theorem term_integrable {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (n : ℕ) :
    LocallyIntegrable (fun t => A t (PeanoBaker.term A x n t)) volume :=
  locallyIntegrable_apply hA (term_continuous hA x n)

theorem term_succ_ae_hasDerivAt {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (n : ℕ) :
    ∀ᵐ t, HasDerivAt (PeanoBaker.term A x (n+1)) (A t (PeanoBaker.term A x n t)) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (term_integrable hA x n)] with t
    ht
  exact ht 0

noncomputable def accumulatedNorm (A : ℝ → E →L[ℝ] E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖A s‖

omit [CompleteSpace E] in
theorem norm_locallyIntegrable {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) : LocallyIntegrable (fun t => ‖A t‖) volume :=
  fun t => (hA t).norm

omit [CompleteSpace E] in
theorem accumulatedNorm_nonneg (A : ℝ → E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ accumulatedNorm A t :=
  intervalIntegral.integral_nonneg ht fun _ _ => norm_nonneg _

omit [CompleteSpace E] in
theorem accumulatedNorm_mono {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    accumulatedNorm A s ≤ accumulatedNorm A t := by
  apply intervalIntegral.integral_mono_interval (f := fun u => ‖A u‖) (a := 0) (b := s)
    (c := 0) (d := t) le_rfl hs hst
  · exact Filter.Eventually.of_forall fun t => norm_nonneg (A t)
  · exact intervalIntegrable_of_locallyIntegrable (norm_locallyIntegrable hA) _ _

omit [CompleteSpace E] in
theorem norm_term_le_of_nonneg {A : ℝ → E →L[ℝ] E}
    (hA : LocallyIntegrable A volume) (x : E) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖PeanoBaker.term A x n t‖ ≤ accumulatedNorm A t ^ n / (n.factorial : ℝ) * ‖x‖ := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hg := norm_locallyIntegrable hA
    have hi := intervalIntegrable_of_locallyIntegrable hg 0 t
    have hc : Continuous (fun s => accumulatedNorm A s ^ n) :=
      (continuous_primitive hg 0).pow n
    have hib : IntervalIntegrable (fun s => ‖A s‖ * (accumulatedNorm A s ^ n /
        (n.factorial : ℝ) * ‖x‖)) volume 0 t :=
      hi.mul_continuousOn ((hc.div_const _).mul continuous_const).continuousOn
    calc
      ‖PeanoBaker.term A x (n+1) t‖ ≤
          ∫ s in (0 : ℝ)..t, ‖A s‖ * (accumulatedNorm A s ^ n / (n.factorial : ℝ) * ‖x‖) := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht _ hib
        filter_upwards with s hs
        exact ((A s).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (ih hs.1.le) (norm_nonneg _))
      _ = accumulatedNorm A t ^ (n+1) / ((n+1).factorial : ℝ) * ‖x‖ := by
        have heq : (fun s => ‖A s‖ * (accumulatedNorm A s ^ n / (n.factorial : ℝ) * ‖x‖)) =
            (fun s => (‖A s‖ * accumulatedNorm A s ^ n) * ((n.factorial : ℝ)⁻¹ * ‖x‖)) := by
          funext s; ring
        rw [heq, intervalIntegral.integral_mul_const]
        simp only [accumulatedNorm]
        rw [IntegratedNormPower.integral_mul_cumulative_pow hg 0 t n]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

end Rhone.Statistics.Identifiability.LocallyIntegrablePeanoBaker
