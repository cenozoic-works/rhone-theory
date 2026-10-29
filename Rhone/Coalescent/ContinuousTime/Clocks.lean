/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTime.Interpolation

/-! # Positivity and the exact exponential holding law of the continuous-time path -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTime

open MeasureTheory ProbabilityTheory TypedAncestralChain BranchLengthMoments ContinuousTimeGenealogy
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem ae_path_closed (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {s : TS n KA KB} (hs : C s) :
    ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s), ∀ k : ℕ, C (ω k) := by
  classical
  rw [ae_all_iff]
  intro k
  let g : TS n KA KB → ℝ := fun t => if C t then 0 else 1
  have hg : ∀ t, 0 ≤ g t := by intro t; simp only [g]; split_ifs <;> norm_num
  have hzero : (∫⁻ ω, ENNReal.ofReal (g (ω k)) ∂(argTrajT θA θB ρ πA πB h s)) = 0 := by
    rw [lintegral_argTrajT h k hg s,
      mstep_congr_closed hC (g₂ := fun _ => 0) (by intros; simp_all [g]) k hs,
      mstep_const h k 0 s, ENNReal.ofReal_zero]
  have hmeas : Measurable (fun ω : ℕ → TS n KA KB => ENNReal.ofReal (g (ω k))) :=
    (Measurable.of_discrete (f := fun t : TS n KA KB => ENNReal.ofReal (g t))).comp
      (measurable_pi_apply k)
  have hz := (lintegral_eq_zero_iff hmeas).mp hzero
  filter_upwards [hz] with ω hω
  by_contra hc
  simp [g, hc] at hω

theorem ae_pos_expOne : ∀ᵐ x ∂expOne, 0 < x := by
  have hn : ∀ᵐ x ∂expOne, 0 ≤ x := ae_nonneg_expMeasure one_pos
  have : NullSingletonClass expOne := by
    rw [expOne, expMeasure_eq_withDensity]
    infer_instance
  filter_upwards [hn, expOne.ae_ne 0] with x hx hne
  exact lt_of_le_of_ne hx (Ne.symm hne)

theorem ae_pos_clocks : ∀ᵐ e ∂clocks, ∀ k : ℕ, 0 < e k := by
  rw [ae_all_iff]
  intro k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => expOne) k).quasiMeasurePreserving.ae
    ae_pos_expOne

theorem ae_pos_path_clocks (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    ∀ᵐ z ∂(ctLaw θA θB ρ πA πB h s), ∀ k : ℕ, 0 < z.2 k :=
  (Measure.quasiMeasurePreserving_snd
    (μ := argTrajT θA θB ρ πA πB h s) (ν := clocks)).ae ae_pos_clocks

theorem ae_holding_eq_holdTime (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    ∀ᵐ z ∂(ctLaw θA θB ρ πA πB h s), ∀ k : ℕ,
      holding θA θB ρ z k = holdTime θA θB ρ z k := by
  filter_upwards [ae_pos_path_clocks h s] with z hz k
  apply max_eq_right
  exact div_nonneg (le_of_lt (hz k)) (rateTotS_nonneg h.thA h.thB h.rho _)

theorem ae_holding_pos_before_absorption (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB}
        (hw : Rhone.Coalescent.TwoLocusGenealogy.WF s.st.1) :
    ∀ᵐ z ∂(ctLaw θA θB ρ πA πB h s), ∀ k : ℕ, k < absTime z.1 →
      0 < holding θA θB ρ z k := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := argTrajT θA θB ρ πA πB h s) (ν := clocks)).ae
    (ae_lt_absTime_iff h hθA hθB hw)
  have hwp := (Measure.quasiMeasurePreserving_fst
    (μ := argTrajT θA θB ρ πA πB h s) (ν := clocks)).ae
    (ae_path_closed h closed_wf hw)
  filter_upwards [ae_pos_path_clocks h s, hp, hwp] with z hz htrans hwf k hk
  apply lt_of_lt_of_le _ (le_max_right _ _)
  exact div_pos (hz k) (rateTotS_pos_of_transient hθA hθB h.rho
    ⟨hwf k, (htrans k).mp hk⟩)

theorem lintegral_clocks_holding {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (ω : ℕ → TS n KA KB) (k : ℕ) (hpos : 0 < rateTotS θA θB ρ (ω k)) :
    (∫⁻ e, f (holding θA θB ρ (ω, e) k) ∂clocks)
      = ∫⁻ t, f t ∂(expMeasure (rateTotS θA θB ρ (ω k))) := by
  calc (∫⁻ e, f (holding θA θB ρ (ω, e) k) ∂clocks)
      = ∫⁻ e, f (holdTime θA θB ρ (ω, e) k) ∂clocks := by
        apply lintegral_congr_ae
        filter_upwards [ae_pos_clocks] with e he
        congr 1
        exact max_eq_right (div_nonneg (le_of_lt (he k)) (le_of_lt hpos))
    _ = _ := lintegral_clocks_holdTime hf ω k hpos

end Rhone.Coalescent.ContinuousTime
