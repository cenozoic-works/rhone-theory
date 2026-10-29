/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanModel

/-! # Cumulative clocks and decay for the AC/AE pan model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

noncomputable def integrablePanClock (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, panZeroExtension rate s

@[simp] theorem integrablePanClock_zero (rate : ℝ → ℝ) : integrablePanClock rate 0 = 0 := by
  simp [integrablePanClock]

theorem integrablePanClock_eq_integral (rate : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    integrablePanClock rate t = ∫ s in (0 : ℝ)..t, rate s := by
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ (fun s hs => panZeroExtension_of_nonneg rate
    ((by simpa only [uIoc_of_le ht, mem_Ioc] using hs : 0 < s ∧ s ≤ t).1.le))

theorem integrablePanClock_ac {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (integrablePanClock rate) a b := by
  exact (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable
    (panZeroExtension_locallyIntegrable hr) (min 0 (min a b)) (max 0 (max a
      b))).absolutelyContinuousOnInterval_intervalIntegral
    (by simp) |>.mono (by
      intro t ht
      rw [uIcc_of_le (le_trans (min_le_left _ _) (le_max_left _ _))]
      exact ⟨(min_le_right _ _).trans ht.1, ht.2.trans (le_max_right _ _)⟩)

theorem integrablePanClock_ae_hasDerivAt {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (integrablePanClock rate) (rate t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (panZeroExtension_locallyIntegrable hr)] with t ht ht0
  change HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, panZeroExtension rate s) (rate t) t
  rw [← panZeroExtension_of_nonneg rate ht0]
  exact ht 0

theorem integrablePanClock_nonneg {rate : ℝ → ℝ}
    (hr : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ integrablePanClock rate t := by
  apply intervalIntegral.integral_nonneg_of_ae ht
  filter_upwards [hr] with s hs
  change 0 ≤ panZeroExtension rate s
  by_cases hs0 : 0 ≤ s
  · simpa only [panZeroExtension_of_nonneg rate hs0] using hs hs0
  · simp only [panZeroExtension_of_neg rate (lt_of_not_ge hs0), le_refl]

theorem integrablePanClock_monotoneOn {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) :
    MonotoneOn (integrablePanClock rate) (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  have hn : AntitoneOn (fun t => -integrablePanClock rate t) (uIcc 0 b) := by
    apply ac_antitoneOn_of_ae_hasDerivAt_nonpos (integrablePanClock_ac hr 0 b).neg
      (fDot := fun t => -rate t)
    · filter_upwards [integrablePanClock_ae_hasDerivAt hr] with t ht hmem
      exact (ht ((by simpa only [uIcc_of_le hb, mem_Icc] using hmem : 0 ≤ t ∧ t ≤ b).1)).neg
    · filter_upwards [hrn] with t ht hmem
      exact neg_nonpos.mpr (ht ((by simpa only [uIcc_of_le hb, mem_Icc] using hmem : 0 ≤ t ∧ t ≤
        b).1))
  exact neg_le_neg_iff.mp (hn (by simpa only [uIcc_of_le hb, mem_Icc] using And.intro ha hab)
    (by simp) hab)

def IntegrablePanPreModel.total {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate) (t : ℝ) : ℝ :=
  P.D t + (P.R t + P.U t)

@[simp] theorem IntegrablePanPreModel.total_zero {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) : P.total 0 = 1 := by
  simp [IntegrablePanPreModel.total, P.initial]

theorem IntegrablePanPreModel.total_ac {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) {t : ℝ} (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval P.total 0 t :=
  (P.D_ac t ht).fun_add ((P.R_ac t ht).fun_add (P.U_ac t ht))

theorem IntegrablePanPreModel.total_positive {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) {t : ℝ} (ht : 0 ≤ t) : 0 < P.total t :=
  add_pos_of_pos_of_nonneg (P.D_positive t ht) (add_nonneg (P.R_nonneg t ht) (P.U_nonneg t ht))

theorem IntegrablePanPreModel.total_ae_hasDerivAt {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt P.total
      (-rate t * (P.D t + 2 * (P.R t + P.U t))) t := by
  filter_upwards [P.equations] with t ht ht0
  obtain ⟨hD, hR, hU⟩ := ht ht0
  convert! hD.add (hR.add hU) using 1
  ring

theorem IntegrablePanPreModel.total_le_exp_neg_clock {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) {t : ℝ} (ht : 0 ≤ t) :
    P.total t ≤ Real.exp (-integrablePanClock rate t) := by
  have hfd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt P.total
      (-rate s * (P.D s + 2 * (P.R s + P.U s))) s := by
    filter_upwards [P.total_ae_hasDerivAt] with s hs hmem
    exact hs ((by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1)
  have hHd : ∀ᵐ s, s ∈ uIcc 0 t →
      HasDerivAt (integrablePanClock rate) (rate s) s := by
    filter_upwards [integrablePanClock_ae_hasDerivAt P.rate_integrable] with s hs hmem
    exact hs ((by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1)
  have hbound : ∀ᵐ s, s ∈ uIcc 0 t →
      -rate s * (P.D s + 2 * (P.R s + P.U s)) ≤ -rate s * P.total s := by
    filter_upwards [P.rate_nonneg] with s hs hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    dsimp [IntegrablePanPreModel.total]
    nlinarith [mul_nonneg (hs hs0) (add_nonneg (P.R_nonneg s hs0) (P.U_nonneg s hs0))]
  have h := ac_comparison_upper P.total
    (fun s => -rate s * (P.D s + 2 * (P.R s + P.U s)))
    (integrablePanClock rate) rate 0 t ht (P.total_ac ht)
    (integrablePanClock_ac P.rate_integrable 0 t) hfd hHd hbound
  simpa only [P.total_zero, integrablePanClock_zero, zero_sub, one_mul] using h

theorem IntegrablePanPreModel.D_lower_bound {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(integrablePanClock rate t + 2 * integrablePanClock P.recomb t)) ≤ P.D t := by
  let H := fun s => integrablePanClock rate s + 2 * integrablePanClock P.recomb s
  let c := fun s => rate s + 2 * P.recomb s
  let fDot := fun s => rate s * (P.R s - P.D s) - 2 * P.recomb s * P.D s
  have hHac : AbsolutelyContinuousOnInterval H 0 t :=
    (integrablePanClock_ac P.rate_integrable 0 t).fun_add
      ((integrablePanClock_ac P.recomb_integrable 0 t).const_mul 2)
  have hfd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt P.D (fDot s) s := by
    filter_upwards [P.equations] with s hs hmem
    exact (hs ((by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1)).1
  have hHd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt H (c s) s := by
    filter_upwards [integrablePanClock_ae_hasDerivAt P.rate_integrable,
      integrablePanClock_ae_hasDerivAt P.recomb_integrable] with s hrs hρs hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    exact (hrs hs0).add ((hρs hs0).const_mul 2)
  have hbound : ∀ᵐ s, s ∈ uIcc 0 t → -c s * P.D s ≤ fDot s := by
    filter_upwards [P.rate_nonneg] with s hrs hmem
    have hs0 : 0 ≤ s :=
      (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    dsimp [c, fDot]
    nlinarith [mul_nonneg (hrs hs0) (P.R_nonneg s hs0)]
  have h := ac_comparison_lower P.D fDot H c 0 t ht (P.D_ac t ht) hHac hfd hHd hbound
  simpa only [H, integrablePanClock_zero, mul_zero, add_zero, P.initial.1, one_mul,
    zero_sub] using h

theorem IntegrablePanPreModel.D_compact_lower_bound {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) (T : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 T, ε ≤ P.D t := by
  refine ⟨Real.exp (-(integrablePanClock rate T + 2 * integrablePanClock P.recomb T)),
    Real.exp_pos _, ?_⟩
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hr := integrablePanClock_monotoneOn P.rate_integrable P.rate_nonneg ht.1 hT ht.2
  have hρ := integrablePanClock_monotoneOn P.recomb_integrable P.recomb_nonneg ht.1 hT ht.2
  exact (Real.exp_le_exp.mpr (by linarith)).trans (P.D_lower_bound ht.1)

theorem IntegrablePanPreModel.total_le_one {rate : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) {t : ℝ} (ht : 0 ≤ t) : P.total t ≤ 1 :=
  (P.total_le_exp_neg_clock ht).trans
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integrablePanClock_nonneg P.rate_nonneg ht)))

structure ProperIntegrablePanModel where
  rate : ℝ → ℝ
  pre : IntegrablePanPreModel rate
  clock_diverges : Tendsto (integrablePanClock rate) atTop atTop

theorem ProperIntegrablePanModel.total_tendsto_zero (P : ProperIntegrablePanModel) :
    Tendsto P.pre.total atTop (𝓝 0) := by
  have hlim := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp P.clock_diverges)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (P.pre.total_positive ht).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact P.pre.total_le_exp_neg_clock ht

end Rhone.Statistics.Identifiability
