/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanForwardSeparation

/-! # Every locally integrable pair-rate history supplies the required clock -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def integratedClock (rate : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in 0..t, rate x

theorem locallyIntegrable_interval (rate : ℝ → ℝ) (h : LocallyIntegrable rate volume) (a b : ℝ) :
    IntervalIntegrable rate volume a b :=
  intervalIntegrable_iff.mpr
    ((h.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

theorem integratedClock_continuous (rate : ℝ → ℝ) (h : LocallyIntegrable rate volume) :
    Continuous (integratedClock rate) :=
  intervalIntegral.continuous_primitive (locallyIntegrable_interval rate h) 0

theorem integratedClock_ac (rate : ℝ → ℝ) (h : LocallyIntegrable rate volume)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    AbsolutelyContinuousOnInterval (integratedClock rate) s t := by
  have hi := locallyIntegrable_interval rate h 0 t
  have hbase := hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  apply hbase.mono
  rw [uIcc_of_le hst.le, uIcc_of_le (lt_trans hs hst).le]
  intro x hx
  exact ⟨le_trans hs.le hx.1,hx.2⟩

theorem integratedClock_derivative_ae (rate : ℝ → ℝ) (h : LocallyIntegrable rate volume)
    (s t : ℝ) : ∀ᵐ x, x ∈ uIcc s t → HasDerivAt (integratedClock rate) (rate x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral h] with x hx
  intro _
  exact hx 0

theorem panPost_survival_integrated_clock (rate recomb : ℝ → ℝ)
    (hRate : LocallyIntegrable rate volume) (p : ℝ → Fin 2 → ℝ) {s t : ℝ}
    (hs : 0 < s) (hst : s < t)
    (hpac : ∀ i, AbsolutelyContinuousOnInterval (fun x => p x i) s t)
    (hp : ∀ᵐ x, x ∈ uIcc s t → ∀ i, HasDerivAt (fun y => p y i)
      (∑ j, p x j * panPostGenerator (rate x) (recomb x) j i) x) :
    (∑ i, p t i) = (∑ i, p s i) *
      Real.exp (integratedClock rate s - integratedClock rate t) :=
  panPost_survival_clock_ae rate recomb (integratedClock rate) p s t hpac
    (integratedClock_ac rate hRate hs hst) hp (integratedClock_derivative_ae rate hRate s t)

end Rhone.Statistics.Identifiability
