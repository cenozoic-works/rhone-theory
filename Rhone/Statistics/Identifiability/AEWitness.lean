/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Panmixia
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Null-set robust separation of forward observables -/

@[expose] public section

open MeasureTheory Filter Set

namespace Rhone.Statistics.Identifiability

theorem witness_continuous (k : Nat) (c q r : ℝ) :
    Continuous (witness k c q r) :=
  continuous_iff_continuousAt.mpr fun t =>
    (witness_hasDerivAt k c q r t).continuousAt

theorem island_witness_not_ae_zero (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ (witness k c q r =ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] fun _ => 0) := by
  intro hz
  have heq : EqOn (witness k c q r) (fun _ => 0) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hz isOpen_Ioi
      (witness_continuous k c q r).continuousOn continuous_const.continuousOn
  apply island_witness_not_identically_zero k hc hq hr
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · simp [← hzero]
  · exact heq hpos

theorem no_ae_matching_pan_forward_observables (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ ∃ (rate survival : ℝ → ℝ) (mass : ℝ → PanState → ℝ),
      ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioi 0),
        survivalJet k c q 0 t = survival t ∧
        densityJet k c q 0 t = panPairDensity (rate t) (survival t) ∧
        firstAJet k c q r 0 t = panFirstA (rate t) (mass t) ∧
        postBJet k c q r 0 t = panNextB (rate t) (mass t) := by
  rintro ⟨rate, survival, mass, hmatch⟩
  apply island_witness_not_ae_zero k hc hq hr
  filter_upwards [hmatch] with t ht
  rcases ht with ⟨hs, hf, hb, hj⟩
  unfold witness
  rw [hs, hf, hb, hj]
  exact pan_witness_zero (rate t) (survival t) (mass t)

end Rhone.Statistics.Identifiability
