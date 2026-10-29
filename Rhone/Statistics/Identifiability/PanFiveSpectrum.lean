/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanFiveData
public import Rhone.Statistics.Identifiability.IntegratedClock

/-! # A universal fifth-sample panmictic spectrum inequality -/

@[expose] public section

open scoped ENNReal
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem integratedClock_ac_zero (rate : ℝ → ℝ) (h : LocallyIntegrable rate volume) (t : ℝ) :
    AbsolutelyContinuousOnInterval (integratedClock rate) 0 t :=
  (locallyIntegrable_interval rate h 0 t).absolutelyContinuousOnInterval_intervalIntegral (by simp)

theorem zero_solution_scaled_clock (S rate : ℝ → ℝ) (hRate : LocallyIntegrable rate volume)
    (a t : ℝ) (hSac : AbsolutelyContinuousOnInterval S 0 t) (hzero : S 0 = 0)
    (hS : ∀ᵐ x, x ∈ uIcc 0 t → HasDerivAt S (-(a * rate x) * S x) x) : S t = 0 := by
  have hac := AbsolutelyContinuousOnInterval.const_mul a (integratedClock_ac_zero rate hRate t)
  have hH : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt (fun y => a * integratedClock rate y) (a * rate x) x := by
    filter_upwards [integratedClock_derivative_ae rate hRate 0 t] with x hx
    intro hmem
    exact (hx hmem).const_mul a
  have h := survival_clock_of_ac_forward_equation S (fun x => a*rate x)
    (fun x => a*integratedClock rate x) 0 t hSac hac hS hH
  simpa only [hzero, zero_mul] using h

structure PanFiveForwardSystem where
  rate : ℝ → ℝ
  rate_nonneg : ∀ t, 0 ≤ rate t
  rate_locallyIntegrable : LocallyIntegrable rate volume
  mass : ℝ → PanFiveState → ℝ
  initial_mass : ∀ i, mass 0 i = if i = 0 then 1 else 0
  mass_nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ mass t i
  mass_ac : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun x => mass x i) 0 t
  mass_equation : ∀ t, 0 ≤ t → ∀ᵐ x, x ∈ uIcc 0 t → ∀ i,
    HasDerivAt (fun y => mass y i) (∑ j, mass x j * panFiveGenerator (rate x) j i) x

theorem PanFiveForwardSystem.three_state_symmetry (P : PanFiveForwardSystem)
    (t : ℝ) (ht : 0 ≤ t) : P.mass t 2 - P.mass t 3 = 0 := by
  apply zero_solution_scaled_clock (fun x => P.mass x 2 - P.mass x 3)
    P.rate P.rate_locallyIntegrable 3 t
  · convert! (P.mass_ac t ht 2).sub (P.mass_ac t ht 3) using 1
  · simp [P.initial_mass, show (2 : PanFiveState) ≠ 0 by decide,
      show (3 : PanFiveState) ≠ 0 by decide]
  · filter_upwards [P.mass_equation t ht] with x hx
    intro hmem
    have h := ((hx hmem 2).sub (hx hmem 3))
    rw [panFive_three_state_difference] at h
    convert! h using 1
    ring

theorem PanFiveForwardSystem.two_state_symmetry (P : PanFiveForwardSystem)
    (t : ℝ) (ht : 0 ≤ t) : P.mass t 4 - P.mass t 5 = 0 := by
  apply zero_solution_scaled_clock (fun x => P.mass x 4 - P.mass x 5)
    P.rate P.rate_locallyIntegrable 1 t
  · convert! (P.mass_ac t ht 4).sub (P.mass_ac t ht 5) using 1
  · simp [P.initial_mass, show (4 : PanFiveState) ≠ 0 by decide,
      show (5 : PanFiveState) ≠ 0 by decide]
  · filter_upwards [P.mass_equation t ht] with x hx
    intro hmem
    have h := ((hx hmem 4).sub (hx hmem 5))
    rw [panFive_two_state_difference,
      P.three_state_symmetry x (by rw [uIcc_of_le ht] at hmem; exact hmem.1)] at h
    convert! h using 1
    ring

theorem PanFiveForwardSystem.reward_tail_nonneg (P : PanFiveForwardSystem)
    (t : ℝ) (ht : 0 ≤ t) : panFiveReward 4 (P.mass t) ≤ panFiveReward 3 (P.mass t) := by
  have h := panFive_reward_tail (P.mass t)
  have hsym := P.two_state_symmetry t ht
  have hp := P.mass_nonneg t ht 2
  linarith

noncomputable def PanFiveForwardSystem.expectedBranch (P : PanFiveForwardSystem) (w : Nat) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (panFiveReward w (P.mass t))

theorem PanFiveForwardSystem.spectrum_tail_monotone (P : PanFiveForwardSystem) :
    P.expectedBranch 4 ≤ P.expectedBranch 3 := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact ENNReal.ofReal_le_ofReal (P.reward_tail_nonneg t ht.le)

end Rhone.Statistics.Identifiability
