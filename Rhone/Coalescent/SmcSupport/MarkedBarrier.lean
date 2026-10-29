/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.MarkedEventRates
public import Rhone.Coalescent.SmcSupport.ConcretePrefix
public import Rhone.Coalescent.SmcSupport.ContactClosure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrating branch values against the marked event law -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory

noncomputable def markMixtureReward (pairValue splitValue : ℝ) (e : Event) : ℝ := by
  classical
  exact coalSet.indicator (fun _ => pairValue) e +
    splitSet.indicator (fun _ => splitValue) e

theorem integral_markMixtureReward (mode : Mode) (R : ℝ) (s : State)
    (pairValue splitValue : ℝ) :
    (∫ e, markMixtureReward pairValue splitValue e ∂markedLaw mode R s) =
      (markedLaw mode R s coalSet).toReal * pairValue +
      (markedLaw mode R s splitSet).toReal * splitValue := by
  unfold markMixtureReward
  rw [integral_add ((integrable_const pairValue).indicator coalSet_measurable)
    ((integrable_const splitValue).indicator splitSet_measurable),
    integral_indicator_const pairValue coalSet_measurable,
    integral_indicator_const splitValue splitSet_measurable]
  rfl

theorem marked_branch_mass_sum (mode : Mode) (R : ℝ) (s : State)
    (hm : 1 < s.2.2.1) (ht : totalRate mode R s ≠ 0) :
    (markedLaw mode R s coalSet).toReal +
      (markedLaw mode R s splitSet).toReal = 1 := by
  rw [markedLaw_coal_mass mode R s hm ht, markedLaw_split_mass mode R s hm ht]
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal]
  have he : (coalRate mode s : ℝ) + (splitRate R s : ℝ) =
      (totalRate mode R s : ℝ) := by
    rw [totalRate_eq, NNReal.coe_add]
  rw [← add_div, he, div_self]
  exact_mod_cast ht

theorem contact_totalRate_positive (mode : Mode) (R : ℝ) (s : State)
    (hm : 2 ≤ s.2.2.1)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    0 < totalRate mode R s := by
  cases mode with
  | false => exact unrestricted_totalRate_positive R s hm
  | true =>
    have he : totalRate false R s = totalRate true R s := by
      unfold totalRate
      rw [candidateRate_agreement R s hs]
    rw [← he]
    exact unrestricted_totalRate_positive R s hm

theorem marked_phase_one_barrier (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState (n + 1))
    (hs : ∀ i j, touches (s.val.2.2.2 i).2 (s.val.2.2.2 j).2) :
    (∫ e, markMixtureReward (raceBound (hazard R) n) 1 e
      ∂markedLaw mode R s.val) ≤ raceBound (hazard R) (n + 1) := by
  have hm : 2 ≤ s.val.2.2.1 := by have := s.property.2; omega
  have ht := contact_totalRate_positive mode R s.val hm hs
  have hsum := marked_branch_mass_sum mode R s.val (by omega) (ne_of_gt ht)
  have hq := markedLaw_contact_split_race mode R hR n s hs
  have hc : (markedLaw mode R s.val coalSet).toReal = 1 - recombinationRace R n s := by
    rw [hq] at hsum
    linarith
  rw [integral_markMixtureReward, hc, hq, mul_one]
  have h := phaseOne_barrier_step R hR n s
  linarith

theorem marked_phase_zero_barrier (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState (n + 1)) (hs : AllMaterials FullAtoms s.val) :
    (∫ e, markMixtureReward (doubleBound R n) (raceBound (hazard R) (n + 2)) e
      ∂markedLaw mode R s.val) = doubleBound R (n + 1) := by
  have hcontact := full_contacts s.val hs
  have hm : 2 ≤ s.val.2.2.1 := by have := s.property.2; omega
  have ht := contact_totalRate_positive mode R s.val hm hcontact
  have hsum := marked_branch_mass_sum mode R s.val (by omega) (ne_of_gt ht)
  have hq := markedLaw_contact_split_race mode R hR n s hcontact
  have hc : (markedLaw mode R s.val coalSet).toReal = 1 - recombinationRace R n s := by
    rw [hq] at hsum
    linarith
  rw [integral_markMixtureReward, hc, hq]
  exact phaseZero_full_barrier_step R hR n s hs

end Rhone.Coalescent.SmcSupport
