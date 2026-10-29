/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Prefix
public import Rhone.Coalescent.SmcSupport.Agreement
public import Rhone.Coalescent.SmcSupport.Selector
public import Rhone.Coalescent.FiniteIntervalMaterialPairRates

/-! # The marked event rates equal the hull-rate calculation -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem splitRate_eq_recombinationRate (R : ℝ) (hR : 0 ≤ R) (s : State) :
    (splitRate R s : ℝ) = recombinationRate R s := by
  classical
  simp only [splitRate, NNReal.coe_sum]
  unfold recombinationRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact candidateRate_split_eq false R hR s i

theorem totalRate_unrestricted_real (R : ℝ) (hR : 0 ≤ R) (s : State) :
    (totalRate false R s : ℝ) =
      (s.2.2.1 : ℝ) * ((s.2.2.1 : ℝ) - 1) / 2 + recombinationRate R s := by
  rw [totalRate_eq, NNReal.coe_add, coalRate_unrestricted,
    splitRate_eq_recombinationRate R hR s]

theorem markedLaw_unrestricted_split_race (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState (n + 1)) :
    (markedLaw false R s.val splitSet).toReal = recombinationRace R n s := by
  have hc : s.val.2.2.1 = n + 2 := by have := s.property.2; omega
  have hm : 2 ≤ s.val.2.2.1 := by omega
  have ht := unrestricted_totalRate_positive R s.val hm
  rw [markedLaw_split_mass false R s.val (by omega) (ne_of_gt ht),
    ENNReal.toReal_div]
  simp only [ENNReal.coe_toReal]
  rw [splitRate_eq_recombinationRate R hR s.val,
    totalRate_unrestricted_real R hR s.val]
  unfold recombinationRace
  rw [hc]
  push_cast
  congr 2
  ring

theorem markedLaw_contact_split_race (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState (n + 1))
    (hs : ∀ i j, touches (s.val.2.2.2 i).2 (s.val.2.2.2 j).2) :
    (markedLaw mode R s.val splitSet).toReal = recombinationRace R n s := by
  cases mode with
  | false => exact markedLaw_unrestricted_split_race R hR n s
  | true =>
    rw [← markedLaw_agreement R s.val hs]
    exact markedLaw_unrestricted_split_race R hR n s

theorem markedLaw_contact_split_le_hazard (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState (n + 1))
    (hs : ∀ i j, touches (s.val.2.2.2 i).2 (s.val.2.2.2 j).2) :
    (markedLaw mode R s.val splitSet).toReal ≤
      Rhone.Coalescent.SmcBound.hazard R n := by
  rw [markedLaw_contact_split_race mode R hR n s hs]
  exact (recombinationRace_bounds R hR n s).2

end Rhone.Coalescent.SmcSupport
