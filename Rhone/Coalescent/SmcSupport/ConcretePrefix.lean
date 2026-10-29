/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Prefix
public import Rhone.Coalescent.SmcSupport.Successors
public import Rhone.Coalescent.SmcSupport.StateSupport

/-! # Finite prefix failure bounds for the coalescence updates of the sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

def coalNext (n : ℕ) (s : CountState (n + 1))
    (k : CoalChoices n) : CountState n := by
  have hc : s.val.2.2.1 = n + 2 := by have := s.property.2; omega
  let i : Fin s.val.2.2.1 := Fin.cast hc.symm k.val.1
  let j : Fin s.val.2.2.1 := Fin.cast hc.symm k.val.2
  have hij : i.val < j.val := k.property
  refine ⟨coalSuccessor s.val i j, coalSuccessor_valid s.val s.property.1 i j, ?_⟩
  have hh := coalSuccessor_count s.val i j hij
  omega

def initialCountState (n : ℕ) : CountState n :=
  ⟨initialState (n + 1), initialState_valid (n + 1), rfl⟩

noncomputable def firstSplitNext (n : ℕ) (s : CountState n) (hs : ZeroSplitReachable s.val)
    (i : Fin s.val.2.2.1) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    CountState (n + 1) := by
  refine ⟨splitSuccessor s.val i x, ?_, ?_⟩
  · exact splitSuccessor_full_valid s.val s.property.1 (zeroSplit_full hs) i x hx0 hx1
  · have hh := splitSuccessor_count s.val i x
    have hc := s.property.2
    omega

noncomputable def coalPrefixFailure (R : ℝ) (n : ℕ) (s : CountState n) : ℝ :=
  prefixFailure R coalNext n s

theorem coalPrefixFailure_le (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (s : CountState n) :
    coalPrefixFailure R n s ≤ raceBound (hazard R) n :=
  prefixFailure_le R hR coalNext n s

theorem firstSplit_prefixFailure_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState n) (hs : ZeroSplitReachable s.val)
    (i : Fin s.val.2.2.1) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    coalPrefixFailure R (n + 1) (firstSplitNext n s hs i x hx0 hx1) ≤
      raceBound (hazard R) (n + 1) :=
  coalPrefixFailure_le R hR _ _

theorem recombinationRace_full (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) (hs : AllMaterials FullAtoms s.val) :
    recombinationRace R n s = hazard R n := by
  have hc : (s.val.2.2.1 : ℝ) = (n : ℝ) + 2 := by
    rw [s.property.2]
    push_cast
    ring
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 + R * ((n : ℝ) + 2) / 2 ≠ 0 :=
    ne_of_gt (by positivity)
  have hr : (n : ℝ) + 1 + R ≠ 0 := ne_of_gt (by positivity)
  unfold recombinationRace hazard
  rw [full_recombinationRate R hs, hc]
  field_simp

theorem recombinationRace_zeroSplit (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) (hs : ZeroSplitReachable s.val) :
    recombinationRace R n s = hazard R n :=
  recombinationRace_full R hR n s (zeroSplit_full hs)

theorem phaseOne_barrier_step (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) :
    recombinationRace R n s + (1 - recombinationRace R n s) * raceBound (hazard R) n ≤
      raceBound (hazard R) (n + 1) := by
  have hq := recombinationRace_bounds R hR n s
  have hp := raceBound_nonneg_le_one (hazard R) (fun j => hazard_bounds R hR j) n
  have hm := mul_le_mul_of_nonneg_right hq.2 (sub_nonneg.mpr hp.2)
  rw [raceBound]
  nlinarith

theorem phaseZero_barrier_step (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) (hs : ZeroSplitReachable s.val) :
    (1 - recombinationRace R n s) * doubleBound R n +
      recombinationRace R n s * raceBound (hazard R) (n + 2) = doubleBound R (n + 1) := by
  rw [recombinationRace_zeroSplit R hR n s hs]
  rfl

theorem phaseZero_full_barrier_step (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) (hs : AllMaterials FullAtoms s.val) :
    (1 - recombinationRace R n s) * doubleBound R n +
      recombinationRace R n s * raceBound (hazard R) (n + 2) = doubleBound R (n + 1) := by
  rw [recombinationRace_full R hR n s hs]
  rfl

end Rhone.Coalescent.SmcSupport
