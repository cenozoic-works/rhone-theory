/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Rhone.Coalescent.SmcBound.Bounds
public import Rhone.Coalescent.FiniteIntervalMaterialState
public import Rhone.Coalescent.FiniteIntervalMaterialArrays

/-! # Barrier function on the split-counting phase of the tracked sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

inductive Phase | zero | one | two
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.zero, .one, .two}, by intro p; cases p <;> simp⟩

instance : MeasurableSpace Phase := ⊤

abbrev TrackedState := State × Phase × EventRecord

def advancePhase : Phase → Event → Phase
  | .two, _ => .two
  | .zero, .inr (.inr _) => .one
  | .one, .inr (.inr _) => .two
  | p, _ => p

def trackedInitial (n : ℕ) : TrackedState :=
  (initialState n, .zero, (0, .inl ()))

noncomputable def barrier (R : ℝ) (z : TrackedState) : ℝ :=
  match z.2.1 with
  | .zero => doubleBound R (z.1.2.2.1 - 1)
  | .one => raceBound (hazard R) (z.1.2.2.1 - 1)
  | .two => 1

theorem liveCount_measurable : Measurable (fun s : State => s.2.2.1) := by
  have h : Measurable (fun a : LiveState => a.1) :=
    measurable_sigma_of_fibers _ (fun _ => measurable_const)
  exact h.comp measurable_snd.snd

theorem barrier_measurable (R : ℝ) : Measurable (barrier R) := by
  have h : Measurable (fun q : ℕ × Phase => match q.2 with
      | .zero => doubleBound R (q.1 - 1)
      | .one => raceBound (hazard R) (q.1 - 1)
      | .two => 1) := measurable_of_countable _
  exact h.comp ((liveCount_measurable.comp measurable_fst).prodMk measurable_snd.fst)

theorem barrier_bounds (R : ℝ) (hR : 0 ≤ R) (z : TrackedState) :
    0 ≤ barrier R z ∧ barrier R z ≤ 1 := by
  unfold barrier
  cases z.2.1 with
  | zero => exact ⟨doubleBound_nonneg R hR _, doubleBound_le_one R hR _⟩
  | one => exact raceBound_nonneg_le_one (hazard R) (hazard_bounds R hR) _
  | two => exact ⟨by norm_num, le_rfl⟩

theorem barrier_flag (R : ℝ) (hR : 0 ≤ R) (z : TrackedState) :
    (if z.2.1 = .two then (1 : ℝ) else 0) ≤ barrier R z := by
  by_cases h : z.2.1 = .two
  · simp [h, barrier]
  · simp only [h, ↓reduceIte]
    exact (barrier_bounds R hR z).1

theorem barrier_initial (R : ℝ) (n : ℕ) :
    barrier R (trackedInitial n) = doubleBound R (n - 1) := rfl

theorem advancePhase_two (e : Event) : advancePhase .two e = .two := rfl

end Rhone.Coalescent.SmcSupport
