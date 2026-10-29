/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.XLinked
public import Rhone.Dynamics.XLinkedApproach
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable X-linked recursion equals the specification

Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/

@[expose] public section
namespace Rhone.Computation.XLinked
open Filter Topology

theorem xOrbit_cast (f0 m0 : Rat) (t : Nat) :
    (((xOrbit f0 m0 t).1 : Rat) : ℝ) = (Rhone.Dynamics.XLinked.xOrbit (f0 : ℝ) (m0 : ℝ) t).1 ∧
      (((xOrbit f0 m0 t).2 : Rat) : ℝ) =
        (Rhone.Dynamics.XLinked.xOrbit (f0 : ℝ) (m0 : ℝ) t).2 := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [xOrbit, xStep, Rhone.Dynamics.XLinked.xOrbit, Rhone.Dynamics.XLinked.xStep]
    refine ⟨?_, h1⟩
    push_cast
    rw [h1, h2]

theorem xOrbit_fst (f0 m0 : Rat) (t : Nat) : (xOrbit f0 m0 t).1 = fClosed f0 m0 t := by
  apply Rat.cast_injective (α := ℝ)
  rw [(xOrbit_cast f0 m0 t).1, Rhone.Dynamics.XLinked.xOrbit_fst, fClosed]
  push_cast
  rfl

theorem xOrbit_snd (f0 m0 : Rat) (t : Nat) : (xOrbit f0 m0 t).2 = mClosed f0 m0 t := by
  apply Rat.cast_injective (α := ℝ)
  rw [(xOrbit_cast f0 m0 t).2, Rhone.Dynamics.XLinked.xOrbit_snd, mClosed]
  push_cast
  rfl

theorem weightedMean_xOrbit (f0 m0 : Rat) (t : Nat) :
    weightedMean (xOrbit f0 m0 t) = weightedMean (f0, m0) := by
  apply Rat.cast_injective (α := ℝ)
  have h := Rhone.Dynamics.XLinked.xOrbit_weighted_mean (f0 : ℝ) (m0 : ℝ) t
  rw [← (xOrbit_cast f0 m0 t).1, ← (xOrbit_cast f0 m0 t).2] at h
  unfold weightedMean
  push_cast
  rw [h]

theorem xOrbit_diff (f0 m0 : Rat) (t : Nat) :
    (xOrbit f0 m0 t).1 - (xOrbit f0 m0 t).2 = (-1 / 2) ^ t * (f0 - m0) := by
  apply Rat.cast_injective (α := ℝ)
  have h := Rhone.Dynamics.XLinked.xOrbit_diff (f0 : ℝ) (m0 : ℝ) t
  rw [← (xOrbit_cast f0 m0 t).1, ← (xOrbit_cast f0 m0 t).2] at h
  push_cast at h ⊢
  exact h

theorem xOrbit_tendsto (f0 m0 : Rat) :
    Tendsto (fun t => (((xOrbit f0 m0 t).1 : Rat) : ℝ)) atTop
        (𝓝 (((weightedMean (f0, m0) : Rat) : ℝ))) ∧
      Tendsto (fun t => (((xOrbit f0 m0 t).2 : Rat) : ℝ)) atTop
        (𝓝 (((weightedMean (f0, m0) : Rat) : ℝ))) := by
  have hw : (((weightedMean (f0, m0) : Rat) : ℝ)) = (2 * (f0 : ℝ) + (m0 : ℝ)) / 3 := by
    unfold weightedMean
    push_cast
    rfl
  rw [hw]
  refine ⟨?_, ?_⟩
  · refine (Rhone.Dynamics.XLinked.tendsto_xOrbit_fst (f0 : ℝ) (m0 : ℝ)).congr (fun t => ?_)
    exact ((xOrbit_cast f0 m0 t).1).symm
  · refine (Rhone.Dynamics.XLinked.tendsto_xOrbit_snd (f0 : ℝ) (m0 : ℝ)).congr (fun t => ?_)
    exact ((xOrbit_cast f0 m0 t).2).symm

end Rhone.Computation.XLinked
