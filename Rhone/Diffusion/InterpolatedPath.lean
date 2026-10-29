/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Piecewise-linear interpolation of a sequence -/

@[expose] public section

namespace Rhone.Diffusion

open scoped NNReal

noncomputable def interpolatePrefix (a : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  a 0 + ∑ k ∈ Finset.range n, (a (k + 1) - a k) * max 0 (min 1 (s - k))

theorem continuous_interpolatePrefix (a : ℕ → ℝ) (n : ℕ) :
    Continuous (interpolatePrefix a n) := by
  unfold interpolatePrefix
  fun_prop

theorem interpolatePrefix_of_le (a : ℕ → ℝ) {n m : ℕ} {s : ℝ} (hs : s ≤ n) (hnm : n ≤ m) :
    interpolatePrefix a m s = interpolatePrefix a n s := by
  unfold interpolatePrefix
  congr 1
  symm
  refine Finset.sum_subset (Finset.range_mono hnm) fun k _ hk => ?_
  have hk' : (n : ℝ) ≤ k := by exact_mod_cast not_lt.1 (by simpa using hk)
  have h0 : min 1 (s - k) ≤ 0 := (min_le_right _ _).trans (by linarith)
  rw [max_eq_left h0, mul_zero]

noncomputable def interpolate (a : ℕ → ℝ) (s : ℝ) : ℝ := interpolatePrefix a ⌈s⌉₊ s

theorem interpolate_eq_interpolatePrefix (a : ℕ → ℝ) {n : ℕ} {s : ℝ} (hs : s ≤ n) :
    interpolate a s = interpolatePrefix a n s :=
  (interpolatePrefix_of_le a (Nat.le_ceil s) (Nat.ceil_le.2 hs)).symm

theorem continuous_interpolate (a : ℕ → ℝ) : Continuous (interpolate a) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have hlt : s < ((⌈s⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil s]
  refine ((continuous_interpolatePrefix a (⌈s⌉₊ + 1)).continuousAt).congr ?_
  filter_upwards [Iio_mem_nhds hlt] with u hu
  exact (interpolate_eq_interpolatePrefix a (le_of_lt hu)).symm

theorem interpolate_add (a : ℕ → ℝ) (m : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    interpolate a (m + θ) = a m + θ * (a (m + 1) - a m) := by
  have hs : (m : ℝ) + θ ≤ ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [interpolate_eq_interpolatePrefix a hs, interpolatePrefix, Finset.sum_range_succ]
  have hone : ∀ k ∈ Finset.range m,
      (a (k + 1) - a k) * max 0 (min 1 ((m : ℝ) + θ - k)) = a (k + 1) - a k := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hk
    rw [min_eq_left (by linarith), max_eq_right zero_le_one, mul_one]
  have hlast : max 0 (min 1 ((m : ℝ) + θ - m)) = θ := by
    rw [add_sub_cancel_left, min_eq_right h1, max_eq_right h0]
  rw [Finset.sum_congr rfl hone, Finset.sum_range_sub, hlast]
  ring

theorem interpolate_natCast (a : ℕ → ℝ) (m : ℕ) : interpolate a m = a m := by
  have h := interpolate_add a m le_rfl zero_le_one
  simpa using h

noncomputable def rescaledPath (τ : ℝ) (a : ℕ → ℝ) : C(ℝ≥0, ℝ) where
  toFun t := interpolate a (τ * t)
  continuous_toFun := by
    have h := continuous_interpolate a
    fun_prop

theorem rescaledPath_apply (τ : ℝ) (a : ℕ → ℝ) (t : ℝ≥0) :
    rescaledPath τ a t = interpolate a (τ * t) := rfl

end Rhone.Diffusion
