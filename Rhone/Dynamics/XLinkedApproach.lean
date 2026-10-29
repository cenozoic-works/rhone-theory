/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Approach to equilibrium at an X-linked locus

Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/

@[expose] public section

namespace Rhone.Dynamics.XLinked

open Filter Topology

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
noncomputable def xStep (x : ℝ × ℝ) : ℝ × ℝ := ((x.1 + x.2) / 2, x.1)

noncomputable def xOrbit (f0 m0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (f0, m0)
  | t + 1 => xStep (xOrbit f0 m0 t)

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem xOrbit_weighted_mean (f0 m0 : ℝ) (t : ℕ) :
    (2 * (xOrbit f0 m0 t).1 + (xOrbit f0 m0 t).2) / 3 = (2 * f0 + m0) / 3 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [xOrbit, xStep]
    linarith

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem xOrbit_diff (f0 m0 : ℝ) (t : ℕ) :
    (xOrbit f0 m0 t).1 - (xOrbit f0 m0 t).2 = (-1 / 2) ^ t * (f0 - m0) := by
  induction t with
  | zero => simp [xOrbit]
  | succ t ih =>
    simp only [xOrbit, xStep]
    rw [pow_succ]
    linarith

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem xOrbit_fst (f0 m0 : ℝ) (t : ℕ) :
    (xOrbit f0 m0 t).1 = (2 * f0 + m0) / 3 + (1 / 3) * (-1 / 2) ^ t * (f0 - m0) := by
  have h1 := xOrbit_weighted_mean f0 m0 t
  have h2 := xOrbit_diff f0 m0 t
  linarith

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem xOrbit_snd (f0 m0 : ℝ) (t : ℕ) :
    (xOrbit f0 m0 t).2 = (2 * f0 + m0) / 3 - (2 / 3) * (-1 / 2) ^ t * (f0 - m0) := by
  have h1 := xOrbit_weighted_mean f0 m0 t
  have h2 := xOrbit_diff f0 m0 t
  linarith

private theorem tendsto_half_pow :
    Tendsto (fun t : ℕ => (-1 / 2 : ℝ) ^ t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem tendsto_xOrbit_fst (f0 m0 : ℝ) :
    Tendsto (fun t => (xOrbit f0 m0 t).1) atTop (𝓝 ((2 * f0 + m0) / 3)) := by
  have h := ((tendsto_half_pow.const_mul (1 / 3 : ℝ)).mul_const (f0 - m0)).const_add
    ((2 * f0 + m0) / 3)
  simp only [mul_zero, zero_mul, add_zero] at h
  refine h.congr (fun t => ?_)
  rw [xOrbit_fst]

/-- Source: crow_kimura1970, sec. 2.5, eq. (2.5.4), pp. 45–47. -/
theorem tendsto_xOrbit_snd (f0 m0 : ℝ) :
    Tendsto (fun t => (xOrbit f0 m0 t).2) atTop (𝓝 ((2 * f0 + m0) / 3)) := by
  have h := ((tendsto_half_pow.const_mul (2 / 3 : ℝ)).mul_const (f0 - m0)).const_sub
    ((2 * f0 + m0) / 3)
  simp only [mul_zero, zero_mul, sub_zero] at h
  refine h.congr (fun t => ?_)
  rw [xOrbit_snd]

end Rhone.Dynamics.XLinked
