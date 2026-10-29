/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Rhone.Statistics.Identifiability.PanClockCDF

/-! # Positive two-epoch realization of pair/three first-merger means -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

noncomputable def epochEarly (d z : ℝ) : ℝ := d*z*(3-z)/(1-z^2)
noncomputable def epochLate (d z : ℝ) : ℝ := d*(1-z)^2/(z*(1+z))
noncomputable def epochMoment (u v z : ℝ) (j : ℕ) : ℝ :=
  (u*(1-z^j)+v*z^j)/(j : ℝ)

theorem epochEarly_pos {d z : ℝ} (hd : 0 < d) (hz : 0 < z) (hz1 : z < 1) :
    0 < epochEarly d z := by
  unfold epochEarly
  exact div_pos (mul_pos (mul_pos hd hz) (by linarith)) (by nlinarith)

theorem epochLate_pos {d z : ℝ} (hd : 0 < d) (hz : 0 < z) (hz1 : z < 1) :
    0 < epochLate d z := by
  unfold epochLate
  exact div_pos (mul_pos hd (sq_pos_of_pos (by linarith))) (mul_pos hz (by linarith))

theorem twoEpoch_moments {d z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    epochMoment (epochEarly d z) (epochLate d z) z 1 = d ∧
    epochMoment (epochEarly d z) (epochLate d z) z 3 = d*z := by
  have h1 : 1-z^2 ≠ 0 := by nlinarith
  have h2 : z ≠ 0 := ne_of_gt hz
  have h3 : 1+z ≠ 0 := by linarith
  constructor <;> unfold epochMoment epochEarly epochLate <;>
    norm_num <;> field_simp <;> ring

theorem positive_twoEpoch_realization {d a : ℝ} (ha : 0 < a) (had : a < d) :
    ∃ u v z : ℝ, 0 < u ∧ 0 < v ∧ 0 < z ∧ z < 1 ∧
      epochMoment u v z 1 = d ∧ epochMoment u v z 3 = a := by
  have hd : 0 < d := lt_trans ha had
  have hz : 0 < a/d := div_pos ha hd
  have hz1 : a/d < 1 := (div_lt_one hd).mpr had
  refine ⟨epochEarly d (a/d),epochLate d (a/d),a/d,
    epochEarly_pos hd hz hz1,epochLate_pos hd hz hz1,hz,hz1,?_,?_⟩
  · exact (twoEpoch_moments hz hz1).1
  · rw [(twoEpoch_moments hz hz1).2]
    field_simp

end Rhone.Statistics.Identifiability
