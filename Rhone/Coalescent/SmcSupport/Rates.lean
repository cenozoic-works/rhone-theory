/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialState
public import Rhone.Coalescent.SmcBound.Bounds

/-! # Rate bounds for the concrete finite-atom ancestral state -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

theorem hull_bounds (a : Material) (ha : MaterialValid a) :
    0 ≤ hullLo a ∧ hullLo a ≤ hullHi a ∧ hullHi a ≤ 1 := by
  classical
  have hlo : 0 ≤ hullLo a := by
    apply Finset.le_inf'
    intro i hi
    split_ifs
    · exact (ha.1 i).1
    · norm_num
  have hhi : hullHi a ≤ 1 := by
    apply Finset.sup'_le
    intro i hi
    split_ifs
    · exact (ha.1 i).2.2
    · norm_num
  obtain ⟨i, hi⟩ := ha.2
  have hl : hullLo a ≤ (a.2 i).1 := by
    have h := Finset.inf'_le (s := Finset.univ)
      (f := fun j => if (a.2 j).1 < (a.2 j).2 then (a.2 j).1 else 1)
      (Finset.mem_univ i)
    simpa only [hullLo, ite_eq_left hi] using h
  have hr : (a.2 i).2 ≤ hullHi a := by
    have h := Finset.le_sup' (s := Finset.univ)
      (f := fun j => if (a.2 j).1 < (a.2 j).2 then (a.2 j).2 else 0)
      (Finset.mem_univ i)
    simpa only [hullHi, ite_eq_left hi] using h
  exact ⟨hlo, le_trans hl (le_trans hi.le hr), hhi⟩

theorem hullLength_bounds (a : Material) (ha : MaterialValid a) :
    0 ≤ hullLength a ∧ hullLength a ≤ 1 := by
  obtain ⟨hlo, hmid, hhi⟩ := hull_bounds a ha
  simp only [hullLength, max_eq_right (sub_nonneg.mpr hmid)]
  constructor <;> linarith

noncomputable def recombinationRate (R : ℝ) (s : State) : ℝ :=
  (R / 2) * ∑ i, hullLength (s.2.2.2 i).2

theorem recombinationRate_bounds (R : ℝ) (hR : 0 ≤ R)
    (s : State) (hs : Valid s) :
    0 ≤ recombinationRate R s ∧
      recombinationRate R s ≤ R * (s.2.2.1 : ℝ) / 2 := by
  have hlen := fun i => hullLength_bounds (s.2.2.2 i).2 (hs.2.1 i)
  have hsum0 : 0 ≤ ∑ i, hullLength (s.2.2.2 i).2 :=
    Finset.sum_nonneg (fun i _ => (hlen i).1)
  have hsum1 : ∑ i, hullLength (s.2.2.2 i).2 ≤ (s.2.2.1 : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin s.2.2.1, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hlen i).2)
      _ = _ := by simp
  unfold recombinationRate
  constructor
  · positivity
  · nlinarith

theorem normalized_rate_le_hazard (R b : ℝ) (n : ℕ)
    (hR : 0 ≤ R) (hb0 : 0 ≤ b)
    (hb : b ≤ R * ((n : ℝ) + 2) / 2) :
    b / (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 + b) ≤ hazard R n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 + b := by positivity
  have hr : 0 < (n : ℝ) + 1 + R := by positivity
  unfold hazard
  apply (div_le_div_iff₀ hd hr).2
  have hm := mul_le_mul_of_nonneg_right hb (show 0 ≤ (n : ℝ) + 1 by positivity)
  nlinarith

end Rhone.Coalescent.SmcSupport
