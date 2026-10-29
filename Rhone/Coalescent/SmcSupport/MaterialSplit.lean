/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Material

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem hullLo_lt_hullHi (a : Material) (ha : MaterialValid a) : hullLo a < hullHi a := by
  obtain ⟨i, hi⟩ := ha.2
  have hl := hullLo_le_atom a i
  have hr := atom_le_hullHi a i
  rw [ite_eq_left hi] at hl hr
  exact hl.trans_lt (hi.trans_le hr)

theorem affine_cut_interior (a : Material) (ha : MaterialValid a)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    hullLo a < hullLo a + hullLength a * u ∧
      hullLo a + hullLength a * u < hullHi a := by
  have hw := sub_pos.mpr (hullLo_lt_hullHi a ha)
  have hp := mul_pos hw hu0
  have ht := mul_lt_mul_of_pos_left hu1 hw
  rw [hullLength, max_eq_right hw.le]
  constructor <;> nlinarith

theorem splitMaterial_valid (a : Material) (ha : MaterialValid a) (x : ℝ)
    (hlo : hullLo a < x) (hhi : x < hullHi a) :
    MaterialValid (splitMaterial a x).1 ∧ MaterialValid (splitMaterial a x).2 := by
  classical
  obtain ⟨hb0, _, hb1⟩ := hull_bounds a ha
  have hx0 : 0 < x := hb0.trans_lt hlo
  have hx1 : x < 1 := hhi.trans_le hb1
  have hc : ∀ i, (a.2 i).1 ≤ max (a.2 i).1 (min (a.2 i).2 x) ∧
      max (a.2 i).1 (min (a.2 i).2 x) ≤ (a.2 i).2 := by
    intro i
    exact ⟨le_max_left _ _, max_le (ha.1 i).2.1 (min_le_left _ _)⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun j : Fin (a.1 + 1) => if (a.2 j).1 < (a.2 j).2 then (a.2 j).1 else 1)
  change hullLo a = _ at hi
  have hil : (a.2 i).1 < (a.2 i).2 := by
    by_contra h
    rw [ite_eq_right h] at hi
    rw [hi] at hlo
    linarith
  have hix : (a.2 i).1 < x := by rw [ite_eq_left hil] at hi; rwa [hi] at hlo
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun k : Fin (a.1 + 1) => if (a.2 k).1 < (a.2 k).2 then (a.2 k).2 else 0)
  change hullHi a = _ at hj
  have hjr : (a.2 j).1 < (a.2 j).2 := by
    by_contra h
    rw [ite_eq_right h] at hj
    rw [hj] at hhi
    linarith
  have hxj : x < (a.2 j).2 := by rw [ite_eq_left hjr] at hj; rwa [hj] at hhi
  constructor
  · constructor
    · intro k
      exact ⟨(ha.1 k).1, (hc k).1, (hc k).2.trans (ha.1 k).2.2⟩
    · refine ⟨i, ?_⟩
      change (a.2 i).1 < max (a.2 i).1 (min (a.2 i).2 x)
      exact (lt_min hil hix).trans_le (le_max_right _ _)
  · constructor
    · intro k
      exact ⟨(ha.1 k).1.trans (hc k).1, (hc k).2, (ha.1 k).2.2⟩
    · refine ⟨j, ?_⟩
      change max (a.2 j).1 (min (a.2 j).2 x) < (a.2 j).2
      exact max_lt hjr ((min_le_right _ _).trans_lt hxj)

end Rhone.Coalescent.SmcSupport
