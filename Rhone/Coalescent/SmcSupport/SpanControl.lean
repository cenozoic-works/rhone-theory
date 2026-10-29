/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.MaterialSplit

/-! # Hull length decreases under accepted contact coalescences -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem hullLength_merge_le (a b : Material) (ha : MaterialValid a)
    (hb : MaterialValid b) (hc : touches a b) :
    hullLength (mergeMaterial a b) ≤ hullLength a + hullLength b := by
  have hla := (hullLo_lt_hullHi a ha).le
  have hlb := (hullLo_lt_hullHi b hb).le
  have hmerge : min (hullLo a) (hullLo b) ≤ max (hullHi a) (hullHi b) :=
    (min_le_left _ _).trans (hla.trans (le_max_left _ _))
  rw [hullLength, hullLo_merge, hullHi_merge, max_eq_right (sub_nonneg.mpr hmerge)]
  rw [hullLength, max_eq_right (sub_nonneg.mpr hla),
    hullLength, max_eq_right (sub_nonneg.mpr hlb)]
  rcases le_total (hullLo a) (hullLo b) with hab | hba
  · rw [min_eq_left hab]
    rcases le_total (hullHi a) (hullHi b) with hab' | hba'
    · rw [max_eq_right hab']; linarith [hc.2]
    · rw [max_eq_left hba']; linarith
  · rw [min_eq_right hba]
    rcases le_total (hullHi a) (hullHi b) with hab' | hba'
    · rw [max_eq_right hab']; linarith
    · rw [max_eq_left hba']; linarith [hc.1]

theorem hullLength_split_le (a : Material) (ha : MaterialValid a) (x : ℝ)
    (hlo : hullLo a < x) (hhi : x < hullHi a) :
    hullLength (splitMaterial a x).1 + hullLength (splitMaterial a x).2 ≤ hullLength a := by
  classical
  have hb := hull_bounds a ha
  have hx0 : 0 ≤ x := hb.1.trans hlo.le
  have hx1 : x ≤ 1 := hhi.le.trans hb.2.2
  have hc (i : Fin (a.1 + 1)) :
      max (a.2 i).1 (min (a.2 i).2 x) ≤ (a.2 i).2 :=
    max_le (ha.1 i).2.1 (min_le_left _ _)
  have hl : hullLo a ≤ hullLo (splitMaterial a x).1 := by
    apply Finset.le_inf'
    intro i _
    change hullLo a ≤ if (a.2 i).1 < max (a.2 i).1 (min (a.2 i).2 x)
      then (a.2 i).1 else 1
    split_ifs with hp
    · have ho : (a.2 i).1 < (a.2 i).2 := hp.trans_le (hc i)
      simpa only [ite_eq_left ho] using hullLo_le_atom a i
    · exact hb.2.1.trans hb.2.2
  have hlu : hullHi (splitMaterial a x).1 ≤ x := by
    apply Finset.sup'_le
    intro i _
    change (if (a.2 i).1 < max (a.2 i).1 (min (a.2 i).2 x)
      then max (a.2 i).1 (min (a.2 i).2 x) else 0) ≤ x
    split_ifs with hp
    · have hmin : (a.2 i).1 < min (a.2 i).2 x := by
        by_contra hn
        rw [max_eq_left (le_of_not_gt hn)] at hp
        exact lt_irrefl _ hp
      exact max_le (hmin.le.trans (min_le_right _ _)) (min_le_right _ _)
    · exact hx0
  have hrl : x ≤ hullLo (splitMaterial a x).2 := by
    apply Finset.le_inf'
    intro i _
    change x ≤ if max (a.2 i).1 (min (a.2 i).2 x) < (a.2 i).2
      then max (a.2 i).1 (min (a.2 i).2 x) else 1
    split_ifs with hp
    · have hx : x < (a.2 i).2 := by
        by_contra hn
        rw [min_eq_left (le_of_not_gt hn)] at hp
        exact (not_lt_of_ge (le_max_right _ _)) hp
      rw [min_eq_right hx.le]
      exact le_max_right _ _
    · exact hx1
  have hr : hullHi (splitMaterial a x).2 ≤ hullHi a := by
    apply Finset.sup'_le
    intro i _
    change (if max (a.2 i).1 (min (a.2 i).2 x) < (a.2 i).2
      then (a.2 i).2 else 0) ≤ hullHi a
    split_ifs with hp
    · have ho : (a.2 i).1 < (a.2 i).2 := (le_max_left _ _).trans_lt hp
      simpa only [ite_eq_left ho] using atom_le_hullHi a i
    · exact hb.1.trans hb.2.1
  have hv := splitMaterial_valid a ha x hlo hhi
  have hla := (hullLo_lt_hullHi a ha).le
  have hll := (hullLo_lt_hullHi _ hv.1).le
  have hrr := (hullLo_lt_hullHi _ hv.2).le
  simp only [hullLength, max_eq_right (sub_nonneg.mpr hll),
    max_eq_right (sub_nonneg.mpr hrr), max_eq_right (sub_nonneg.mpr hla)]
  linarith

end Rhone.Coalescent.SmcSupport
