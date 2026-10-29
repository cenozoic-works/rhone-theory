/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Sfs
public import Rhone.Statistics.Watterson

/-! # Equality of executable infinite-sites formulas with existing specifications -/

@[expose] public section
namespace Rhone.Computation.Sfs
open Finset

theorem harmonic_eq (n : Nat) : harmonic n = _root_.harmonic n := by
  induction n with
  | zero => simp [harmonic, harmonic_zero]
  | succ n ih => simp [harmonic, harmonic_succ, ih, one_div]

theorem harmonic2_eq (n : Nat) :
    harmonic2 n = ∑ i ∈ Icc 1 n, (1 : Rat) / (i : Rat) ^ 2 := by
  induction n with
  | zero => simp [harmonic2]
  | succ n ih =>
    rw [harmonic2, ih, Finset.sum_Icc_succ_top (by omega)]

theorem a1_eq (n : Nat) : (coefficients n).a1 = Rhone.Statistics.tajimaA1 n := by
  simp [coefficients, Rhone.Statistics.tajimaA1, harmonic_eq]

theorem a2_eq (n : Nat) : (coefficients n).a2 = Rhone.Statistics.tajimaA2 n := by
  simp [coefficients, Rhone.Statistics.tajimaA2, harmonic2_eq]

theorem b1_eq (n : Nat) : (coefficients n).b1 = Rhone.Statistics.tajimaB1 n := by rfl

theorem b2_eq (n : Nat) : (coefficients n).b2 = Rhone.Statistics.tajimaB2 n := by rfl

theorem c1_eq (n : Nat) : (coefficients n).c1 = Rhone.Statistics.tajimaC1 n := by
  simp [coefficients, Rhone.Statistics.tajimaC1, Rhone.Statistics.tajimaB1,
    Rhone.Statistics.tajimaA1, harmonic_eq]

theorem c2_eq (n : Nat) : (coefficients n).c2 = Rhone.Statistics.tajimaC2 n := by
  simp [coefficients, Rhone.Statistics.tajimaC2, Rhone.Statistics.tajimaB2,
    Rhone.Statistics.tajimaA1, Rhone.Statistics.tajimaA2, harmonic_eq, harmonic2_eq]

theorem e1_eq (n : Nat) : (coefficients n).e1 = Rhone.Statistics.tajimaE1 n := by
  change (coefficients n).c1 / (coefficients n).a1 = _
  rw [c1_eq, a1_eq]
  rfl

theorem e2_eq (n : Nat) : (coefficients n).e2 = Rhone.Statistics.tajimaE2 n := by
  change (coefficients n).c2 / ((coefficients n).a1 ^ 2 + (coefficients n).a2) = _
  rw [c2_eq, a1_eq, a2_eq]
  rfl

theorem meanBin_eq (theta : Rat) {n i : Nat} (hi : 1 ≤ i) (hin : i < n) :
    meanBin theta i = Rhone.Statistics.expSfs theta n i := by
  exact (Rhone.Statistics.expSfs_eq theta hi hin).symm

theorem spectrum_size (n : Nat) (theta : Rat) : (spectrum n theta).size = n - 1 := by
  simp [spectrum]

theorem spectrum_getD_eq (theta : Rat) {n i : Nat} (hi : 1 ≤ i) (hin : i < n) :
    (spectrum n theta).getD (i - 1) 0 = Rhone.Statistics.expSfs theta n i := by
  have hb : i - 1 < n - 1 := by omega
  simp [spectrum, Array.getD, hb, List.getElem_toArray, List.getElem_map,
    List.getElem_range, show i - 1 + 1 = i by omega, meanBin_eq theta hi hin]

theorem meanSegregating_eq (n : Nat) (theta : Rat) :
    (moments n theta).meanSegregating = Rhone.Statistics.expSegSites theta n := by
  simp [moments, a1_eq, Rhone.Statistics.expSegSites_eq, Rhone.Statistics.tajimaA1]

theorem varianceSegregating_eq (n : Nat) (theta : Rat) :
    (moments n theta).varianceSegregating = Rhone.Statistics.varSegSites theta n := by
  simp [moments, a1_eq, a2_eq, Rhone.Statistics.varSegSites_eq]

theorem watterson_eq (n : Nat) (segregating : Rat) :
    watterson n segregating = Rhone.Statistics.wattersonEstimator n segregating := by
  simp [watterson, a1_eq, Rhone.Statistics.wattersonEstimator]

end Rhone.Computation.Sfs
