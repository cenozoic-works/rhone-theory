/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.CollisionLabels
public import Rhone.Algebra.DiagonalObstruction.CollisionSeries
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Int

/-! # Units of the localization of `ℤ` at a prime and no integral collision branch -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

abbrev PrimeIntegerLocal (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime (Ideal.span {(p : ℤ)})

theorem isUnit_intCast_primeIntegerLocal_iff (p : ℕ) [Fact p.Prime] (a : ℤ) :
    IsUnit (a : PrimeIntegerLocal p) ↔ ¬ (p : ℤ) ∣ a := by
  have h := IsLocalization.AtPrime.isUnit_to_map_iff
    (PrimeIntegerLocal p) (Ideal.span {(p : ℤ)}) a
  simpa only [eq_intCast, Ideal.mem_primeCompl_iff,
    Ideal.mem_span_singleton] using h

theorem isUnit_intCast_primeIntegerLocal_iff_zmod (p : ℕ) [Fact p.Prime] (a : ℤ) :
    IsUnit (a : PrimeIntegerLocal p) ↔ (a : ZMod p) ≠ 0 := by
  rw [isUnit_intCast_primeIntegerLocal_iff]
  exact (not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd a p)).symm

theorem intCast_primeIntegerLocal_ne_zero (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : a ≠ 0) : (a : PrimeIntegerLocal p) ≠ 0 := by
  have h := (FaithfulSMul.algebraMap_injective ℤ (PrimeIntegerLocal p)).ne
    (show a ≠ 0 from ha)
  simpa only [eq_intCast, map_zero] using h

theorem coalDiag_ne_of_labels_ne {m i j : ℕ} (hm : 1 ≤ m)
    (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) : coalDiag m i ≠ coalDiag m j := by
  apply sub_ne_zero.mp
  rw [coalDiag_sub]
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (by exact_mod_cast hij.symm)
  · have hmi : (i : ℤ) ≤ m := by exact_mod_cast hi
    have hmj : (j : ℤ) ≤ m := by exact_mod_cast hj
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    omega

theorem coalDiag_collision_gap_local {p m i j : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j)
    (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p)) :
    ((coalDiag m i - coalDiag m j : ℤ) : PrimeIntegerLocal p) ≠ 0 ∧
      ¬ IsUnit ((coalDiag m i - coalDiag m j : ℤ) : PrimeIntegerLocal p) := by
  constructor
  · exact intCast_primeIntegerLocal_ne_zero p
      (sub_ne_zero.mpr (coalDiag_ne_of_labels_ne hm hi hj hij))
  · rw [isUnit_intCast_primeIntegerLocal_iff_zmod]
    simpa only [Int.cast_sub, sub_eq_zero, not_not] using heq

theorem coalDiag_outside_gap_isUnit {p m i j k : ℕ} [Fact p.Prime]
    (hp : m < p) (hi : i ≤ m) (hj : j ≤ m) (hk : k ≤ m)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p)) :
    IsUnit ((coalDiag m i - coalDiag m k : ℤ) : PrimeIntegerLocal p) := by
  rw [isUnit_intCast_primeIntegerLocal_iff_zmod]
  simp only [Int.cast_sub, sub_ne_zero]
  intro h
  exact (coalDiag_collision_pair hp hi hj hk hij heq h.symm).elim hki hkj

theorem isUnit_natCast_primeIntegerLocal {p n : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : IsUnit (n : PrimeIntegerLocal p) := by
  have h := (isUnit_intCast_primeIntegerLocal_iff p (n : ℤ)).mpr
    (by exact_mod_cast Nat.not_dvd_of_pos_of_lt hn hnp)
  simpa only [Int.cast_natCast] using h

theorem characteristic_edges_isUnit {p m t : ℕ} [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p) (ht : t < m) :
    IsUnit (2 * ((m - t : ℕ) : PrimeIntegerLocal p) ^ 2) ∧
      IsUnit ((t + 1 : ℕ) : PrimeIntegerLocal p) := by
  constructor
  · exact (isUnit_natCast_primeIntegerLocal (p := p) (n := 2) (by omega) (by omega)).mul
      ((isUnit_natCast_primeIntegerLocal (p := p) (n := m - t) (by omega) (by omega)).pow 2)
  · exact isUnit_natCast_primeIntegerLocal (by omega) (by omega)

theorem no_integral_coal_collision_branch_of_lt {p m i j : ℕ} [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p) (hij : i < j) (hjm : j ≤ m)
    (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p))
    (z : PowerSeries (PrimeIntegerLocal p))
    (hz : PowerSeries.constantCoeff z = (coalDiag m i : PrimeIntegerLocal p)) :
    Rhone.LinearAlgebra.Tridiag.cont
      (spectralSeriesDiagonal
        (fun t => (coalDiag m t : PrimeIntegerLocal p))
        (fun t => -(t : PrimeIntegerLocal p)) z)
      (fun t => PowerSeries.C (2 * ((m : PrimeIntegerLocal p) - t) ^ 2))
      (fun t => PowerSeries.X * PowerSeries.C ((t : PrimeIntegerLocal p) + 1))
      (m + 1) ≠ 0 := by
  apply no_spectral_continuant_root_of_isolated_gap
    (fun t => (coalDiag m t : PrimeIntegerLocal p))
    (fun t => -(t : PrimeIntegerLocal p))
    (fun t => 2 * ((m : PrimeIntegerLocal p) - t) ^ 2)
    (fun t => ((t : PrimeIntegerLocal p) + 1)) z hij (by omega) hz
  · intro t htn hti
    have hdiff := coalDiag_ne_of_labels_ne (by omega : 1 ≤ m)
      (by omega : i ≤ m) (by omega : t ≤ m) hti.symm
    simpa only [Int.cast_sub] using
      intCast_primeIntegerLocal_ne_zero p (sub_ne_zero.mpr hdiff)
  · have hgap := (coalDiag_collision_gap_local (p := p) (by omega : 1 ≤ m)
      (by omega : i ≤ m) hjm (by omega : i ≠ j) heq).2
    simpa only [Int.cast_sub] using hgap
  · intro t htn hti htj
    simpa only [Int.cast_sub] using
      coalDiag_outside_gap_isUnit hp (by omega : i ≤ m) hjm (by omega : t ≤ m)
        (by omega : i ≠ j) hti htj heq
  · intro t ht
    have hti := Finset.mem_Ico.mp ht
    have htm : t < m := by omega
    simpa only [Nat.cast_sub (Nat.le_of_lt htm)] using
      (characteristic_edges_isUnit hm hp htm).1
  · intro t ht
    have hti := Finset.mem_Ico.mp ht
    simpa only [Nat.cast_add, Nat.cast_one] using
      (characteristic_edges_isUnit hm hp (by omega : t < m)).2

theorem no_integral_coal_collision_branch_of_gt {p m i j : ℕ} [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p) (hji : j < i) (him : i ≤ m)
    (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p))
    (z : PowerSeries (PrimeIntegerLocal p))
    (hz : PowerSeries.constantCoeff z = (coalDiag m i : PrimeIntegerLocal p)) :
    Rhone.LinearAlgebra.Tridiag.cont
      (spectralSeriesDiagonal
        (fun t => (coalDiag m t : PrimeIntegerLocal p))
        (fun t => -(t : PrimeIntegerLocal p)) z)
      (fun t => PowerSeries.C (2 * ((m : PrimeIntegerLocal p) - t) ^ 2))
      (fun t => PowerSeries.X * PowerSeries.C ((t : PrimeIntegerLocal p) + 1))
      (m + 1) ≠ 0 := by
  apply no_spectral_continuant_root_of_isolated_gap_right
    (fun t => (coalDiag m t : PrimeIntegerLocal p))
    (fun t => -(t : PrimeIntegerLocal p))
    (fun t => 2 * ((m : PrimeIntegerLocal p) - t) ^ 2)
    (fun t => ((t : PrimeIntegerLocal p) + 1)) z hji (by omega) hz
  · intro t htn hti
    have hdiff := coalDiag_ne_of_labels_ne (by omega : 1 ≤ m)
      him (by omega : t ≤ m) hti.symm
    simpa only [Int.cast_sub] using
      intCast_primeIntegerLocal_ne_zero p (sub_ne_zero.mpr hdiff)
  · have hgap := (coalDiag_collision_gap_local (p := p) (by omega : 1 ≤ m)
      him (by omega : j ≤ m) (by omega : i ≠ j) heq).2
    simpa only [Int.cast_sub] using hgap
  · intro t htn htj hti
    simpa only [Int.cast_sub] using
      coalDiag_outside_gap_isUnit hp him (by omega : j ≤ m) (by omega : t ≤ m)
        (by omega : i ≠ j) hti htj heq
  · intro t ht
    have hti := Finset.mem_Ico.mp ht
    have htm : t < m := by omega
    simpa only [Nat.cast_sub (Nat.le_of_lt htm)] using
      (characteristic_edges_isUnit hm hp htm).1
  · intro t ht
    have hti := Finset.mem_Ico.mp ht
    simpa only [Nat.cast_add, Nat.cast_one] using
      (characteristic_edges_isUnit hm hp (by omega : t < m)).2

theorem no_integral_coal_collision_branch {p m i j : ℕ} [Fact p.Prime]
    (hm : 2 ≤ m) (hp : m < p) (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j)
    (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p))
    (z : PowerSeries (PrimeIntegerLocal p))
    (hz : PowerSeries.constantCoeff z = (coalDiag m i : PrimeIntegerLocal p)) :
    Rhone.LinearAlgebra.Tridiag.cont
      (spectralSeriesDiagonal
        (fun t => (coalDiag m t : PrimeIntegerLocal p))
        (fun t => -(t : PrimeIntegerLocal p)) z)
      (fun t => PowerSeries.C (2 * ((m : PrimeIntegerLocal p) - t) ^ 2))
      (fun t => PowerSeries.X * PowerSeries.C ((t : PrimeIntegerLocal p) + 1))
      (m + 1) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact no_integral_coal_collision_branch_of_lt hm hp hlt hj heq z hz
  · exact no_integral_coal_collision_branch_of_gt hm hp hgt hi heq z hz

end Rhone.Algebra.DiagonalObstruction
