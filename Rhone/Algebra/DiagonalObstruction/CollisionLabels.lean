/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-! # Exact modular collisions of the zero-recombination diagonal entries -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

def coalDiag (m t : ℕ) : ℤ :=
  (2 * (m : ℤ) - t) * (2 * (m : ℤ) - t - 1)

theorem coalDiag_sub (m i j : ℕ) :
    coalDiag m i - coalDiag m j =
      ((j : ℤ) - i) * (4 * (m : ℤ) - i - j - 1) := by
  unfold coalDiag
  ring

theorem coalDiag_sub_pos {m i j : ℕ} (hm : 1 ≤ m)
    (hi : i ≤ m) (hj : j ≤ m) (hij : i < j) :
    0 < coalDiag m i - coalDiag m j := by
  rw [coalDiag_sub]
  have hmq : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hiq : (i : ℤ) ≤ m := by exact_mod_cast hi
  have hjq : (j : ℤ) ≤ m := by exact_mod_cast hj
  have hijq : (i : ℤ) < j := by exact_mod_cast hij
  exact mul_pos (by linarith) (by linarith)

theorem coalDiag_ne {m i j : ℕ} (hm : 1 ≤ m)
    (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) : coalDiag m i ≠ coalDiag m j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (sub_pos.mp (coalDiag_sub_pos hm hi hj h)).ne'
  · exact (sub_pos.mp (coalDiag_sub_pos hm hj hi h)).ne

theorem coalDiag_cast {R : Type*} [CommRing R] (m i : ℕ) :
    (coalDiag m i : R) = (2 * (m : R) - i) * (2 * (m : R) - i - 1) := by
  simp [coalDiag]

theorem coalDiag_collision_iff {p m i j : ℕ} [Fact p.Prime]
    (hp : m < p) (hi : i ≤ m) (hj : j ≤ m) :
    (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p) ↔
      i = j ∨ (4 * (m : ZMod p) - i - j - 1 = 0) := by
  have hij : (i : ZMod p) = (j : ZMod p) ↔ i = j := by
    rw [ZMod.natCast_eq_natCast_iff]
    change i % p = j % p ↔ i = j
    simp only [Nat.mod_eq_of_lt (hi.trans_lt hp), Nat.mod_eq_of_lt (hj.trans_lt hp)]
  have hsub : (coalDiag m i : ZMod p) - (coalDiag m j : ZMod p) =
      ((j : ZMod p) - i) * (4 * (m : ZMod p) - i - j - 1) := by
    simp only [coalDiag_cast]
    ring
  rw [← sub_eq_zero, hsub, mul_eq_zero, sub_eq_zero]
  simp only [eq_comm, hij]

theorem coalDiag_collision_pair {p m i j k : ℕ} [Fact p.Prime]
    (hp : m < p) (hi : i ≤ m) (hj : j ≤ m) (hk : k ≤ m)
    (hij : i ≠ j) (heq : (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p))
    (hkeq : (coalDiag m k : ZMod p) = (coalDiag m i : ZMod p)) :
    k = i ∨ k = j := by
  have hsum := (coalDiag_collision_iff hp hi hj).mp heq
  have hsum' := hsum.resolve_left hij
  rcases (coalDiag_collision_iff hp hi hk).mp hkeq.symm with hki | hki
  · exact Or.inl hki.symm
  · right
    have hcast : (k : ZMod p) = (j : ZMod p) := by linear_combination hsum' - hki
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    change k % p = j % p at hcast
    simpa only [Nat.mod_eq_of_lt (hk.trans_lt hp), Nat.mod_eq_of_lt (hj.trans_lt hp)]
      using hcast

theorem coalDiag_reflection {p m i j : ℕ}
    (hcenter : i + j + 2 * p + 1 = 4 * m) :
    (coalDiag m i : ZMod p) = (coalDiag m j : ZMod p) := by
  have hs : (4 * (m : ZMod p) - i - j - 1) = 0 := by
    have hz := congrArg (fun n : ℕ => (n : ZMod p)) hcenter
    push_cast at hz
    simp only [ZMod.natCast_self, mul_zero, add_zero] at hz
    linear_combination -hz
  apply sub_eq_zero.mp
  have hd := congrArg (fun z : ℤ => (z : ZMod p)) (coalDiag_sub m i j)
  push_cast at hd
  rw [hd, hs, mul_zero]

theorem coalDiag_reflection_dvd {p m i j : ℕ}
    (hcenter : i + j + 2 * p + 1 = 4 * m) :
    (p : ℤ) ∣ coalDiag m i - coalDiag m j := by
  have hgap : 4 * (m : ℤ) - i - j - 1 = 2 * p := by
    have hz : (i : ℤ) + j + 2 * p + 1 = 4 * m := by exact_mod_cast hcenter
    linarith
  rw [coalDiag_sub, hgap]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

end Rhone.Algebra.DiagonalObstruction
