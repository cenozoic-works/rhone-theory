/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingWitness
public import Rhone.Statistics.Identifiability.SilentMigrationClock

/-! # Explicit occupancy probabilities under a migration-only clock -/

@[expose] public section

noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def pairCollision (k : ℕ) (z : ℝ) : ℝ := (1 + (k + 1 : ℝ) * z^2) / (k + 2 : ℝ)

def tripleSame (k : ℕ) (z : ℝ) : ℝ :=
  (1 + 3 * (k + 1 : ℝ) * z^2 + (k : ℝ) * (k + 1 : ℝ) * z^3) / (k + 2 : ℝ)^2

def migrationRow (k : ℕ) (z : ℝ) : ThreeState → ℝ :=
  ![tripleSame k z, 3 * (pairCollision k z - tripleSame k z),
    1 - 3 * pairCollision k z + 2 * tripleSame k z]

lemma migrationRow_initial (k : ℕ) : migrationRow k 1 = Pi.single 0 1 := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  ext i
  fin_cases i <;> simp [migrationRow, pairCollision, tripleSame] <;>
    field_simp <;> ring

lemma migrationRow_sum (k : ℕ) (z : ℝ) : ∑ i, migrationRow k z i = 1 := by
  simp [migrationRow, Fin.sum_univ_succ]
  ring

lemma migrationRow_weight (k : ℕ) (z : ℝ) :
    (∑ i, migrationRow k z i * mergerWeight i) = 3 * pairCollision k z := by
  simp [migrationRow, mergerWeight, Fin.sum_univ_succ]
  ring

lemma tripleSame_sub_collision_sq (k : ℕ) (z : ℝ) :
    tripleSame k z - (pairCollision k z)^2 =
      (k + 1 : ℝ) * z^2 * (1 - z) * (1 + (k + 1 : ℝ) * z) / (k + 2 : ℝ)^2 := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  unfold tripleSame pairCollision
  field_simp
  ring

lemma tripleSame_sub_collision_sq_pos (k : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    0 < tripleSame k z - (pairCollision k z)^2 := by
  rw [tripleSame_sub_collision_sq]
  exact div_pos
    (mul_pos (mul_pos (mul_pos (by positivity) (sq_pos_of_pos hz)) (sub_pos.mpr hz1))
      (by positivity)) (sq_pos_of_pos (by positivity))

lemma pairCollision_derivative (k : ℕ) (z : ℝ → ℝ) {t q : ℝ}
    (hz : HasDerivAt z (-(k + 2 : ℝ) * q * z t) t) :
    HasDerivAt (fun u => pairCollision k (z u)) (-2 * (k + 1 : ℝ) * q * (z t)^2) t := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  have h := (((hz.pow 2).const_mul (k + 1 : ℝ)).const_add 1).div_const (k + 2 : ℝ)
  apply h.congr_deriv
  field_simp
  ring

lemma tripleSame_derivative (k : ℕ) (z : ℝ → ℝ) {t q : ℝ}
    (hz : HasDerivAt z (-(k + 2 : ℝ) * q * z t) t) :
    HasDerivAt (fun u => tripleSame k (z u))
      (-3 * (k + 1 : ℝ) * q * (2 * (z t)^2 + (k : ℝ) * (z t)^3) / (k + 2 : ℝ)) t := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  have h := ((((hz.pow 2).const_mul (3 * (k + 1 : ℝ))).const_add 1).add
    ((hz.pow 3).const_mul ((k : ℝ) * (k + 1 : ℝ)))).div_const ((k + 2 : ℝ)^2)
  apply h.congr_deriv
  field_simp
  ring

lemma migrationRow_hasDerivAt (k : ℕ) (z : ℝ → ℝ) {t q : ℝ}
    (hz : HasDerivAt z (-(k + 2 : ℝ) * q * z t) t) (i : ThreeState) :
    HasDerivAt (fun u => migrationRow k (z u) i)
      ((migrationRow k (z t) ᵥ* threeGenerator k 0 q) i) t := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  have hp := pairCollision_derivative k z hz
  have ha := tripleSame_derivative k z hz
  fin_cases i
  · change HasDerivAt (fun u => tripleSame k (z u)) _ t
    apply ha.congr_deriv
    norm_num [migrationRow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      threeGenerator, MarkovChain.Identifiability.totalMigration, pairCollision, tripleSame]
    field_simp
    ring
  · change HasDerivAt (fun u => 3 * (pairCollision k (z u) - tripleSame k (z u))) _ t
    apply ((hp.sub ha).const_mul 3).congr_deriv
    norm_num [migrationRow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      threeGenerator, MarkovChain.Identifiability.totalMigration, pairCollision, tripleSame]
    field_simp
    ring
  · change HasDerivAt (fun u => 1 - 3 * pairCollision k (z u) + 2 * tripleSame k (z u)) _ t
    apply (((hp.const_mul 3).const_sub 1).add (ha.const_mul 2)).congr_deriv
    norm_num [migrationRow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      threeGenerator, MarkovChain.Identifiability.totalMigration, pairCollision, tripleSame]
    field_simp
    ring

end Rhone.Statistics.Identifiability.ThreeTimeVarying
