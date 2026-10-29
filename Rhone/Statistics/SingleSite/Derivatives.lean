/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SingleSite.MomentMap

/-! # Checked coordinate derivatives of the algebraic candidate moment map -/

@[expose] public section

noncomputable section
open scoped Topology
namespace Rhone.Statistics.SingleSite

lemma pair_hasDerivAt {k : ℝ} (hk : 0 < k) :
    HasDerivAt (pairMoment k) (pairDerivative k) 1 := by
  have hd : (1 : ℝ) + k ≠ 0 := by positivity
  change HasDerivAt (fun x : ℝ => x / (x + k)) _ 1
  convert! (hasDerivAt_id (1 : ℝ)).div ((hasDerivAt_id (1 : ℝ)).add_const k) hd using 1
  unfold pairDerivative
  dsimp only [id]
  ring

lemma triple_factor (k x : ℝ) :
    tripleMoment k x = pairMoment k x * (2 * x / (2 * x + k)) := by
  unfold tripleMoment pairMoment
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma triple_hasDerivAt {k : ℝ} (hk : 0 < k) :
    HasDerivAt (tripleMoment k) (tripleDerivative k) 1 := by
  have hd : 2 * (1 : ℝ) + k ≠ 0 := by positivity
  have hg := ((hasDerivAt_id (1 : ℝ)).const_mul 2).div
    (((hasDerivAt_id (1 : ℝ)).const_mul 2).add_const k) hd
  have h := (pair_hasDerivAt hk).mul hg
  have hf : (fun x => pairMoment k x * (2 * x / (2 * x + k))) = tripleMoment k := by
    funext x
    exact (triple_factor k x).symm
  change HasDerivAt (fun x => pairMoment k x * (2 * x / (2 * x + k))) _ 1 at h
  rw [hf] at h
  convert! h using 1
  unfold tripleDerivative pairDerivative pairMoment
  dsimp only [id]
  simp only [Pi.div_apply]
  have h1 : 1 + k ≠ 0 := by positivity
  have h2 : 2 + k ≠ 0 := by positivity
  field_simp
  ring

lemma ePair_differentiable (k τ : ℝ) : Differentiable ℝ (ePair k τ) := by
  unfold ePair
  fun_prop

lemma eTriple_differentiable (k τ : ℝ) : Differentiable ℝ (eTriple k τ) := by
  unfold eTriple
  fun_prop

lemma crossFactor_differentiableAt {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    DifferentiableAt ℝ (crossFactor k τ) 1 := by
  have hd : 2 * (1 : ℝ) + k / 2 ≠ 0 := by positivity
  unfold crossFactor ePair eTriple
  fun_prop

lemma firstCoordinate_first_derivative {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    HasDerivAt (fun x => firstCoordinate k τ x 1)
      (pairDerivative k * (1 - ePair k τ 1)) 1 := by
  have da := pair_hasDerivAt hk
  have de := (ePair_differentiable k τ 1).hasDerivAt
  have h := da.add (de.mul ((hasDerivAt_const (1 : ℝ) (pairMoment k 1)).sub da))
  change HasDerivAt (fun x => pairMoment k x +
    ePair k τ x * (pairMoment k 1 - pairMoment k x)) _ 1
  convert! h using 1
  simp only [Pi.sub_apply, sub_self]
  ring

lemma firstCoordinate_second_derivative {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    HasDerivAt (fun y => firstCoordinate k τ 1 y)
      (pairDerivative k * ePair k τ 1) 1 := by
  have h := (((pair_hasDerivAt hk).sub_const (pairMoment k 1)).const_mul
    (ePair k τ 1)).const_add (pairMoment k 1)
  change HasDerivAt (fun y => pairMoment k 1 +
    ePair k τ 1 * (pairMoment k y - pairMoment k 1)) _ 1
  convert! h using 1
  ring

lemma secondCoordinate_first_derivative {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    HasDerivAt (fun x => secondCoordinate k τ x 1)
      (tripleDerivative k * (1 - eTriple k τ 1) -
        pairDerivative k * crossFactor k τ 1) 1 := by
  have da := pair_hasDerivAt hk
  have db := triple_hasDerivAt hk
  have de := (eTriple_differentiable k τ 1).hasDerivAt
  have dg := (crossFactor_differentiableAt hk τ).hasDerivAt
  have h := (db.add (de.mul ((hasDerivAt_const (1 : ℝ) (tripleMoment k 1)).sub db))).add
    (((hasDerivAt_const (1 : ℝ) (pairMoment k 1)).sub da).mul dg)
  change HasDerivAt (fun x => tripleMoment k x +
    eTriple k τ x * (tripleMoment k 1 - tripleMoment k x) +
    (pairMoment k 1 - pairMoment k x) * crossFactor k τ x) _ 1
  convert! h using 1
  simp only [Pi.sub_apply, sub_self]
  ring

lemma secondCoordinate_second_derivative {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    HasDerivAt (fun y => secondCoordinate k τ 1 y)
      (tripleDerivative k * eTriple k τ 1 +
        pairDerivative k * crossFactor k τ 1) 1 := by
  have h := ((((triple_hasDerivAt hk).sub_const (tripleMoment k 1)).const_mul
    (eTriple k τ 1)).const_add (tripleMoment k 1)).add
    (((pair_hasDerivAt hk).sub_const (pairMoment k 1)).mul_const (crossFactor k τ 1))
  change HasDerivAt (fun y => tripleMoment k 1 +
    eTriple k τ 1 * (tripleMoment k y - tripleMoment k 1) +
    (pairMoment k y - pairMoment k 1) * crossFactor k τ 1) _ 1
  convert! h using 1
  ring

end Rhone.Statistics.SingleSite
