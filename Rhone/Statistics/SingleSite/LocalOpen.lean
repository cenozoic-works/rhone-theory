/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SingleSite.Derivatives
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Local openness of the algebraic two-epoch candidate moment map -/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace Rhone.Statistics.SingleSite

def momentMap (k τ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (firstCoordinate k τ p.1 p.2, secondCoordinate k τ p.1 p.2)

lemma momentMap_contDiffAt {k : ℝ} (hk : 0 < k) (τ : ℝ) :
    ContDiffAt ℝ 1 (momentMap k τ) (1, 1) := by
  have h1 : (1 : ℝ) + k ≠ 0 := by positivity
  have h2 : 2 * (1 : ℝ) + k ≠ 0 := by positivity
  have hd : 2 * (1 : ℝ) + k / 2 ≠ 0 := by positivity
  unfold momentMap firstCoordinate secondCoordinate pairMoment tripleMoment
    crossFactor ePair eTriple
  fun_prop (disch := positivity)

lemma linear_map_of_columns (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (a b c d : ℝ) (h1 : L (1, 0) = (a, c)) (h2 : L (0, 1) = (b, d)) (p : ℝ × ℝ) :
    L p = (a * p.1 + b * p.2, c * p.1 + d * p.2) := by
  calc
    L p = L (p.1 • ((1, 0) : ℝ × ℝ) + p.2 • ((0, 1) : ℝ × ℝ)) := by congr 1; ext <;> simp
    _ = p.1 • L (1, 0) + p.2 • L (0, 1) := by rw [map_add, map_smul, map_smul]
    _ = _ := by rw [h1, h2]; ext <;> simp [mul_comm]

lemma momentMap_derivative {k : ℝ} (hk : 0 < k) (τ : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (momentMap k τ) (1, 1) p =
      (pairDerivative k * (1 - ePair k τ 1) * p.1 +
        pairDerivative k * ePair k τ 1 * p.2,
       (tripleDerivative k * (1 - eTriple k τ 1) -
         pairDerivative k * crossFactor k τ 1) * p.1 +
       (tripleDerivative k * eTriple k τ 1 +
         pairDerivative k * crossFactor k τ 1) * p.2) := by
  have hf := (momentMap_contDiffAt hk τ).differentiableAt (by norm_num)
  have hx : HasDerivAt (fun x : ℝ => momentMap k τ (x, 1))
      (fderiv ℝ (momentMap k τ) (1, 1) (1, 0)) 1 := by
    convert! hf.hasFDerivAt.comp_hasDerivAt (f := fun x : ℝ => (x, 1)) 1
      ((hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (1 : ℝ) (1 : ℝ))) using 1
  have hy : HasDerivAt (fun y : ℝ => momentMap k τ (1, y))
      (fderiv ℝ (momentMap k τ) (1, 1) (0, 1)) 1 := by
    convert! hf.hasFDerivAt.comp_hasDerivAt (f := fun y : ℝ => (1, y)) 1
      ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).prodMk (hasDerivAt_id (1 : ℝ))) using 1
  exact linear_map_of_columns _ _ _ _ _
    (hx.unique ((firstCoordinate_first_derivative hk τ).prodMk
      (secondCoordinate_first_derivative hk τ)))
    (hy.unique ((firstCoordinate_second_derivative hk τ).prodMk
      (secondCoordinate_second_derivative hk τ))) p

lemma momentMap_derivative_surjective {k τ : ℝ} (hk : 0 < k) (hτ : 0 < τ) :
    Function.Surjective (fderiv ℝ (momentMap k τ) (1, 1)) := by
  let a := pairDerivative k * (1 - ePair k τ 1)
  let b := pairDerivative k * ePair k τ 1
  let c := tripleDerivative k * (1 - eTriple k τ 1) -
    pairDerivative k * crossFactor k τ 1
  let d := tripleDerivative k * eTriple k τ 1 + pairDerivative k * crossFactor k τ 1
  have hdet : a * d - b * c ≠ 0 := (determinant_positive hk hτ).ne'
  intro y
  refine ⟨((d * y.1 - b * y.2) / (a * d - b * c),
    (a * y.2 - c * y.1) / (a * d - b * c)), ?_⟩
  rw [momentMap_derivative hk τ]
  change (a * ((d * y.1 - b * y.2) / (a * d - b * c)) +
      b * ((a * y.2 - c * y.1) / (a * d - b * c)),
    c * ((d * y.1 - b * y.2) / (a * d - b * c)) +
      d * ((a * y.2 - c * y.1) / (a * d - b * c))) = y
  apply Prod.ext
  · calc
      _ = (y.1 * (a * d - b * c)) / (a * d - b * c) := by ring
      _ = y.1 := by rw [mul_div_assoc, div_self hdet, mul_one]
  · calc
      _ = (y.2 * (a * d - b * c)) / (a * d - b * c) := by ring
      _ = y.2 := by rw [mul_div_assoc, div_self hdet, mul_one]

theorem positive_moment_image_mem_nhds {k τ : ℝ} (hk : 0 < k) (hτ : 0 < τ) :
    momentMap k τ '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} ∈
      𝓝 (momentMap k τ (1, 1)) := by
  have hc := momentMap_contDiffAt hk τ
  have hm := hc.hasStrictFDerivAt (by norm_num)
  have he := hm.map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr (momentMap_derivative_surjective hk hτ))
  rw [← he]
  apply Filter.image_mem_map
  exact IsOpen.mem_nhds
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)) (by norm_num)

end Rhone.Statistics.SingleSite
