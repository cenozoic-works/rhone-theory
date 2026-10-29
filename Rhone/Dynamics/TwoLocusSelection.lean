/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.LDDecay
public import Rhone.Dynamics.MultiAlleleSelection
public import Mathlib.Tactic.NormNum

/-!
# Diploid two - locus viability selection followed by recombination

Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/

@[expose] public section
namespace Rhone.Dynamics.TwoLocusSelection

noncomputable def vector (g : Gametes ℝ) : Fin 4 → ℝ :=
  ![g.x11, g.x12, g.x21, g.x22]

noncomputable def fromVector (x : Fin 4 → ℝ) : Gametes ℝ :=
  ⟨x 0, x 1, x 2, x 3⟩

def sign : Fin 4 → ℝ := ![1,-1,-1,1]

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
noncomputable def step (W : Fin 4 → Fin 4 → ℝ) (r : ℝ)
    (g : Gametes ℝ) : Gametes ℝ := fromVector (fun i =>
  (vector g i * marginalFit W (vector g) i -
    sign i * r * W 0 3 * g.D) / multiMeanFit W (vector g))

noncomputable def selected (W : Fin 4 → Fin 4 → ℝ)
    (g : Gametes ℝ) : Gametes ℝ := fromVector (multiSelStep W (vector g))

noncomputable def witness : Gametes ℝ := ⟨1 / 2,0,0,1 / 2⟩

def witnessFitness : Fin 4 → Fin 4 → ℝ :=
  ![![0,0,0,1],![0,0,1,0],![0,1,0,0],![1,0,0,0]]

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem step_zero (W : Fin 4 → Fin 4 → ℝ) (g : Gametes ℝ) :
    step W 0 g = selected W g := by
  unfold step selected
  congr 1
  funext i
  simp [multiSelStep]

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem step_alleles (W : Fin 4 → Fin 4 → ℝ) (r : ℝ) (g : Gametes ℝ) :
    (step W r g).pA = (selected W g).pA ∧
    (step W r g).pB = (selected W g).pB := by
  simp only [Gametes.pA, Gametes.pB, step, selected, fromVector, multiSelStep,
    sign, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  constructor <;> ring

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem step_simplex (W : Fin 4 → Fin 4 → ℝ) (r : ℝ) (g : Gametes ℝ)
    (hg : ∀ i, 0 ≤ vector g i) (ht : g.total = 1)
    (hW : ∀ i j, 0 ≤ W i j) (hsym : ∀ i j, W i j = W j i)
    (hpos : W 0 3 = W 1 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (hmean : 0 < multiMeanFit W (vector g)) :
    (∀ i, 0 ≤ vector (step W r g) i) ∧ (step W r g).total = 1 := by
  have h00 := hg 0
  have h01 := hg 1
  have h02 := hg 2
  have h03 := hg 3
  simp only [vector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h00 h01 h02 h03
  have hr : 0 ≤ 1 - r := by linarith
  have hs10 := hsym 1 0
  have hs20 := hsym 2 0
  have hs30 := hsym 3 0
  have hs21 := hsym 2 1
  have hs31 := hsym 3 1
  have hs32 := hsym 3 2
  have hnum (i : Fin 4) : 0 ≤ vector g i * marginalFit W (vector g) i -
      sign i * r * W 0 3 * g.D := by
    fin_cases i <;>
      norm_num [vector, sign, marginalFit, Fin.sum_univ_four, Gametes.D]
    all_goals
      rw [hs10, hs20, hs30, hs21, hs31, hs32, ← hpos] at *
    all_goals
      nlinarith [mul_nonneg hr (mul_nonneg (hW 0 3) (mul_nonneg h00 h03)),
        mul_nonneg hr (mul_nonneg (hW 0 3) (mul_nonneg h01 h02)),
        mul_nonneg hr0 (mul_nonneg (hW 0 3) (mul_nonneg h00 h03)),
        mul_nonneg hr0 (mul_nonneg (hW 0 3) (mul_nonneg h01 h02)),
        mul_nonneg (hW 0 0) (sq_nonneg g.x11),
        mul_nonneg (hW 1 1) (sq_nonneg g.x12),
        mul_nonneg (hW 2 2) (sq_nonneg g.x21),
        mul_nonneg (hW 3 3) (sq_nonneg g.x22),
        mul_nonneg (hW 0 1) (mul_nonneg h00 h01),
        mul_nonneg (hW 0 2) (mul_nonneg h00 h02),
        mul_nonneg (hW 1 3) (mul_nonneg h01 h03),
        mul_nonneg (hW 2 3) (mul_nonneg h02 h03)]
  constructor
  · intro i
    fin_cases i
    · simpa [vector, step, fromVector, sign] using div_nonneg (hnum 0) hmean.le
    · simpa [vector, step, fromVector, sign] using div_nonneg (hnum 1) hmean.le
    · simpa [vector, step, fromVector, sign] using div_nonneg (hnum 2) hmean.le
    · simpa [vector, step, fromVector, sign] using div_nonneg (hnum 3) hmean.le
  · have hfreq : ∑ i, vector g i = 1 := by
      simpa [vector, Fin.sum_univ_four, Gametes.total, add_assoc] using ht
    have hsum := (multiSelStep_simplex W (vector g) hg hfreq hsym hW hmean).2
    simp only [Fin.sum_univ_four] at hsum
    simp only [Gametes.total, step, fromVector, sign, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    simp only [multiSelStep] at hsum
    convert hsum using 1
    ring

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem step_constant (r : ℝ) (g : Gametes ℝ) (ht : g.total = 1) :
    step (fun _ _ => 1) r g = g.recombine r := by
  have hm (i : Fin 4) : marginalFit (fun _ _ => 1) (vector g) i = 1 := by
    simpa [marginalFit, vector, Fin.sum_univ_four, Gametes.total, add_assoc] using ht
  have hw : multiMeanFit (fun _ _ => 1) (vector g) = 1 := by
    unfold multiMeanFit
    simp only [hm, mul_one]
    simpa [vector, Fin.sum_univ_four, Gametes.total] using ht
  have htotal : g.x22 = 1 - g.x11 - g.x12 - g.x21 := by
    unfold Gametes.total at ht
    linarith
  simp only [step, fromVector, hm, hw, div_one]
  cases g
  dsimp only at htotal
  simp only [vector, Fin.isValue, Matrix.cons_val_zero, mul_one, sign, one_mul,
    Gametes.D, Matrix.cons_val_one, neg_mul, sub_neg_eq_add, Matrix.cons_val,
    Gametes.recombine, Gametes.pA, Gametes.pB, Gametes.pB', Gametes.pA', Gametes.mk.injEq]
  constructor
  · rw [htotal]; ring
  constructor
  · rw [htotal]; ring
  constructor <;> rw [htotal] <;> ring

/-- Source: burger2013_migration_selection, sec. 7.2. -/
theorem witness_admissible :
    (∀ i, 0 ≤ vector witness i) ∧ witness.total = 1 ∧
    (∀ i j, 0 ≤ witnessFitness i j) ∧
    (∀ i j, witnessFitness i j = witnessFitness j i) ∧
    witnessFitness 0 3 = witnessFitness 1 2 ∧
    0 < multiMeanFit witnessFitness (vector witness) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [vector, witness]
  · norm_num [witness, Gametes.total]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [witnessFitness]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [witnessFitness]
  · norm_num [witnessFitness]
  · norm_num [multiMeanFit, marginalFit, witnessFitness, vector, witness, Fin.sum_univ_four]

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem witness_step : step witnessFitness (1 / 2) witness = ⟨1 / 4,1 / 4,1 / 4,1 / 4⟩ := by
  norm_num [step, fromVector, vector, witness, witnessFitness, sign,
    multiMeanFit, marginalFit, Gametes.D, Fin.sum_univ_four]

/-- Source: moran1964_adaptive_topographies, pp. 389–390; felsenstein_teg2019, p. 376. -/
theorem mean_fitness_decreases :
    multiMeanFit witnessFitness (vector (step witnessFitness (1 / 2) witness)) <
    multiMeanFit witnessFitness (vector witness) := by
  rw [witness_step]
  norm_num [multiMeanFit, marginalFit, witnessFitness, vector, witness, Fin.sum_univ_four]

end Rhone.Dynamics.TwoLocusSelection
