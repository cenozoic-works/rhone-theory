/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.BlockExpectations

/-! # A reconstruction approach, not a recovered seven-site certificate -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.SevenSiteSeparator
open ThreeSiteSeparator ThreeTipSites SingleSiteChannel

abbrev Word := Fin 7 → Option (Fin 3)

noncomputable def wordFeature {K : ℕ} (w : Word) (x : Panel K 7) : ℝ :=
  ∏ i, (w i).elim 1 (fun e => uScore e (x i))

noncomputable def wordValue (w : Word) (A B : ℝ) (q : Fin 3) : ℝ :=
  ∏ i, (w i).elim 1 (fun e => pairMeans A B q e)

noncomputable def fixedSevenMean {K : ℕ} (π : Roots K 7) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f : Panel K 7 → ℝ) : ℝ := ∑ x, f x * fixedTopology π k t q x

theorem word_fixed_mean {K : ℕ} (hK : 2 ≤ K) (w : Word) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (wordFeature w) =
      wordValue w (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) q := by
  unfold fixedSevenMean wordFeature wordValue
  rw [fixedTopology_product_scores _ _ _ _
    (fun i y => (w i).elim 1 (fun e => uScore e y))]
  apply Finset.prod_congr rfl
  intro i _
  cases hwi : w i with
  | none =>
    simpa [uniformBlockRoots, hwi] using oriented_one_mean (by omega : 0 < K) k t q
  | some e =>
    simpa [uniformBlockRoots, hwi] using oriented_pair_mean hK k t q e

theorem fixed_seven_add {K : ℕ} (π : Roots K 7) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3)
    (f g : Panel K 7 → ℝ) :
    fixedSevenMean π k t q (fun x => f x + g x) =
      fixedSevenMean π k t q f + fixedSevenMean π k t q g := by
  simp only [fixedSevenMean, add_mul, Finset.sum_add_distrib]

theorem fixed_seven_div {K : ℕ} (π : Roots K 7) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3)
    (f : Panel K 7 → ℝ) (c : ℝ) :
    fixedSevenMean π k t q (fun x => f x / c) = fixedSevenMean π k t q f / c := by
  simp only [fixedSevenMean, div_eq_mul_inv, mul_right_comm, Finset.sum_mul]

def aWord (e : Fin 3) : Word := ![some e, some e, none, none, none, none, none]
def p2Word (e : Fin 3) : Word := ![some e, some e, some e, some e, none, none, none]
def p3Word (e : Fin 3) : Word := ![some e, some e, some e, some e, some e, some e, none]
def hWord (e : Fin 3) : Word := ![some 0, some 1, some 2, some e, some e, some e, some e]
def jWord (e f : Fin 3) : Word := ![some 0, some 1, some 2, some e, some e, some f, some f]

noncomputable def sevenFeatures {K : ℕ} : Fin 5 → Panel K 7 → ℝ :=
  ![fun x => (wordFeature (aWord 0) x + wordFeature (aWord 1) x + wordFeature (aWord 2) x) / 3,
    fun x => (wordFeature (p2Word 0) x + wordFeature (p2Word 1) x + wordFeature (p2Word 2) x) / 3,
    fun x => (wordFeature (p3Word 0) x + wordFeature (p3Word 1) x + wordFeature (p3Word 2) x) / 3,
    fun x => (wordFeature (hWord 0) x + wordFeature (hWord 1) x + wordFeature (hWord 2) x) / 3,
    fun x => (wordFeature (jWord 0 1) x + wordFeature (jWord 0 2) x + wordFeature (jWord 1 0) x +
      wordFeature (jWord 1 2) x + wordFeature (jWord 2 0) x + wordFeature (jWord 2 1) x) / 6]

noncomputable def sevenKernel (A B : ℝ) : Fin 5 → ℝ :=
  ![(A ^ 2 + 2 * B ^ 2) / 3, (A ^ 4 + 2 * B ^ 4) / 3, (A ^ 6 + 2 * B ^ 6) / 3,
    A * B ^ 2 * (A ^ 4 + 2 * B ^ 4) / 3,
    A * B ^ 2 * (2 * A ^ 2 * B ^ 2 + B ^ 4) / 3]

private theorem seven_fixed_0 {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures 0) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) 0 := by
  change fixedSevenMean _ _ _ _ (fun x =>
    (wordFeature (aWord 0) x + wordFeature (aWord 1) x + wordFeature (aWord 2) x) / 3) = _
  rw [fixed_seven_div]
  simp_rw [fixed_seven_add, word_fixed_mean hK]
  generalize Real.exp (-k * t.1) = A
  generalize Real.exp (-k * (t.1 + t.2)) = B
  simp only [wordValue, Fin.prod_univ_succ]
  dsimp [aWord, p2Word, p3Word, hWord, jWord, sevenKernel]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

private theorem seven_fixed_1 {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures 1) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) 1 := by
  change fixedSevenMean _ _ _ _ (fun x =>
    (wordFeature (p2Word 0) x + wordFeature (p2Word 1) x + wordFeature (p2Word 2) x) / 3) = _
  rw [fixed_seven_div]
  simp_rw [fixed_seven_add, word_fixed_mean hK]
  generalize Real.exp (-k * t.1) = A
  generalize Real.exp (-k * (t.1 + t.2)) = B
  simp only [wordValue, Fin.prod_univ_succ]
  dsimp [aWord, p2Word, p3Word, hWord, jWord, sevenKernel]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

private theorem seven_fixed_2 {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures 2) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) 2 := by
  change fixedSevenMean _ _ _ _ (fun x =>
    (wordFeature (p3Word 0) x + wordFeature (p3Word 1) x + wordFeature (p3Word 2) x) / 3) = _
  rw [fixed_seven_div]
  simp_rw [fixed_seven_add, word_fixed_mean hK]
  generalize Real.exp (-k * t.1) = A
  generalize Real.exp (-k * (t.1 + t.2)) = B
  simp only [wordValue, Fin.prod_univ_succ]
  dsimp [aWord, p2Word, p3Word, hWord, jWord, sevenKernel]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

private theorem seven_fixed_3 {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures 3) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) 3 := by
  change fixedSevenMean _ _ _ _ (fun x =>
    (wordFeature (hWord 0) x + wordFeature (hWord 1) x + wordFeature (hWord 2) x) / 3) = _
  rw [fixed_seven_div]
  simp_rw [fixed_seven_add, word_fixed_mean hK]
  generalize Real.exp (-k * t.1) = A
  generalize Real.exp (-k * (t.1 + t.2)) = B
  simp only [wordValue, Fin.prod_univ_succ]
  dsimp [aWord, p2Word, p3Word, hWord, jWord, sevenKernel]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

private theorem seven_fixed_4 {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures 4) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) 4 := by
  change fixedSevenMean _ _ _ _ (fun x =>
    (wordFeature (jWord 0 1) x +
      wordFeature (jWord 0 2) x +
      wordFeature (jWord 1 0) x +
      wordFeature (jWord 1 2) x +
      wordFeature (jWord 2 0) x +
      wordFeature (jWord 2 1) x) / 6) = _
  rw [fixed_seven_div]
  simp_rw [fixed_seven_add, word_fixed_mean hK]
  generalize Real.exp (-k * t.1) = A
  generalize Real.exp (-k * (t.1 + t.2)) = B
  simp only [wordValue, Fin.prod_univ_succ]
  dsimp [aWord, p2Word, p3Word, hWord, jWord, sevenKernel]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

theorem seven_fixed_mean {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3)
    (j : Fin 5) :
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures j) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) j := by
  fin_cases j
  · exact seven_fixed_0 hK k t q
  · exact seven_fixed_1 hK k t q
  · exact seven_fixed_2 hK k t q
  · exact seven_fixed_3 hK k t q
  · exact seven_fixed_4 hK k t q

end Rhone.Statistics.SevenSiteSeparator
