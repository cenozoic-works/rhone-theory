/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.MullerRatchet
public import Rhone.Dynamics.HaighRecursion
public import Rhone.MarkovChain.MultinomialAllocation

/-!
# Class counts of Muller's ratchet and the link to Haigh's recursion

Source: haigh1978, pp. 251–267, sec. 2, eq. (2.1), (2.2). -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone.MarkovChain.MullerRatchet

open MeasureTheory ProbabilityTheory Finset Filter
open Dynamics.HaighRecursion
open scoped ENNReal NNReal

variable {N : ℕ}

def classCount (x : Fin N → ℕ) (k : ℕ) : ℕ := (univ.filter fun i => x i = k).card

noncomputable def relCount (x : Fin N → ℕ) (j : ℕ) : ℕ := classCount x (minLoad x + j)

noncomputable def classFreq (x : Fin N → ℕ) (k : ℕ) : ℝ := (classCount x k : ℝ) / N

noncomputable def classProb (s U : ℝ) (x : Fin N → ℕ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1),
    (classCount x j : ℝ) * (1 - s) ^ j / (∑ q, (1 - s) ^ x q) * poissonWeight U (k - j)

noncomputable def relMeanFitness (s : ℝ) (x : Fin N → ℕ) : ℝ :=
  (∑ q, (1 - s) ^ (x q - minLoad x)) / N

noncomputable def bestProb (s U : ℝ) (x : Fin N → ℕ) : ℝ :=
  (relCount x 0 : ℝ) * Real.exp (-U) / (N * relMeanFitness s x)

theorem classCount_of_lt_minLoad (x : Fin N → ℕ) {k : ℕ} (hk : k < minLoad x) :
    classCount x k = 0 := by
  rw [classCount, card_eq_zero, filter_eq_empty_iff]
  intro i _ hi
  have := minLoad_le x i
  omega

theorem relCount_zero_pos [NeZero N] (x : Fin N → ℕ) : 0 < relCount x 0 := by
  have : Nonempty (Fin N) := ⟨0⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
  rw [relCount, add_zero, classCount, card_pos]
  exact ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩

theorem sum_ite_le_eq_sum_classCount (x : Fin N → ℕ) (g : ℕ → ℝ) (k : ℕ) :
    ∑ p, (if x p ≤ k then g (x p) else 0) = ∑ j ∈ range (k + 1), (classCount x j : ℝ) * g j := by
  have h : ∀ j, (classCount x j : ℝ) * g j = ∑ p, if x p = j then g j else 0 := by
    intro j
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    rfl
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

theorem sum_classCount_mul_pow (s : ℝ) (x : Fin N → ℕ) {M : ℕ} (hM : ∀ q, x q ≤ M) :
    ∑ i ∈ range (M + 1), (classCount x i : ℝ) * (1 - s) ^ i = ∑ q, (1 - s) ^ x q := by
  rw [← sum_ite_le_eq_sum_classCount x (fun i => (1 - s) ^ i) M]
  exact sum_congr rfl fun q _ => ite_eq_left (hM q)

theorem classCount_le (x : Fin N → ℕ) (k : ℕ) : classCount x k ≤ N := by
  have h := card_filter_le (univ : Finset (Fin N)) fun i => x i = k
  rwa [card_univ, Fintype.card_fin] at h

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem classProb_nonneg {s U : ℝ} (hs : s < 1) (hU : 0 ≤ U) (x : Fin N → ℕ) (k : ℕ) :
    0 ≤ classProb s U x k := by
  have hpos : 0 < 1 - s := by linarith
  refine sum_nonneg fun j _ => mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg hpos.le _)) (sum_nonneg fun q _ => pow_nonneg hpos.le _))
    (poissonWeight_nonneg hU _)

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem offspringLaw_singleton [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (k : ℕ) : offspringLaw s U x {k} = ENNReal.ofReal (classProb s U x k) := by
  have hterm : ∀ p, ENNReal.ofReal (parentProb s x p) *
      poissonMeasure U ((fun i => x p + i) ⁻¹' {k}) =
      ENNReal.ofReal (if x p ≤ k then
        (1 - s) ^ x p / (∑ q, (1 - s) ^ x q) * poissonWeight U (k - x p) else 0) := by
    intro p
    split_ifs with h
    · have hpre : (fun i => x p + i) ⁻¹' {k} = {k - x p} := by
        ext i
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        omega
      rw [hpre, poissonMeasure_singleton, ← ENNReal.ofReal_mul (parentProb_nonneg hs x p)]
      rfl
    · have hpre : (fun i => x p + i) ⁻¹' {k} = ∅ := by
        ext i
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hpre, measure_empty, mul_zero, ENNReal.ofReal_zero]
  rw [offspringLaw_apply]
  simp only [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [sum_ite_le_eq_sum_classCount x
      (fun j => (1 - s) ^ j / (∑ q, (1 - s) ^ x q) * poissonWeight U (k - j)) k]
    refine sum_congr rfl fun j _ => ?_
    ring
  · intro p _
    split_ifs
    · exact mul_nonneg (parentProb_nonneg hs x p) (poissonWeight_nonneg U.coe_nonneg _)
    · exact le_rfl

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem stepLaw_singleton [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x y : Fin N → ℕ) :
    stepLaw s U x {y} = ∏ i, ENNReal.ofReal (classProb s U x (y i)) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  rw [stepLaw, Measure.pi_singleton]
  exact prod_congr rfl fun i _ => offspringLaw_singleton hs U x (y i)

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem classProb_le_one [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) (k : ℕ) :
    classProb s U x k ≤ 1 := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have h : offspringLaw s U x {k} ≤ 1 := prob_le_one
  rw [offspringLaw_singleton hs] at h
  exact ENNReal.ofReal_le_one.1 h

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_classFreq (s : ℝ) (x : Fin N → ℕ) :
    meanFitness s (classFreq x) = (∑ q, (1 - s) ^ x q) / N := by
  have hM : ∀ q, x q ≤ univ.sup x := fun q => le_sup (mem_univ q)
  have hzero : ∀ k ∉ range (univ.sup x + 1), classFreq x k * (1 - s) ^ k = 0 := by
    intro k hk
    have hk' : univ.sup x < k := by
      rw [mem_range] at hk
      omega
    have hc : classCount x k = 0 := by
      rw [classCount, card_eq_zero, filter_eq_empty_iff]
      intro i _ hi
      have := hM i
      omega
    simp [classFreq, hc]
  rw [meanFitness, tsum_eq_sum hzero, ← sum_classCount_mul_pow s x hM, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [classFreq]
  ring

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1), (2.2). -/
theorem classProb_eq_step [NeZero N] (s U : ℝ) (x : Fin N → ℕ) (k : ℕ) :
    classProb s U x k = step s U (classFreq x) k := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [classProb, step, meanFitness_classFreq]
  refine sum_congr rfl fun j _ => ?_
  rw [classFreq]
  congr 1
  rw [div_mul_eq_mul_div, div_div_div_cancel_right₀ hN]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1), (2.2). -/
theorem offspringLaw_singleton_eq_step [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0)
    (x : Fin N → ℕ) (k : ℕ) :
    offspringLaw s U x {k} = ENNReal.ofReal (step s U (classFreq x) k) := by
  rw [offspringLaw_singleton hs, classProb_eq_step]

theorem abs_classFreq_le_one (x : Fin N → ℕ) (k : ℕ) : |classFreq x k| ≤ 1 := by
  rw [classFreq, abs_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast classCount_le x k

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1), (2.2). -/
theorem integral_classFreq_stepLaw [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (k : ℕ) : ∫ y, classFreq y k ∂stepLaw s U x = step s U (classFreq x) k := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have := isProbabilityMeasure_stepLaw hs U x
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hfun : (fun y : Fin N → ℕ => classFreq y k) =
      fun y => (∑ t : Fin N,
        Set.indicator {y : Fin N → ℕ | y t = k} (fun _ => (1 : ℝ)) y) / N := by
    funext y
    rw [classFreq, classCount, card_filter]
    congr 1
    push_cast
    refine sum_congr rfl fun t _ => ?_
    by_cases h : y t = k <;> simp [h]
  have hmeas : ∀ t : Fin N, MeasurableSet {y : Fin N → ℕ | y t = k} := fun t =>
    (measurableSet_singleton k).preimage (measurable_pi_apply t)
  have hreal : ∀ t : Fin N, (stepLaw s U x).real {y : Fin N → ℕ | y t = k} =
      classProb s U x k := by
    intro t
    have hpre := (measurePreserving_eval (fun _ : Fin N => offspringLaw s U x) t).measure_preimage
      (measurableSet_singleton k).nullMeasurableSet
    have hset : {y : Fin N → ℕ | y t = k} =
        (Function.eval t : (Fin N → ℕ) → ℕ) ⁻¹' ({k} : Set ℕ) := rfl
    rw [measureReal_def, stepLaw, hset, hpre, offspringLaw_singleton hs,
      ENNReal.toReal_ofReal (classProb_nonneg hs U.coe_nonneg x k)]
  rw [hfun, integral_div, integral_finsetSum _ fun t _ =>
    (integrable_const (1 : ℝ)).indicator (hmeas t)]
  simp only [integral_indicator_const _ (hmeas _), hreal, smul_eq_mul, mul_one, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hN, classProb_eq_step]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1), (2.2). -/
theorem condExp_classFreq_succ [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (n k : ℕ) :
    ((process s hs U).pathLaw x)[fun ω => classFreq (ω (n + 1)) k | Filtration.piLE n]
      =ᵐ[(process s hs U).pathLaw x] fun ω => step s U (classFreq (ω n)) k := by
  have h := (process s hs U).condExp_eval_succ x n
    (Measurable.of_discrete (f := fun y : Fin N → ℕ => classFreq y k))
    (fun y => abs_classFreq_le_one y k)
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  exact integral_classFreq_stepLaw hs U (ω n) k

def classCell (K k : ℕ) : Fin (K + 2) := ⟨min k (K + 1), by omega⟩

theorem allocationCounts_classCell (K : ℕ) (y : Fin N → ℕ) (i : Fin (K + 1)) :
    (Rhone.MarkovChain.wfAlleleAllocationCounts N (K + 2) (fun t => classCell K (y t))).val
      i.castSucc = classCount y i := by
  rw [Rhone.MarkovChain.wfAlleleAllocationCounts_apply, classCount]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and, classCell, Fin.ext_iff, Fin.val_castSucc]
  have := i.isLt
  omega

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem stepLaw_classCounts_multinomial [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0)
    (x : Fin N → ℕ) (K : ℕ) (b : Rhone.MarkovChain.AlleleCounts N (K + 2)) :
    stepLaw s U x
        {y | Rhone.MarkovChain.wfAlleleAllocationCounts N (K + 2) (fun t => classCell K (y t)) = b} =
      (Nat.multinomial (univ : Finset (Fin (K + 2))) b.val : ℝ≥0∞) *
        ((∏ i : Fin (K + 1), ENNReal.ofReal (classProb s U x i) ^ b.val i.castSucc) *
          ENNReal.ofReal (1 - ∑ k ∈ range (K + 1), classProb s U x k) ^ b.val (Fin.last _)) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have hcell : ∀ i : Fin (K + 1), classCell K ⁻¹' {i.castSucc} = ({(i : ℕ)} : Set ℕ) := by
    intro i
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff, classCell, Fin.ext_iff,
      Fin.val_castSucc]
    have := i.isLt
    omega
  have hlast : classCell K ⁻¹' {Fin.last (K + 1)} = ((range (K + 1) : Finset ℕ) : Set ℕ)ᶜ := by
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff, classCell, Fin.ext_iff, Fin.val_last,
      Set.mem_compl_iff, mem_coe, mem_range]
    omega
  have hfin : offspringLaw s U x ((range (K + 1) : Finset ℕ) : Set ℕ) =
      ENNReal.ofReal (∑ k ∈ range (K + 1), classProb s U x k) := by
    rw [← sum_measure_singleton,
      ENNReal.ofReal_sum_of_nonneg fun k _ => classProb_nonneg hs U.coe_nonneg x k]
    exact sum_congr rfl fun k _ => offspringLaw_singleton hs U x k
  have hcompl : offspringLaw s U x (classCell K ⁻¹' {Fin.last (K + 1)}) =
      ENNReal.ofReal (1 - ∑ k ∈ range (K + 1), classProb s U x k) := by
    rw [hlast, prob_compl_eq_one_sub (Finset.measurableSet _), hfin,
      ENNReal.ofReal_sub _ (sum_nonneg fun k _ => classProb_nonneg hs U.coe_nonneg x k),
      ENNReal.ofReal_one]
  rw [stepLaw, Rhone.MarkovChain.pi_allocationCounts (offspringLaw s U x) N (K + 2)
    (Measurable.of_discrete (f := classCell K)) b, Fin.prod_univ_castSucc, hcompl]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  rw [hcell, offspringLaw_singleton hs]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem stepLaw_classCount [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (k j : ℕ) :
    stepLaw s U x {y | classCount y k = j} =
      ENNReal.ofReal ((N.choose j : ℝ) * classProb s U x k ^ j *
        (1 - classProb s U x k) ^ (N - j)) := by
  classical
  have := isProbabilityMeasure_offspringLaw hs U x
  have h0 := classProb_nonneg hs U.coe_nonneg x k
  have h1 : 0 ≤ 1 - classProb s U x k := sub_nonneg.2 (classProb_le_one hs U x k)
  have hset : {y : Fin N → ℕ | classCount y k = j} =
      {y | (univ.filter fun t => y t ∈ ({k} : Set ℕ)).card = j} := by
    ext y
    simp only [Set.mem_ofPred_eq, classCount, Set.mem_singleton_iff]
  rw [hset, stepLaw, Rhone.MarkovChain.pi_card_mem (offspringLaw s U x) N
      (measurableSet_singleton k) j,
    prob_compl_eq_one_sub (measurableSet_singleton k), offspringLaw_singleton hs,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0, ← ENNReal.ofReal_pow h0,
    ← ENNReal.ofReal_pow h1, ← ENNReal.ofReal_natCast (N.choose j),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _))]

theorem relMeanFitness_pos [NeZero N] {s : ℝ} (hs : s < 1) (x : Fin N → ℕ) :
    0 < relMeanFitness s x := by
  have hpos : 0 < 1 - s := by linarith
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  exact div_pos (sum_pos (fun q _ => pow_pos hpos _) ⟨0, mem_univ _⟩) hN

/-- Source: haigh1978, p. 254; etheridge_etal2007, sec. 2, eq. (2.3). -/
theorem classProb_minLoad [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ) (x : Fin N → ℕ) :
    classProb s U x (minLoad x) = bestProb s U x := by
  have hpos : 0 < 1 - s := by linarith
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hpow : ((1 - s) ^ minLoad x) ≠ 0 := (pow_pos hpos _).ne'
  have hD : ∑ q, (1 - s) ^ x q = (1 - s) ^ minLoad x * ∑ q, (1 - s) ^ (x q - minLoad x) := by
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    rw [← pow_add, Nat.add_sub_cancel' (minLoad_le x q)]
  have hsum : (∑ q, (1 - s) ^ (x q - minLoad x)) ≠ 0 :=
    (sum_pos (fun q _ => pow_pos hpos _) ⟨0, mem_univ _⟩).ne'
  rw [classProb, sum_eq_single (minLoad x)]
  · rw [Nat.sub_self, poissonWeight_zero, bestProb, relMeanFitness, relCount, add_zero, hD]
    field_simp
  · intro j hj hne
    have hlt : j < minLoad x := by
      rw [mem_range] at hj
      omega
    rw [classCount_of_lt_minLoad x hlt]
    simp
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_self _)) h

/-- Source: haigh1978, p. 254; etheridge_etal2007, sec. 2, eq. (2.3). -/
theorem stepLaw_classCount_minLoad [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (j : ℕ) :
    stepLaw s U x {y | classCount y (minLoad x) = j} =
      ENNReal.ofReal ((N.choose j : ℝ) * bestProb s U x ^ j *
        (1 - bestProb s U x) ^ (N - j)) := by
  rw [stepLaw_classCount hs, classProb_minLoad hs]

theorem offspringLaw_Ioi_minLoad [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    offspringLaw s U x (Set.Ioi (minLoad x)) = ENNReal.ofReal (1 - bestProb s U x) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have hnull : offspringLaw s U x (Set.Iio (minLoad x)) = 0 := by
    rw [offspringLaw_apply]
    refine sum_eq_zero fun p _ => ?_
    have hempty : (fun k => x p + k) ⁻¹' Set.Iio (minLoad x) = ∅ := by
      ext k
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      have := minLoad_le x p
      omega
    rw [hempty, measure_empty, mul_zero]
  have hle : offspringLaw s U x {minLoad x}ᶜ ≤ offspringLaw s U x (Set.Ioi (minLoad x)) := by
    have hsub : ({minLoad x}ᶜ : Set ℕ) ⊆ Set.Ioi (minLoad x) ∪ Set.Iio (minLoad x) := by
      intro k hk
      have hk' : k ≠ minLoad x := hk
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
      omega
    calc offspringLaw s U x {minLoad x}ᶜ
        ≤ offspringLaw s U x (Set.Ioi (minLoad x) ∪ Set.Iio (minLoad x)) := measure_mono hsub
      _ ≤ offspringLaw s U x (Set.Ioi (minLoad x)) + offspringLaw s U x (Set.Iio (minLoad x)) :=
          measure_union_le _ _
      _ = offspringLaw s U x (Set.Ioi (minLoad x)) := by rw [hnull, add_zero]
  have hge : offspringLaw s U x (Set.Ioi (minLoad x)) ≤ offspringLaw s U x {minLoad x}ᶜ :=
    measure_mono fun k hk => by
      have hk' : minLoad x < k := hk
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      omega
  rw [le_antisymm hge hle, prob_compl_eq_one_sub (measurableSet_singleton _),
    offspringLaw_singleton hs, classProb_minLoad hs,
    ENNReal.ofReal_sub _ (by
      rw [← classProb_minLoad hs]
      exact classProb_nonneg hs U.coe_nonneg x _), ENNReal.ofReal_one]

/-- Source: haigh1978, p. 254; etheridge_etal2007, sec. 2, eq. (2.3). -/
theorem stepLaw_click [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    stepLaw s U x {y | minLoad x < minLoad y} = ENNReal.ofReal ((1 - bestProb s U x) ^ N) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have hset : {y : Fin N → ℕ | minLoad x < minLoad y} =
      Set.pi Set.univ fun _ : Fin N => Set.Ioi (minLoad x) := by
    ext y
    simp [lt_minLoad_iff]
  have hnn : 0 ≤ 1 - bestProb s U x := by
    rw [← classProb_minLoad hs]
    exact sub_nonneg.2 (classProb_le_one hs U x _)
  rw [hset, stepLaw, Measure.pi_pi, prod_const, card_univ, Fintype.card_fin,
    offspringLaw_Ioi_minLoad hs, ENNReal.ofReal_pow hnn]

end Rhone.MarkovChain.MullerRatchet
