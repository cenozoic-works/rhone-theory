/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGWordHistory
public import Rhone.Coalescent.FiniteIntervalMaterialPairRates
public import Rhone.Coalescent.Kingman
public import Mathlib.Probability.UniformOn

/-! # One-step law of the unrestricted event kernel at zero recombination: Kingman marks -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
open scoped ENNReal

def kingmanPairSet (m : ℕ) : Set (ℕ × ℕ) := {ij | ij.1 < ij.2 ∧ ij.2 < m}

def eventPair (z : AugmentedState) : ℕ × ℕ :=
  Sum.elim (fun _ => (0, 0)) (Sum.elim id (fun _ => (0, 0))) z.2.2

def kingmanMark (z y : AugmentedState) : (ℕ × ℕ) × ℝ := (eventPair y, y.1.1 - z.1.1)

theorem eventPair_measurable : Measurable eventPair := by
  unfold eventPair
  exact (measurable_const.sumElim (measurable_id.sumElim measurable_const)).comp
    measurable_snd.snd

theorem kingmanMark_measurable : Measurable (fun p : AugmentedState × AugmentedState =>
    kingmanMark p.1 p.2) :=
  (eventPair_measurable.comp measurable_snd).prodMk
    (measurable_snd.fst.fst.sub measurable_fst.fst.fst)

theorem pairClock_shift_law (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ((volume.restrict (Set.Ioi s)).withDensity
      (fun t => ENNReal.ofReal (Real.exp (-r * (t - s))))).map (fun t => t - s) =
      ENNReal.ofReal r⁻¹ • expMeasure r := by
  have hd : (volume.restrict (Set.Ioi s)).withDensity
      (fun t => ENNReal.ofReal (r * Real.exp (-r * (t - s)))) =
      ENNReal.ofReal r • (volume.restrict (Set.Ioi s)).withDensity
        (fun t => ENNReal.ofReal (Real.exp (-r * (t - s)))) := by
    rw [← withDensity_smul _ (by fun_prop)]
    congr 1
    funext t
    simp [ENNReal.ofReal_mul hr.le]
  have h := inverseClock_shift_density r hr s
  rw [hd] at h
  have h2 : (volume.restrict (Set.Ioi s)).withDensity
      (fun t => ENNReal.ofReal (Real.exp (-r * (t - s)))) =
      ENNReal.ofReal r⁻¹ • unitUniform.map (fun u => s - Real.log u / r) := by
    rw [h, smul_smul, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hr.ne',
      ENNReal.ofReal_one, one_smul]
  rw [h2, Measure.map_smul, Measure.map_map (by fun_prop) (by fun_prop), ← inverseClock_law r hr]
  · congr 2
    funext u
    simp only [Function.comp_apply]
    ring
  · fun_prop

theorem argPairTransition_kingmanMark (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1)
    (i j : Fin z.1.2.2.1) :
    (argPairTransition 0 z i j).map (kingmanMark z) =
      ENNReal.ofReal (totalRate false 0 z.1 : ℝ)⁻¹ •
        (Measure.dirac (i.val, j.val)).prod (expMeasure (totalRate false 0 z.1 : ℝ)) := by
  have ht := unrestricted_totalRate_positive 0 z.1 hm
  have hq : 0 < (totalRate false 0 z.1 : ℝ) := by exact_mod_cast ht
  have hmk : Measurable (kingmanMark z) :=
    kingmanMark_measurable.comp (measurable_const.prodMk measurable_id)
  have hE : IsProbabilityMeasure (expMeasure (totalRate false 0 z.1 : ℝ)) :=
    isProbabilityMeasure_expMeasure hq
  have hg : Measurable (fun t : ℝ => ((atTime t (coalSuccessor z.1 i j),
      (t, .inr (.inl (i.val, j.val)))) : AugmentedState)) :=
    (measurable_id.prodMk measurable_const).prodMk (measurable_id.prodMk measurable_const)
  have hp : Measurable (fun t : ℝ => (((i.val, j.val), t) : (ℕ × ℕ) × ℝ)) :=
    measurable_const.prodMk measurable_id
  unfold argPairTransition
  rw [Measure.map_map hmk hg, Measure.dirac_prod, ← Measure.map_smul,
    ← pairClock_shift_law _ hq z.1.1, Measure.map_map hp (by fun_prop)]
  · rfl
  · exact hp.aemeasurable

theorem unrestricted_totalRate_zero_eq (s : State) :
    (totalRate false 0 s : ℝ) = (Rhone.Coalescent.coalRate s.2.2.1 : ℝ) := by
  rw [totalRate_eq]
  push_cast
  have h0 : splitRate 0 s = 0 := by
    unfold splitRate
    apply Finset.sum_eq_zero
    intro i _
    simp only [candidateRate, Real.toNNReal_zero, zero_div]
    exact zero_mul _
  rw [coalRate_unrestricted, h0]
  simp [Rhone.Coalescent.coalRate]

theorem pairDirac_sum_eq (m : ℕ) :
    (∑ i : Fin m, ∑ j : Fin m, if i.val < j.val then
      (Measure.dirac (i.val, j.val) : Measure (ℕ × ℕ)) else 0) =
      Measure.count.restrict (kingmanPairSet m) := by
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.restrict_apply (measurableSet_singleton q)]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  by_cases hq : q ∈ kingmanPairSet m
  · have hs : ({q} : Set (ℕ × ℕ)) ∩ kingmanPairSet m = {q} := by
      simpa using hq
    rw [hs, Measure.count_singleton]
    obtain ⟨h1, h2⟩ := hq
    rw [Finset.sum_eq_single (⟨q.1, by omega⟩ : Fin m), Finset.sum_eq_single (⟨q.2, h2⟩ : Fin m)]
    · simp [h1]
    · intro b _ hb
      split_ifs
      · have : (q.1, b.val) ≠ q := fun h => hb (Fin.ext (congrArg Prod.snd h))
        simp [this]
      · simp
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro c _
      split_ifs
      · have : (b.val, c.val) ≠ q := fun h => hb (Fin.ext (congrArg Prod.fst h))
        simp [this]
      · simp
    · simp
  · have hs : ({q} : Set (ℕ × ℕ)) ∩ kingmanPairSet m = ∅ := by
      simpa using hq
    rw [hs, measure_empty]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with hbc
    · have : (b.val, c.val) ≠ q := fun h => hq (h ▸ ⟨hbc, c.isLt⟩)
      simp [this]
    · simp

theorem eventKernel_kingmanMark_law (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) :
    (eventKernel false 0 z).map (kingmanMark z) =
      (uniformOn (kingmanPairSet z.1.2.2.1)).prod
        (expMeasure (Rhone.Coalescent.coalRate z.1.2.2.1 : ℝ)) := by
  classical
  have ht := unrestricted_totalRate_positive 0 z.1 hm
  have hq : 0 < (totalRate false 0 z.1 : ℝ) := by exact_mod_cast ht
  have hmk : Measurable (kingmanMark z) :=
    kingmanMark_measurable.comp (measurable_const.prodMk measurable_id)
  rw [← unrestricted_totalRate_zero_eq]
  set r : ℝ := (totalRate false 0 z.1 : ℝ) with hr
  have hE : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hq
  have hκ : IsProbabilityMeasure ((eventKernel false 0 z).map (kingmanMark z)) :=
    (Measure.isProbabilityMeasure_map_iff hmk.aemeasurable).mpr inferInstance
  have key : ∀ A : Set (ℕ × ℕ), ∀ B : Set ℝ, MeasurableSet A → MeasurableSet B →
      ((eventKernel false 0 z).map (kingmanMark z)) (A ×ˢ B) =
        Measure.count (kingmanPairSet z.1.2.2.1 ∩ A) * (ENNReal.ofReal r⁻¹ * expMeasure r B) := by
    intro A B hA hB
    have hpair : ∀ i j : Fin z.1.2.2.1,
        (if i.val < j.val then argPairTransition 0 z i j else 0) (kingmanMark z ⁻¹' (A ×ˢ B)) =
          (if i.val < j.val then (Measure.dirac (i.val, j.val) : Measure (ℕ × ℕ)) else 0) A *
            (ENNReal.ofReal r⁻¹ * expMeasure r B) := by
      intro i j
      split_ifs
      · rw [← Measure.map_apply hmk (hA.prod hB), argPairTransition_kingmanMark z hm,
          Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
        ring
      · simp
    rw [Measure.map_apply hmk (hA.prod hB), eventKernel_ARG_density 0 le_rfl z (by omega)]
    simp only [argSplitTransition_zero, Finset.sum_const_zero, add_zero,
      Measure.coe_finsetSum, Finset.sum_apply, hpair]
    simp only [← Finset.sum_mul]
    have hD := congrArg (fun μ : Measure (ℕ × ℕ) => μ A) (pairDirac_sum_eq z.1.2.2.1)
    simp only [Measure.coe_finsetSum, Finset.sum_apply] at hD
    rw [hD, Measure.restrict_apply hA, Set.inter_comm]
  have hone : Measure.count (kingmanPairSet z.1.2.2.1) * ENNReal.ofReal r⁻¹ = 1 := by
    have h := key Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    rw [Set.univ_prod_univ, measure_univ, Set.inter_univ, measure_univ, mul_one] at h
    exact h.symm
  have hc : ENNReal.ofReal r⁻¹ = (Measure.count (kingmanPairSet z.1.2.2.1))⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hone)
  symm
  apply Measure.prod_eq
  intro A B hA hB
  rw [key A B hA hB, hc, uniformOn, cond_apply MeasurableSet.of_discrete]
  ring

end Rhone.Coalescent.SmcPrime
