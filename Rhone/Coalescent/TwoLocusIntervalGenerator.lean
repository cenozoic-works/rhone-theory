/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusIntervalCounts

/-!
# The generator of the interval sampler read at two probe positions

Source: griffiths1991_two_locus_graph, pp. 106–107. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open MeasureTheory ProbabilityTheory IntervalProcess MarkovChain.IntervalProcess SmcSupport

noncomputable def countGen (ρ : ℝ) (g : Counts → ℝ) (k : Counts) : ℝ :=
  ((k.1 : ℝ) * ((k.1 : ℝ) - 1) / 2 + (k.1 : ℝ) * (k.2.2 : ℝ)) *
      (g (k.1 - 1, k.2.1, k.2.2) - g k) +
    ((k.2.1 : ℝ) * ((k.2.1 : ℝ) - 1) / 2 + (k.2.1 : ℝ) * (k.2.2 : ℝ)) *
      (g (k.1, k.2.1 - 1, k.2.2) - g k) +
    (k.2.2 : ℝ) * ((k.2.2 : ℝ) - 1) / 2 * (g (k.1, k.2.1, k.2.2 - 1) - g k) +
    (k.1 : ℝ) * (k.2.1 : ℝ) * (g (k.1 - 1, k.2.1 - 1, k.2.2 + 1) - g k) +
    (k.2.2 : ℝ) * (ρ / 2) * (g (recCounts k) - g k)

theorem typeCounts_atTime (x y t : ℝ) (s : State) :
    typeCounts x y (atTime t s) = typeCounts x y s := rfl

theorem mergeCounts_comm (k : Counts) (t t' : Bool × Bool) :
    mergeCounts k t t' = mergeCounts k t' t := by
  obtain ⟨t1, t2⟩ := t
  obtain ⟨u1, u2⟩ := t'
  cases t1 <;> cases t2 <;> cases u1 <;> cases u2 <;>
    simp [mergeCounts, mergeType, typeVec]

theorem mergeCounts_none (k : Counts) (t : Bool × Bool) :
    mergeCounts k t (false, false) = k := by
  obtain ⟨t1, t2⟩ := t
  cases t1 <;> cases t2 <;> simp [mergeCounts, mergeType, typeVec]

theorem card_filter_carrierType (x y : ℝ) (s : State) (t : Bool × Bool) :
    ((Finset.univ.filter fun i : Fin s.2.2.1 => carrierType x y (s.2.2.2 i).2 = t).card) =
      typeCount x y t s := by
  classical
  unfold typeCount materialCount
  convert rfl

theorem totalRate_mul_eventKernel_sub_eq_countGen (R : ℝ) (hR : 0 ≤ R) (x y : ℝ)
    (hxy : x < y) (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) (g : Counts → ℝ)
    (hg : ∃ C, ∀ k, |g k| ≤ C) :
    (totalRate false R z.1 : ℝ) *
        (∫ w, g (typeCounts x y w.1) ∂eventKernel false R z - g (typeCounts x y z.1)) =
      countGen (R * (y - x)) g (typeCounts x y z.1) := by
  classical
  obtain ⟨C, hC⟩ := hg
  set ρ := R * (y - x) with hρdef
  set k := typeCounts x y z.1 with hk
  have htpos := unrestricted_totalRate_positive R z.1 hm
  have ht : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast htpos
  have hΦ : Measurable fun w : AugmentedState => g (typeCounts x y w.1) :=
    (measurable_of_countable g).comp ((typeCounts_measurable x y).comp measurable_fst)
  set U := unitUniform.prod unitUniform with hU
  let I : ActionIndex z.1 → ℝ := fun a =>
    ∫ v, g (typeCounts x y (argActionStep R z a v).1) ∂U
  have hbound : ∀ (μ : Measure AugmentedState) [IsFiniteMeasure μ],
      Integrable (fun w : AugmentedState => g (typeCounts x y w.1)) μ := fun μ _ =>
    Integrable.of_bound hΦ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hC _)
  have hmix : ∫ w, g (typeCounts x y w.1) ∂eventKernel false R z =
      ∑ a : ActionIndex z.1,
        (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) * I a := by
    rw [eventKernel_ARG_action_mixture R z (by omega), integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_smul_measure,
        integral_map (argActionStep_measurable R z a).aemeasurable hΦ.aestronglyMeasurable,
        ENNReal.toReal_ofReal (div_nonneg (NNReal.coe_nonneg _) ht.le), smul_eq_mul]
    · intro a _
      exact (hbound _).smul_measure ENNReal.ofReal_ne_top
  have hsumrate : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) =
      (totalRate false R z.1 : ℝ) := by
    simp [totalRate]
  set τ : Fin z.1.2.2.1 → Bool × Bool := fun i => carrierType x y (z.1.2.2.2 i).2 with hτ
  set Ψ : Bool × Bool → Bool × Bool → ℝ := fun t t' => g (mergeCounts k t t') - g k with hΨ
  have hΨsymm : ∀ t t', Ψ t t' = Ψ t' t := fun t t' => by
    simp only [hΨ, mergeCounts_comm k t t']
  have hpair : ∑ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
      (candidateRate false R z.1 (.inl p) : ℝ) * (I (.inl p) - g k) =
      ((k.1 : ℝ) * ((k.1 : ℝ) - 1) / 2 + (k.1 : ℝ) * (k.2.2 : ℝ)) *
          (g (k.1 - 1, k.2.1, k.2.2) - g k) +
        ((k.2.1 : ℝ) * ((k.2.1 : ℝ) - 1) / 2 + (k.2.1 : ℝ) * (k.2.2 : ℝ)) *
          (g (k.1, k.2.1 - 1, k.2.2) - g k) +
        (k.2.2 : ℝ) * ((k.2.2 : ℝ) - 1) / 2 * (g (k.1, k.2.1, k.2.2 - 1) - g k) +
        (k.1 : ℝ) * (k.2.1 : ℝ) * (g (k.1 - 1, k.2.1 - 1, k.2.2 + 1) - g k) := by
    have hterm : ∀ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inl p) : ℝ) * (I (.inl p) - g k) =
          if p.1.val < p.2.val then Ψ (τ p.1) (τ p.2) else 0 := by
      intro p
      rw [candidateRate_unrestricted_pair]
      by_cases hlt : p.1.val < p.2.val
      · rw [ite_eq_left hlt, ite_eq_left hlt, one_mul]
        have hconst : ∀ v, g (typeCounts x y (argActionStep R z (.inl p) v).1) =
            g (mergeCounts k (τ p.1) (τ p.2)) := by
          intro v
          change g (typeCounts x y (atTime _ (coalSuccessor z.1 p.1 p.2))) = _
          rw [typeCounts_atTime, typeCounts_coalSuccessor x y z.1 p.1 p.2 hlt]
        change ∫ v, g (typeCounts x y (argActionStep R z (.inl p) v).1) ∂U - g k = _
        rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const,
          probReal_univ, one_smul]
      · rw [ite_eq_right hlt, ite_eq_right hlt, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), sum_lt_pair_eq τ Ψ hΨsymm]
    simp only [hτ, card_filter_carrierType]
    have hA : typeCount x y (true, false) z.1 = k.1 := rfl
    have hB : typeCount x y (false, true) z.1 = k.2.1 := rfl
    have hC2 : typeCount x y (true, true) z.1 = k.2.2 := rfl
    have hnone : ∀ t, Ψ t (false, false) = 0 := fun t => by
      simp only [hΨ, mergeCounts_none, sub_self]
    have hnone' : ∀ t, Ψ (false, false) t = 0 := fun t => by
      rw [hΨsymm, hnone]
    have e1 : Ψ (true, false) (true, false) = g (k.1 - 1, k.2.1, k.2.2) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    have e2 : Ψ (false, true) (false, true) = g (k.1, k.2.1 - 1, k.2.2) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    have e3 : Ψ (true, true) (true, true) = g (k.1, k.2.1, k.2.2 - 1) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    have e4 : Ψ (true, false) (false, true) = g (k.1 - 1, k.2.1 - 1, k.2.2 + 1) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    have e5 : Ψ (true, false) (true, true) = g (k.1 - 1, k.2.1, k.2.2) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    have e6 : Ψ (false, true) (true, true) = g (k.1, k.2.1 - 1, k.2.2) - g k := by
      simp only [hΨ, mergeCounts, mergeType, typeVec]; norm_num
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, hA, hB, hC2, hnone, hnone',
      hΨsymm (false, true) (true, false), hΨsymm (true, true) (true, false),
      hΨsymm (true, true) (false, true), e1, e2, e3, e4, e5, e6]
    ring
  have hsnd : U.map Prod.snd = unitUniform := by
    rw [hU, Measure.map_snd_prod, measure_univ, one_smul]
  have hsplit : ∑ i : Fin z.1.2.2.1,
      (candidateRate false R z.1 (.inr i) : ℝ) * (I (.inr i) - g k) =
      (k.2.2 : ℝ) * (ρ / 2) * (g (recCounts k) - g k) := by
    set Δ := g (recCounts k) - g k with hΔ
    have hterm : ∀ i : Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inr i) : ℝ) * (I (.inr i) - g k) =
          (if τ i = (true, true) then 1 else 0) * ((ρ / 2) * Δ) := by
      intro i
      set lo := hullLo (z.1.2.2.2 i).2 with hlo
      set len := hullLength (z.1.2.2.2 i).2 with hlen
      have hstep : ∀ v : ℝ × ℝ, g (typeCounts x y (argActionStep R z (.inr i) v).1) =
          if τ i = (true, true) ∧ x < lo + len * v.2 ∧ lo + len * v.2 ≤ y then
            g (recCounts k) else g k := by
        intro v
        change g (typeCounts x y (atTime _ (splitSuccessor z.1 i (lo + len * v.2)))) = _
        rw [typeCounts_atTime, typeCounts_splitSuccessor x y hxy]
        split_ifs <;> rfl
      by_cases hb : τ i = (true, true)
      · rw [ite_eq_left hb, one_mul, candidateRate_split_eq false R hR]
        have hbx : materialContains (z.1.2.2.2 i).2 x := by
          have := congrArg Prod.fst hb
          simpa [hτ, carrierType] using this
        have hby : materialContains (z.1.2.2.2 i).2 y := by
          have := congrArg Prod.snd hb
          simpa [hτ, carrierType] using this
        have hlox : lo ≤ x := hullLo_le_of_materialContains _ _ hbx
        have hhiy : y < hullHi (z.1.2.2.2 i).2 := lt_hullHi_of_materialContains _ _ hby
        have hlenpos : 0 < len := by
          have : 0 < hullHi (z.1.2.2.2 i).2 - lo := by linarith
          rw [hlen, hullLength]
          exact lt_max_of_lt_right this
        have hleneq : len = hullHi (z.1.2.2.2 i).2 - lo := by
          rw [hlen, hullLength]
          exact max_eq_right (by linarith)
        set T : Set ℝ := {u : ℝ | x < lo + len * u ∧ lo + len * u ≤ y} with hT
        have hTm : MeasurableSet T := by
          rw [hT, affine_cut_set_eq lo len x y hlenpos]
          exact measurableSet_Ioc
        have hSm : MeasurableSet (Prod.snd ⁻¹' T : Set (ℝ × ℝ)) := hTm.preimage measurable_snd
        have hpt : ∀ v : ℝ × ℝ, g (typeCounts x y (argActionStep R z (.inr i) v).1) =
            g k + (Prod.snd ⁻¹' T : Set (ℝ × ℝ)).indicator (fun _ => Δ) v := by
          intro v
          rw [hstep v]
          by_cases hv : v.2 ∈ T
          · rw [Set.indicator_of_mem (show v ∈ Prod.snd ⁻¹' T from hv),
              ite_eq_left ⟨hb, hv⟩, hΔ]
            ring
          · rw [Set.indicator_of_notMem (show v ∉ Prod.snd ⁻¹' T from hv),
              ite_eq_right (fun h => hv h.2), add_zero]
        have hmass : U.real (Prod.snd ⁻¹' T) = (y - x) / len := by
          rw [measureReal_def, ← Measure.map_apply measurable_snd hTm, hsnd, ← measureReal_def]
          exact unitUniform_real_affine_cut lo len x y hlenpos hlox hxy.le (by linarith)
        have hI : I (.inr i) = g k + (y - x) / len * Δ := by
          change ∫ v, g (typeCounts x y (argActionStep R z (.inr i) v).1) ∂U = _
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
            integral_add (integrable_const _) ((integrable_const _).indicator hSm),
            integral_const, probReal_univ, one_smul, integral_indicator_const _ hSm, hmass,
            smul_eq_mul]
        rw [hI, hρdef]
        field_simp
        ring
      · rw [ite_eq_right hb, zero_mul]
        have hpt : ∀ v : ℝ × ℝ, g (typeCounts x y (argActionStep R z (.inr i) v).1) = g k :=
          fun v => by rw [hstep v, ite_eq_right (fun h => hb h.1)]
        have hI : I (.inr i) = g k := by
          change ∫ v, g (typeCounts x y (argActionStep R z (.inr i) v).1) ∂U = _
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const,
            probReal_univ, one_smul]
        rw [hI, sub_self, mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul]
    have hcount : (∑ i : Fin z.1.2.2.1, (if τ i = (true, true) then (1 : ℝ) else 0)) =
        (k.2.2 : ℝ) := by
      rw [Finset.sum_boole, card_filter_carrierType]
      rfl
    rw [hcount]
    ring
  have hkey : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) * (I a - g k) =
      countGen ρ g k := by
    rw [Fintype.sum_sum_type, hpair, hsplit, countGen]
  rw [hmix, ← hkey]
  have hexp : ∑ a : ActionIndex z.1,
      (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) * I a =
      (∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) * (I a - g k)) /
          (totalRate false R z.1 : ℝ) +
        g k * ((∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ)) /
          (totalRate false R z.1 : ℝ)) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hexp, hsumrate, div_self ht.ne', mul_one, add_sub_cancel_right]
  field_simp

theorem countGen_leave (ρ : ℝ) (k : Counts) :
    countGen ρ (fun j => if j = k then 0 else 1) k =
      ((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ) * (((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ) - 1) / 2 +
        (k.2.2 : ℝ) * (ρ / 2) := by
  obtain ⟨a, b, c⟩ := k
  have e1 : ((a : ℝ) * ((a : ℝ) - 1) / 2 + (a : ℝ) * (c : ℝ)) *
      (if ((a - 1, b, c) : Counts) = (a, b, c) then (0 : ℝ) else 1) =
      (a : ℝ) * ((a : ℝ) - 1) / 2 + (a : ℝ) * (c : ℝ) := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp
    · rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]
      ring
  have e2 : ((b : ℝ) * ((b : ℝ) - 1) / 2 + (b : ℝ) * (c : ℝ)) *
      (if ((a, b - 1, c) : Counts) = (a, b, c) then (0 : ℝ) else 1) =
      (b : ℝ) * ((b : ℝ) - 1) / 2 + (b : ℝ) * (c : ℝ) := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      simp
    · rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]
      ring
  have e3 : (c : ℝ) * ((c : ℝ) - 1) / 2 *
      (if ((a, b, c - 1) : Counts) = (a, b, c) then (0 : ℝ) else 1) =
      (c : ℝ) * ((c : ℝ) - 1) / 2 := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      simp
    · rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]
      ring
  have e4 : (a : ℝ) * (b : ℝ) *
      (if ((a - 1, b - 1, c + 1) : Counts) = (a, b, c) then (0 : ℝ) else 1) =
      (a : ℝ) * (b : ℝ) := by
    rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]
    ring
  have e5 : (c : ℝ) * (ρ / 2) *
      (if recCounts (a, b, c) = (a, b, c) then (0 : ℝ) else 1) = (c : ℝ) * (ρ / 2) := by
    rw [ite_eq_right (by simp only [recCounts, Prod.mk.injEq]; omega)]
    ring
  simp only [countGen, ite_true, sub_zero]
  rw [e1, e2, e3, e4, e5]
  push_cast
  ring

theorem totalRate_mul_eventKernel_class (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) (hxy : x < y)
    (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) (k' : Counts)
    (hk' : k' ≠ typeCounts x y z.1) :
    (totalRate false R z.1 : ℝ) *
        (eventKernel false R z).real {w | typeCounts x y w.1 = k'} =
      countGen (R * (y - x)) (fun j => if j = k' then 1 else 0) (typeCounts x y z.1) := by
  classical
  have h := totalRate_mul_eventKernel_sub_eq_countGen R hR x y hxy z hm
    (fun j => if j = k' then 1 else 0) ⟨1, fun j => by split_ifs <;> simp⟩
  rw [← h, ite_eq_right (Ne.symm hk'), sub_zero]
  congr 1
  have hS : MeasurableSet {w : AugmentedState | typeCounts x y w.1 = k'} :=
    (typeCounts_measurable x y).comp measurable_fst (measurableSet_singleton k')
  rw [← integral_indicator_one hS]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  by_cases hw : typeCounts x y w.1 = k'
  · simp [hw]
  · simp [hw]

theorem totalRate_mul_eventKernel_leave (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) (hxy : x < y)
    (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) :
    (totalRate false R z.1 : ℝ) *
        (eventKernel false R z).real {w | typeCounts x y w.1 ≠ typeCounts x y z.1} =
      let n : ℝ := ((typeCounts x y z.1).1 + (typeCounts x y z.1).2.1 +
        (typeCounts x y z.1).2.2 : ℕ)
      n * (n - 1) / 2 + ((typeCounts x y z.1).2.2 : ℝ) * (R * (y - x) / 2) := by
  classical
  set k := typeCounts x y z.1 with hk
  have h := totalRate_mul_eventKernel_sub_eq_countGen R hR x y hxy z hm
    (fun j => if j = k then 0 else 1) ⟨1, fun j => by split_ifs <;> simp⟩
  have hS : MeasurableSet {w : AugmentedState | typeCounts x y w.1 ≠ k} :=
    ((typeCounts_measurable x y).comp measurable_fst (measurableSet_singleton k)).compl
  have hint : ∫ w, (fun j => if j = k then (0 : ℝ) else 1) (typeCounts x y w.1)
      ∂eventKernel false R z = (eventKernel false R z).real {w | typeCounts x y w.1 ≠ k} := by
    rw [← integral_indicator_one hS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : typeCounts x y w.1 = k
    · simp [hw]
    · simp [hw]
  rw [hint, ite_eq_left rfl, sub_zero] at h
  rw [h, countGen_leave]

end Rhone.Coalescent.IntervalCounts
