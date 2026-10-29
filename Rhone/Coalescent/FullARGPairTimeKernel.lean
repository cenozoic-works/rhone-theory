/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSampleKernel
public import Rhone.Coalescent.FullARGTerminationDrift
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # One-step expectations of the first and second moments of the pair coalescence time -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem integral_log_sq_Ioc :
    IntegrableOn (fun v : ℝ => Real.log v ^ 2) (Set.Ioc 0 1) volume ∧
      ∫ v in Set.Ioc (0 : ℝ) 1, Real.log v ^ 2 = 2 := by
  let F : ℝ → ℝ := fun x => x * Real.log x ^ 2 - 2 * (x * Real.log x) + 2 * x
  have hcont : ContinuousOn F (Set.Icc 0 1) := by
    have h1 : Continuous fun x : ℝ => 4 * (Real.sqrt x * Real.log (Real.sqrt x)) ^ 2 :=
      continuous_const.mul ((Real.continuous_mul_log.comp Real.continuous_sqrt).pow 2)
    have h2 : ContinuousOn (fun x : ℝ => x * Real.log x ^ 2) (Set.Icc 0 1) := by
      refine h1.continuousOn.congr fun x hx => ?_
      change x * Real.log x ^ 2 = 4 * (Real.sqrt x * Real.log (Real.sqrt x)) ^ 2
      rw [Real.log_sqrt hx.1, mul_pow, Real.sq_sqrt hx.1]
      ring
    exact (h2.sub (continuous_const.mul Real.continuous_mul_log).continuousOn).add
      (continuous_const.mul continuous_id).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (Real.log x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hl := Real.hasDerivAt_log hx0
    have h : HasDerivAt F _ x :=
      (((hasDerivAt_id' x).mul (hl.pow 2)).sub (((hasDerivAt_id' x).mul hl).const_mul 2)).add
        ((hasDerivAt_id' x).const_mul 2)
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    ring
  have hint : IntegrableOn (fun v : ℝ => Real.log v ^ 2) (Set.Ioc 0 1) volume :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv fun _ _ => sq_nonneg _
  refine ⟨hint, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint)]
  simp [F]

theorem lintegral_log_sq_unitUniform :
    ∫⁻ v, ENNReal.ofReal (Real.log v ^ 2) ∂unitUniform = 2 := by
  obtain ⟨hI, hval⟩ := integral_log_sq_Ioc
  rw [unitUniform, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun v => sq_nonneg _), hval]
  simp

theorem unitUniform_ae_mem : ∀ᵐ u ∂unitUniform, u ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold unitUniform
  exact ae_restrict_mem measurableSet_Ioo

theorem lintegral_clockTime_unitUniform (t lam : ℝ) (ht : 0 ≤ t) (hlam : 0 < lam) :
    ∫⁻ u, ENNReal.ofReal (t - Real.log u / lam) ∂unitUniform =
      ENNReal.ofReal (t + 1 / lam) := by
  have hpt : ∀ᵐ u ∂unitUniform, ENNReal.ofReal (t - Real.log u / lam) =
      ENNReal.ofReal t + ENNReal.ofReal (1 / lam) * ENNReal.ofReal (-Real.log u) := by
    filter_upwards [unitUniform_ae_mem] with u hu
    have hlog : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add ht (by positivity)]
    congr 1
    ring
  have m1 : Measurable fun u : ℝ => ENNReal.ofReal (-Real.log u) :=
    ENNReal.measurable_ofReal.comp Real.measurable_log.neg
  rw [lintegral_congr_ae hpt, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ m1,
    lintegral_neg_log_unitUniform, mul_one, ← ENNReal.ofReal_add ht (by positivity)]

theorem lintegral_clockTime_sq_unitUniform (t lam : ℝ) (ht : 0 ≤ t) (hlam : 0 < lam) :
    ∫⁻ u, ENNReal.ofReal (t - Real.log u / lam) ^ 2 ∂unitUniform =
      ENNReal.ofReal (t ^ 2 + 2 * t / lam + 2 / lam ^ 2) := by
  have hpt : ∀ᵐ u ∂unitUniform, ENNReal.ofReal (t - Real.log u / lam) ^ 2 =
      ENNReal.ofReal (t ^ 2) + ENNReal.ofReal (2 * t / lam) * ENNReal.ofReal (-Real.log u) +
        ENNReal.ofReal (1 / lam ^ 2) * ENNReal.ofReal (Real.log u ^ 2) := by
    filter_upwards [unitUniform_ae_mem] with u hu
    have hlog : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
    have hs : 0 ≤ t - Real.log u / lam := by
      have : 0 ≤ -Real.log u / lam := div_nonneg hlog hlam.le
      have e : t - Real.log u / lam = t + -Real.log u / lam := by ring
      rw [e]
      exact add_nonneg ht this
    rw [← ENNReal.ofReal_pow hs, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have m1 : Measurable fun u : ℝ => ENNReal.ofReal (-Real.log u) :=
    ENNReal.measurable_ofReal.comp Real.measurable_log.neg
  have m2 : Measurable fun u : ℝ => ENNReal.ofReal (Real.log u ^ 2) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_log.pow_const 2)
  rw [lintegral_congr_ae hpt, lintegral_add_right _ (m2.const_mul _),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ m1, lintegral_const_mul _ m2, lintegral_neg_log_unitUniform,
    lintegral_log_sq_unitUniform, mul_one,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp

theorem one_le_unrestricted_totalRate (R : ℝ) (s : State) (hm : 2 ≤ s.2.2.1) :
    (1 : ℝ) ≤ (totalRate false R s : ℝ) := by
  classical
  let i : Fin s.2.2.1 := ⟨0, by omega⟩
  let j : Fin s.2.2.1 := ⟨1, by omega⟩
  have hc : candidateRate false R s (.inl (i, j)) = 1 := by
    simp [candidateRate, i, j]
  have hle : candidateRate false R s (.inl (i, j)) ≤ totalRate false R s :=
    Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ _)
  rw [hc] at hle
  exact_mod_cast hle

theorem exists_carrier_pair (q : ℝ) (s : State) (h : carrierCount q s = 2) :
    ∃ i j : Fin s.2.2.1, i.val < j.val ∧
      ∀ k, materialContains (s.2.2.2 k).2 q ↔ (k = i ∨ k = j) := by
  classical
  unfold carrierCount materialCount at h
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp h
  have key : ∀ k, materialContains (s.2.2.2 k).2 q ↔ (k = a ∨ k = b) := by
    intro k
    have := Finset.ext_iff.mp hset k
    simpa using this
  rcases Nat.lt_or_gt_of_ne (fun e => hab (Fin.ext e)) with hlt | hgt
  · exact ⟨a, b, hlt, key⟩
  · exact ⟨b, a, hgt, fun k => (key k).trans or_comm⟩

theorem eventKernel_lintegral_time_carrier (R q : ℝ) (z : AugmentedState)
    (hz : carrierCount q z.1 = 2) {φ : ℝ → ℕ → ℝ≥0∞}
    (hφ : Measurable fun p : ℝ × ℕ => φ p.1 p.2) :
    ∫⁻ w, φ w.1.1 (carrierCount q w.1) ∂eventKernel false R z =
      ENNReal.ofReal (1 / (totalRate false R z.1 : ℝ)) *
          ∫⁻ u, φ (z.1.1 - Real.log u / (totalRate false R z.1 : ℝ)) 1 ∂unitUniform +
        ENNReal.ofReal (((totalRate false R z.1 : ℝ) - 1) / (totalRate false R z.1 : ℝ)) *
          ∫⁻ u, φ (z.1.1 - Real.log u / (totalRate false R z.1 : ℝ)) 2 ∂unitUniform := by
  classical
  have hm : 2 ≤ z.1.2.2.1 := by
    have h1 := materialCount_le (fun a => materialContains a q) z.1
    unfold carrierCount at hz
    omega
  have ht : 0 < (totalRate false R z.1 : ℝ) := by
    exact_mod_cast unrestricted_totalRate_positive R z.1 hm
  set lam := (totalRate false R z.1 : ℝ) with hlam
  obtain ⟨i0, j0, hij0, hcar⟩ := exists_carrier_pair q z.1 hz
  have hF : Measurable fun w : AugmentedState => φ w.1.1 (carrierCount q w.1) :=
    hφ.comp (measurable_fst.fst.prodMk ((carrierCount_measurable q).comp measurable_fst))
  let I : ℕ → ℝ≥0∞ := fun c => ∫⁻ u, φ (z.1.1 - Real.log u / lam) c ∂unitUniform
  let cnt : ActionIndex z.1 → ℕ := fun a =>
    match a with
    | .inl p => carrierCount q (coalSuccessor z.1 p.1 p.2)
    | .inr _ => 2
  have hfst : (unitUniform.prod unitUniform).map Prod.fst = unitUniform := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hact : ∀ a : ActionIndex z.1,
      ∫⁻ v, φ (argActionStep R z a v).1.1 (carrierCount q (argActionStep R z a v).1)
        ∂(unitUniform.prod unitUniform) = I (cnt a) := by
    intro a
    have hmeasI : Measurable fun u : ℝ => φ (z.1.1 - Real.log u / lam) (cnt a) :=
      hφ.comp ((measurable_const.sub (Real.measurable_log.div_const _)).prodMk
        measurable_const)
    have hpt : ∀ v : ℝ × ℝ,
        φ (argActionStep R z a v).1.1 (carrierCount q (argActionStep R z a v).1) =
          φ (z.1.1 - Real.log v.1 / lam) (cnt a) := by
      intro v
      cases a with
      | inl p => rfl
      | inr i =>
        have e : carrierCount q (argActionStep R z (.inr i) v).1 =
            carrierCount q (splitSuccessor z.1 i
              (hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2)) := rfl
        rw [e, carrierCount_splitSuccessor, hz]
        rfl
    rw [lintegral_congr hpt]
    have hmap := lintegral_map (μ := unitUniform.prod unitUniform) hmeasI measurable_fst
    rw [hfst] at hmap
    exact hmap.symm
  have hterm : ∀ a : ActionIndex z.1,
      ∫⁻ w, φ w.1.1 (carrierCount q w.1)
        ∂(ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) / lam) •
          (unitUniform.prod unitUniform).map (argActionStep R z a)) =
        ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) / lam) * I (cnt a) := by
    intro a
    rw [lintegral_smul_measure, lintegral_map hF (argActionStep_measurable R z a), hact a,
      smul_eq_mul]
  rw [eventKernel_ARG_action_mixture R z hm, lintegral_finsetSum_measure,
    Finset.sum_congr rfl (fun a _ => hterm a)]
  let a0 : ActionIndex z.1 := .inl (i0, j0)
  have hrate0 : (candidateRate false R z.1 a0 : ℝ) = 1 := by
    rw [candidateRate_unrestricted_pair]
    exact ite_eq_left hij0
  have hcnt0 : cnt a0 = 1 := by
    have h := carrierCount_coalSuccessor q q z.1 i0 j0 hij0
    have h1 : materialContains (z.1.2.2.2 i0).2 q := (hcar i0).mpr (Or.inl rfl)
    have h2 : materialContains (z.1.2.2.2 j0).2 q := (hcar j0).mpr (Or.inr rfl)
    simp only [carrierType, h1, h2, decide_true, Bool.and_self, Bool.toNat_true] at h
    change carrierCount q (coalSuccessor z.1 i0 j0) = 1
    omega
  have hother : ∀ a ∈ Finset.univ.erase a0,
      ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) / lam) * I (cnt a) =
        ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) / lam) * I 2 := by
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    cases a with
    | inr i => rfl
    | inl p =>
      by_cases hlt : p.1.val < p.2.val
      · have hnb : ¬(materialContains (z.1.2.2.2 p.1).2 q ∧
            materialContains (z.1.2.2.2 p.2).2 q) := by
          rintro ⟨h1, h2⟩
          apply hne
          have hp : p = (i0, j0) := by
            rcases (hcar p.1).mp h1 with e1 | e1 <;> rcases (hcar p.2).mp h2 with e2 | e2
            · rw [e1, e2] at hlt
              exact absurd hlt (lt_irrefl _)
            · exact Prod.ext e1 e2
            · rw [e1, e2] at hlt
              exact absurd hlt (Nat.lt_asymm hij0)
            · rw [e1, e2] at hlt
              exact absurd hlt (lt_irrefl _)
          rw [hp]
        have h := carrierCount_coalSuccessor q q z.1 p.1 p.2 hlt
        have hb : ((carrierType q q (z.1.2.2.2 p.1).2).1 &&
            (carrierType q q (z.1.2.2.2 p.2).2).1) = false := by
          simp only [carrierType, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          exact not_and_or.mp hnb
        rw [hb] at h
        have hc : cnt (.inl p) = 2 := by
          change carrierCount q (coalSuccessor z.1 p.1 p.2) = 2
          simp only [Bool.toNat_false, add_zero] at h
          omega
        rw [hc]
      · have hr : (candidateRate false R z.1 (.inl p) : ℝ) = 0 := by
          rw [candidateRate_unrestricted_pair]
          exact ite_eq_right hlt
        rw [hr, zero_div, ENNReal.ofReal_zero, zero_mul, zero_mul]
  have hsumrate : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) = lam := by
    simp [hlam, totalRate]
  have hrest : ∑ a ∈ Finset.univ.erase a0, (candidateRate false R z.1 a : ℝ) = lam - 1 := by
    have := Finset.add_sum_erase Finset.univ
      (fun a : ActionIndex z.1 => (candidateRate false R z.1 a : ℝ)) (Finset.mem_univ a0)
    rw [hsumrate] at this
    change (candidateRate false R z.1 a0 : ℝ) + _ = lam at this
    rw [hrate0] at this
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0), Finset.sum_congr rfl hother,
    ← Finset.sum_mul, hcnt0, hrate0,
    ← ENNReal.ofReal_sum_of_nonneg (fun a _ => div_nonneg (NNReal.coe_nonneg _) ht.le),
    ← Finset.sum_div, hrest]

def pairActive (q : ℝ) : Set AugmentedState := {z | carrierCount q z.1 = 2 ∧ 0 ≤ z.1.1}

theorem pairActive_measurable (q : ℝ) : MeasurableSet (pairActive q) :=
  (measurableSet_eq_fun ((carrierCount_measurable q).comp measurable_fst)
    measurable_const).inter (measurableSet_le measurable_const measurable_fst.fst)

open scoped Classical in
noncomputable def pairTimeFirstFn (s : ℝ) (c : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal s + if c = 2 ∧ 0 ≤ s then 1 else 0

open scoped Classical in
noncomputable def pairTimeSecondFn (s : ℝ) (c : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal s ^ 2 + if c = 2 ∧ 0 ≤ s then 2 * ENNReal.ofReal s + 2 else 0

noncomputable def pairTimeFirst (q : ℝ) (z : AugmentedState) : ℝ≥0∞ :=
  pairTimeFirstFn z.1.1 (carrierCount q z.1)

noncomputable def pairTimeSecond (q : ℝ) (z : AugmentedState) : ℝ≥0∞ :=
  pairTimeSecondFn z.1.1 (carrierCount q z.1)

theorem pairTimeFirstFn_measurable : Measurable fun p : ℝ × ℕ => pairTimeFirstFn p.1 p.2 := by
  unfold pairTimeFirstFn
  refine (ENNReal.measurable_ofReal.comp measurable_fst).add
    (Measurable.ite ?_ measurable_const measurable_const)
  exact (measurableSet_eq_fun measurable_snd measurable_const).inter
    (measurableSet_le measurable_const measurable_fst)

theorem pairTimeSecondFn_measurable :
    Measurable fun p : ℝ × ℕ => pairTimeSecondFn p.1 p.2 := by
  unfold pairTimeSecondFn
  have h : Measurable fun p : ℝ × ℕ => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  refine (h.pow_const 2).add
    (Measurable.ite ?_ ((h.const_mul 2).add measurable_const) measurable_const)
  exact (measurableSet_eq_fun measurable_snd measurable_const).inter
    (measurableSet_le measurable_const measurable_fst)

theorem pairTimeFirst_measurable (q : ℝ) : Measurable (pairTimeFirst q) := by
  have hg : Measurable fun z : AugmentedState => (z.1.1, carrierCount q z.1) :=
    measurable_fst.fst.prodMk ((carrierCount_measurable q).comp measurable_fst)
  have h : Measurable fun z : AugmentedState => pairTimeFirstFn z.1.1 (carrierCount q z.1) :=
    pairTimeFirstFn_measurable.comp hg
  exact h

theorem pairTimeSecond_measurable (q : ℝ) : Measurable (pairTimeSecond q) := by
  unfold pairTimeSecond pairTimeSecondFn
  have h : Measurable fun z : AugmentedState => ENNReal.ofReal z.1.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst.fst
  refine (h.pow_const 2).add
    (Measurable.ite ?_ ((h.const_mul 2).add measurable_const) measurable_const)
  exact (measurableSet_eq_fun ((carrierCount_measurable q).comp measurable_fst)
    measurable_const).inter (measurableSet_le measurable_const measurable_fst.fst)

theorem pairTimeFirst_of_mem {q : ℝ} {z : AugmentedState} (hz : z ∈ pairActive q) :
    pairTimeFirst q z = ENNReal.ofReal z.1.1 + 1 := by
  unfold pairTimeFirst pairTimeFirstFn
  rw [ite_eq_left (show carrierCount q z.1 = 2 ∧ 0 ≤ z.1.1 from hz)]

theorem pairTimeFirst_of_notMem {q : ℝ} {z : AugmentedState} (hz : z ∉ pairActive q) :
    pairTimeFirst q z = ENNReal.ofReal z.1.1 := by
  unfold pairTimeFirst pairTimeFirstFn
  rw [ite_eq_right (show ¬(carrierCount q z.1 = 2 ∧ 0 ≤ z.1.1) from hz), add_zero]

theorem pairTimeSecond_of_mem {q : ℝ} {z : AugmentedState} (hz : z ∈ pairActive q) :
    pairTimeSecond q z = ENNReal.ofReal z.1.1 ^ 2 + (2 * ENNReal.ofReal z.1.1 + 2) := by
  unfold pairTimeSecond pairTimeSecondFn
  rw [ite_eq_left (show carrierCount q z.1 = 2 ∧ 0 ≤ z.1.1 from hz)]

theorem pairTimeSecond_of_notMem {q : ℝ} {z : AugmentedState} (hz : z ∉ pairActive q) :
    pairTimeSecond q z = ENNReal.ofReal z.1.1 ^ 2 := by
  unfold pairTimeSecond pairTimeSecondFn
  rw [ite_eq_right (show ¬(carrierCount q z.1 = 2 ∧ 0 ≤ z.1.1) from hz), add_zero]

theorem eventKernel_pairTimeFirst (R q : ℝ) (z : AugmentedState) (hz : z ∈ pairActive q) :
    ∫⁻ w, pairTimeFirst q w ∂eventKernel false R z = pairTimeFirst q z := by
  have hm : 2 ≤ z.1.2.2.1 := by
    have h1 := materialCount_le (fun a => materialContains a q) z.1
    have h2 : carrierCount q z.1 = 2 := hz.1
    unfold carrierCount at h2
    omega
  have hone := one_le_unrestricted_totalRate R z.1 hm
  have h := eventKernel_lintegral_time_carrier R q z hz.1 pairTimeFirstFn_measurable
  set lam := (totalRate false R z.1 : ℝ) with hlam
  have ht : 0 < lam := lt_of_lt_of_le zero_lt_one hone
  have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (z.1.1 - Real.log u / lam) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub (Real.measurable_log.div_const _))
  have I1 : ∫⁻ u, pairTimeFirstFn (z.1.1 - Real.log u / lam) 1 ∂unitUniform =
      ENNReal.ofReal (z.1.1 + 1 / lam) := by
    have e : ∀ u : ℝ, pairTimeFirstFn (z.1.1 - Real.log u / lam) 1 =
        ENNReal.ofReal (z.1.1 - Real.log u / lam) := by
      intro u
      simp [pairTimeFirstFn]
    rw [lintegral_congr e]
    exact lintegral_clockTime_unitUniform z.1.1 lam hz.2 ht
  have h0 : 0 ≤ z.1.1 + 1 / lam := add_nonneg hz.2 (by positivity)
  have h1 : 0 ≤ (lam - 1) / lam := div_nonneg (by linarith) ht.le
  have I2 : ∫⁻ u, pairTimeFirstFn (z.1.1 - Real.log u / lam) 2 ∂unitUniform =
      ENNReal.ofReal (z.1.1 + 1 / lam + 1) := by
    have e : ∀ᵐ u ∂unitUniform, pairTimeFirstFn (z.1.1 - Real.log u / lam) 2 =
        ENNReal.ofReal (z.1.1 - Real.log u / lam) + 1 := by
      filter_upwards [unitUniform_ae_mem] with u hu
      have hlog : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
      have hs : 0 ≤ z.1.1 - Real.log u / lam := by
        have : 0 ≤ -Real.log u / lam := div_nonneg hlog ht.le
        have e : z.1.1 - Real.log u / lam = z.1.1 + -Real.log u / lam := by ring
        rw [e]
        exact add_nonneg hz.2 this
      unfold pairTimeFirstFn
      rw [ite_eq_left (⟨rfl, hs⟩ : (2 : ℕ) = 2 ∧ 0 ≤ z.1.1 - Real.log u / lam)]
    have hadd : ∫⁻ u, (ENNReal.ofReal (z.1.1 - Real.log u / lam) + 1) ∂unitUniform =
        ∫⁻ u, ENNReal.ofReal (z.1.1 - Real.log u / lam) ∂unitUniform +
          ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂unitUniform := lintegral_add_right _ measurable_const
    rw [lintegral_congr_ae e, hadd, lintegral_clockTime_unitUniform z.1.1 lam hz.2 ht,
      lintegral_const, measure_univ, mul_one, ENNReal.ofReal_add h0 zero_le_one,
      ENNReal.ofReal_one]
  have hval : pairTimeFirst q z = ENNReal.ofReal (z.1.1 + 1) := by
    rw [pairTimeFirst_of_mem hz, ENNReal.ofReal_add hz.2 zero_le_one, ENNReal.ofReal_one]
  have hfin : ENNReal.ofReal (1 / lam) * ENNReal.ofReal (z.1.1 + 1 / lam) +
      ENNReal.ofReal ((lam - 1) / lam) * ENNReal.ofReal (z.1.1 + 1 / lam + 1) =
      ENNReal.ofReal (z.1.1 + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul h1,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) h0)
        (mul_nonneg h1 (add_nonneg h0 zero_le_one))]
    congr 1
    field_simp
    ring
  have hgoal : ∫⁻ w, pairTimeFirstFn w.1.1 (carrierCount q w.1) ∂eventKernel false R z =
      ENNReal.ofReal (z.1.1 + 1) := by
    rw [h, I1, I2, hfin]
  rw [hval]
  exact hgoal

theorem eventKernel_pairTimeSecond (R q : ℝ) (z : AugmentedState) (hz : z ∈ pairActive q) :
    ∫⁻ w, pairTimeSecond q w ∂eventKernel false R z = pairTimeSecond q z := by
  have hm : 2 ≤ z.1.2.2.1 := by
    have h1 := materialCount_le (fun a => materialContains a q) z.1
    have h2 : carrierCount q z.1 = 2 := hz.1
    unfold carrierCount at h2
    omega
  have hone := one_le_unrestricted_totalRate R z.1 hm
  have h := eventKernel_lintegral_time_carrier R q z hz.1 pairTimeSecondFn_measurable
  set lam := (totalRate false R z.1 : ℝ) with hlam
  have ht : 0 < lam := lt_of_lt_of_le zero_lt_one hone
  have hmeas : Measurable fun u : ℝ => ENNReal.ofReal (z.1.1 - Real.log u / lam) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub (Real.measurable_log.div_const _))
  have I1 : ∫⁻ u, pairTimeSecondFn (z.1.1 - Real.log u / lam) 1 ∂unitUniform =
      ENNReal.ofReal (z.1.1 ^ 2 + 2 * z.1.1 / lam + 2 / lam ^ 2) := by
    have e : ∀ u : ℝ, pairTimeSecondFn (z.1.1 - Real.log u / lam) 1 =
        ENNReal.ofReal (z.1.1 - Real.log u / lam) ^ 2 := by
      intro u
      simp [pairTimeSecondFn]
    rw [lintegral_congr e]
    exact lintegral_clockTime_sq_unitUniform z.1.1 lam hz.2 ht
  have h0 : 0 ≤ z.1.1 + 1 / lam := add_nonneg hz.2 (by positivity)
  have h1 : 0 ≤ (lam - 1) / lam := div_nonneg (by linarith) ht.le
  have hA : 0 ≤ z.1.1 ^ 2 + 2 * z.1.1 / lam + 2 / lam ^ 2 :=
    add_nonneg (add_nonneg (pow_nonneg hz.2 2)
      (div_nonneg (mul_nonneg zero_le_two hz.2) ht.le)) (by positivity)
  have hB : 0 ≤ 2 * (z.1.1 + 1 / lam) + 2 := add_nonneg (mul_nonneg zero_le_two h0) zero_le_two
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have I2 : ∫⁻ u, pairTimeSecondFn (z.1.1 - Real.log u / lam) 2 ∂unitUniform =
      ENNReal.ofReal (z.1.1 ^ 2 + 2 * z.1.1 / lam + 2 / lam ^ 2 +
        (2 * (z.1.1 + 1 / lam) + 2)) := by
    have e : ∀ᵐ u ∂unitUniform, pairTimeSecondFn (z.1.1 - Real.log u / lam) 2 =
        ENNReal.ofReal (z.1.1 - Real.log u / lam) ^ 2 +
          (2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) + 2) := by
      filter_upwards [unitUniform_ae_mem] with u hu
      have hlog : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
      have hs : 0 ≤ z.1.1 - Real.log u / lam := by
        have : 0 ≤ -Real.log u / lam := div_nonneg hlog ht.le
        have e : z.1.1 - Real.log u / lam = z.1.1 + -Real.log u / lam := by ring
        rw [e]
        exact add_nonneg hz.2 this
      unfold pairTimeSecondFn
      rw [ite_eq_left (⟨rfl, hs⟩ : (2 : ℕ) = 2 ∧ 0 ≤ z.1.1 - Real.log u / lam)]
    have hm2 : Measurable fun u : ℝ => 2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) + 2 :=
      (hmeas.const_mul 2).add measurable_const
    have hadd1 : ∫⁻ u, (ENNReal.ofReal (z.1.1 - Real.log u / lam) ^ 2 +
        (2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) + 2)) ∂unitUniform =
        ∫⁻ u, ENNReal.ofReal (z.1.1 - Real.log u / lam) ^ 2 ∂unitUniform +
          ∫⁻ u, (2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) + 2) ∂unitUniform :=
      lintegral_add_right _ hm2
    have hadd2 : ∫⁻ u, (2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) + 2) ∂unitUniform =
        ∫⁻ u, 2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) ∂unitUniform +
          ∫⁻ _ : ℝ, (2 : ℝ≥0∞) ∂unitUniform := lintegral_add_right _ measurable_const
    have hmul : ∫⁻ u, 2 * ENNReal.ofReal (z.1.1 - Real.log u / lam) ∂unitUniform =
        2 * ∫⁻ u, ENNReal.ofReal (z.1.1 - Real.log u / lam) ∂unitUniform :=
      lintegral_const_mul _ hmeas
    rw [lintegral_congr_ae e, hadd1, hadd2, hmul,
      lintegral_clockTime_sq_unitUniform z.1.1 lam hz.2 ht,
      lintegral_clockTime_unitUniform z.1.1 lam hz.2 ht, lintegral_const, measure_univ,
      mul_one, ENNReal.ofReal_add hA hB, ENNReal.ofReal_add (mul_nonneg zero_le_two h0)
        zero_le_two, ENNReal.ofReal_mul zero_le_two, ← htwo]
  have hval : pairTimeSecond q z = ENNReal.ofReal (z.1.1 ^ 2 + (2 * z.1.1 + 2)) := by
    rw [pairTimeSecond_of_mem hz, ENNReal.ofReal_add (pow_nonneg hz.2 2)
      (add_nonneg (mul_nonneg zero_le_two hz.2) zero_le_two),
      ENNReal.ofReal_add (mul_nonneg zero_le_two hz.2) zero_le_two,
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_pow hz.2, ← htwo]
  have hfin : ENNReal.ofReal (1 / lam) *
        ENNReal.ofReal (z.1.1 ^ 2 + 2 * z.1.1 / lam + 2 / lam ^ 2) +
      ENNReal.ofReal ((lam - 1) / lam) *
        ENNReal.ofReal (z.1.1 ^ 2 + 2 * z.1.1 / lam + 2 / lam ^ 2 +
          (2 * (z.1.1 + 1 / lam) + 2)) =
      ENNReal.ofReal (z.1.1 ^ 2 + (2 * z.1.1 + 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul h1,
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) hA)
        (mul_nonneg h1 (add_nonneg hA hB))]
    congr 1
    field_simp
    ring
  have hgoal : ∫⁻ w, pairTimeSecondFn w.1.1 (carrierCount q w.1) ∂eventKernel false R z =
      ENNReal.ofReal (z.1.1 ^ 2 + (2 * z.1.1 + 2)) := by
    rw [h, I1, I2, hfin]
  rw [hval]
  exact hgoal

end Rhone.Coalescent.IntervalProcess
