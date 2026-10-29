/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGPairTimeMoments
public import Rhone.Coalescent.FullARGTwoSample
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Variance, covariance, and correlation of two-sample pair coalescence times at two probes

Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory MarkovChain
open scoped ENNReal

theorem ENNReal_sq_add_sq (a b : ℝ≥0∞) :
    a ^ 2 + b ^ 2 = (b - a) ^ 2 + (a - b) ^ 2 + 2 * (a * b) := by
  wlog h : a ≤ b generalizing a b
  · rw [add_comm (a ^ 2), this b a (le_of_not_ge h), add_comm ((a - b) ^ 2), mul_comm b a]
  by_cases ha : a = ∞
  · subst ha
    have hb : b = ∞ := top_le_iff.mp h
    subst hb
    simp
  · obtain ⟨d, rfl⟩ := exists_add_of_le h
    rw [ENNReal.add_sub_cancel_left ha, tsub_eq_zero_of_le h]
    ring

theorem pathLaw_lintegral_mul_pairTime_sub_sq (R : ℝ) (hR : 0 ≤ R) (y : GenomicProbe)
    (m : ℕ) {e : EventPath → ℝ≥0∞}
    (he : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) m] e)
    (hsupp : ∀ ω, e ω ≠ 0 → ω m ∈ pairActive (y.val : ℝ))
    (hfin : ∫⁻ ω, e ω * (ENNReal.ofReal (ω m).1.1 ^ 2 + 1)
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞) :
    ∫⁻ ω, e ω * (genealogyObservation 2 ω y 0 1 - ENNReal.ofReal (ω m).1.1) ^ 2
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      2 * ∫⁻ ω, e ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
  have hle := (Filtration.piLE (X := fun _ : ℕ => AugmentedState)).le m
  have hsm : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) m]
      (fun ω : EventPath => ENNReal.ofReal (ω m).1.1) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).comp
      (DiscreteProcess.measurable_eval_piLE (S := AugmentedState) m)
  have hea : Measurable e := he.mono hle le_rfl
  have hsa : Measurable fun ω : EventPath => ENNReal.ofReal (ω m).1.1 := hsm.mono hle le_rfl
  have hYa : Measurable fun ω : EventPath => genealogyObservation 2 ω y 0 1 :=
    (measurable_pairTime y).comp (genealogyObservation_measurable 2)
  have hes : Measurable fun ω : EventPath => e ω * ENNReal.ofReal (ω m).1.1 := hea.mul hsa
  have hes2 : Measurable fun ω : EventPath => e ω * ENNReal.ofReal (ω m).1.1 ^ 2 :=
    hea.mul (hsa.pow_const 2)
  have hI0 : ∫⁻ ω, e ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun ω => ?_)
    calc e ω = e ω * 1 := (mul_one _).symm
      _ ≤ e ω * (ENNReal.ofReal (ω m).1.1 ^ 2 + 1) := by gcongr; exact le_add_self
  have hI2 : ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 ^ 2
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun ω => ?_)
    change e ω * ENNReal.ofReal (ω m).1.1 ^ 2 ≤ e ω * (ENNReal.ofReal (ω m).1.1 ^ 2 + 1)
    gcongr
    exact le_self_add
  have hI1 : ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun ω => ?_)
    change e ω * ENNReal.ofReal (ω m).1.1 ≤ e ω * (ENNReal.ofReal (ω m).1.1 ^ 2 + 1)
    gcongr
    calc ENNReal.ofReal (ω m).1.1 ≤ 2 * ENNReal.ofReal (ω m).1.1 := by
          rw [two_mul]; exact le_self_add
      _ ≤ ENNReal.ofReal (ω m).1.1 ^ 2 + 1 := ENNReal_two_mul_le_sq_add_one _
  have hRb : ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 *
        (pairActive (y.val : ℝ)).indicator (pairTimeFirst (y.val : ℝ)) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 ^ 2
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
        ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
    rw [← lintegral_add_left hes2]
    refine lintegral_congr fun ω => ?_
    by_cases h : e ω = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hsupp ω h), pairTimeFirst_of_mem (hsupp ω h)]
      ring
  have hb : ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 * genealogyObservation 2 ω y 0 1
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 ^ 2
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
        ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
    have hmain := pathLaw_lintegral_mul_pairTime R hR y m
      (W := fun ω => e ω * ENNReal.ofReal (ω m).1.1) (he.mul hsm)
      (by rw [hRb]; exact ENNReal.add_ne_top.mpr ⟨hI2, hI1⟩)
    rw [hRb] at hmain
    rw [← hmain]
    refine lintegral_congr fun ω => ?_
    by_cases h : e ω = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hsupp ω h)]
  have hRc : ∫⁻ ω, e ω *
        (pairActive (y.val : ℝ)).indicator (pairTimeSecond (y.val : ℝ)) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 ^ 2
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
        (2 * ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1
            ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
          2 * ∫⁻ ω, e ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ()))) := by
    rw [← lintegral_const_mul 2 hes, ← lintegral_const_mul 2 hea,
      ← lintegral_add_left (hes.const_mul 2), ← lintegral_add_left hes2]
    refine lintegral_congr fun ω => ?_
    by_cases h : e ω = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hsupp ω h), pairTimeSecond_of_mem (hsupp ω h)]
      ring
  have hc : ∫⁻ ω, e ω * genealogyObservation 2 ω y 0 1 ^ 2
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1 ^ 2
          ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
        (2 * ∫⁻ ω, e ω * ENNReal.ofReal (ω m).1.1
            ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) +
          2 * ∫⁻ ω, e ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ()))) := by
    have hmain := pathLaw_lintegral_mul_pairTime_sq R hR y m (W := e) he
      (by
        rw [hRc]
        exact ENNReal.add_ne_top.mpr ⟨hI2, ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top (by simp) hI1, ENNReal.mul_ne_top (by simp) hI0⟩⟩)
    rw [hRc] at hmain
    rw [← hmain]
    refine lintegral_congr fun ω => ?_
    by_cases h : e ω = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hsupp ω h)]
  have hpt : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      e ω * (genealogyObservation 2 ω y 0 1 - ENNReal.ofReal (ω m).1.1) ^ 2 +
          2 * (e ω * ENNReal.ofReal (ω m).1.1 * genealogyObservation 2 ω y 0 1) =
        e ω * genealogyObservation 2 ω y 0 1 ^ 2 + e ω * ENNReal.ofReal (ω m).1.1 ^ 2 := by
    filter_upwards [eventProcess_pairTimePath R hR] with ω hω
    by_cases h : e ω = 0
    · simp [h]
    · obtain ⟨K, hK, hT⟩ := hω.exists_exit y
      have hmK : m < K := (hK m).mpr (hsupp ω h)
      have hsY : ENNReal.ofReal (ω m).1.1 ≤ genealogyObservation 2 ω y 0 1 := by
        rw [hT]
        exact ENNReal.ofReal_le_ofReal (hω.1.time_monotone hmK.le)
      obtain ⟨d, hd⟩ := exists_add_of_le hsY
      rw [hd, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
      ring
  have hesY : Measurable fun ω : EventPath =>
      e ω * ENNReal.ofReal (ω m).1.1 * genealogyObservation 2 ω y 0 1 := hes.mul hYa
  have hYs : Measurable fun ω : EventPath =>
      2 * (e ω * ENNReal.ofReal (ω m).1.1 * genealogyObservation 2 ω y 0 1) :=
    hesY.const_mul 2
  have hint := lintegral_congr_ae hpt
  rw [lintegral_add_right _ hYs, lintegral_const_mul 2 hesY,
    lintegral_add_right _ hes2, hb, hc] at hint
  refine (ENNReal.add_left_inj (ENNReal.mul_ne_top (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (ENNReal.add_ne_top.mpr ⟨hI2, hI1⟩))).mp ?_
  rw [hint]
  ring

def pairExitBefore (x y : GenomicProbe) (k : ℕ) : Set EventPath :=
  {ω | ω k ∈ pairActive (x.val : ℝ) ∧ ω (k + 1) ∉ pairActive (x.val : ℝ) ∧
    ω (k + 1) ∈ pairActive (y.val : ℝ)}

theorem pairExitBefore_measurableSet_piLE (x y : GenomicProbe) (k : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => AugmentedState) (k + 1)]
      (pairExitBefore x y k) := by
  have hk : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) (k + 1)]
      (fun ω : EventPath => ω k) :=
    (DiscreteProcess.measurable_eval_piLE (S := AugmentedState) k).mono
      ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).mono (Nat.le_succ k)) le_rfl
  have hk1 := DiscreteProcess.measurable_eval_piLE (S := AugmentedState) (k + 1)
  exact MeasurableSet.inter (hk (pairActive_measurable (x.val : ℝ)))
    (MeasurableSet.inter (hk1 (pairActive_measurable (x.val : ℝ))).compl
      (hk1 (pairActive_measurable (y.val : ℝ))))

theorem pairExitBefore_measurableSet (x y : GenomicProbe) (k : ℕ) :
    MeasurableSet (pairExitBefore x y k) :=
  (Filtration.piLE (X := fun _ : ℕ => AugmentedState)).le (k + 1) _
    (pairExitBefore_measurableSet_piLE x y k)

theorem pathLaw_lintegral_pairExitBefore_sub_sq (R : ℝ) (hR : 0 ≤ R) (x y : GenomicProbe)
    (k : ℕ) :
    ∫⁻ ω, (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (genealogyObservation 2 ω y 0 1 - ENNReal.ofReal (ω (k + 1)).1.1) ^ 2
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      2 * (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        (pairExitBefore x y k) := by
  have hmain := pathLaw_lintegral_mul_pairTime_sub_sq R hR y (k + 1)
    (e := (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)))
    (Measurable.indicator measurable_const (pairExitBefore_measurableSet_piLE x y k))
    (fun ω h => by
      by_contra hmem
      exact h (Set.indicator_of_notMem (fun hE => hmem hE.2.2) _))
    (by
      have hbound : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
          (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
              (ENNReal.ofReal (ω (k + 1)).1.1 ^ 2 + 1) ≤
            genealogyObservation 2 ω x 0 1 ^ 2 + 1 := by
        filter_upwards [eventProcess_pairTimePath R hR] with ω hω
        by_cases hE : ω ∈ pairExitBefore x y k
        · obtain ⟨K, hK, hT⟩ := hω.exists_exit x
          have h1 := (hK k).mpr hE.1
          have h2 : ¬k + 1 < K := fun h => hE.2.1 ((hK _).mp h)
          have hKk : K = k + 1 := by omega
          rw [Set.indicator_of_mem hE, one_mul, hT, hKk]
        · rw [Set.indicator_of_notMem hE, zero_mul]
          exact bot_le
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
      have hXa : Measurable fun ω : EventPath => genealogyObservation 2 ω x 0 1 ^ 2 :=
        ((measurable_pairTime x).comp (genealogyObservation_measurable 2)).pow_const 2
      rw [lintegral_add_left hXa, pathLaw_lintegral_pairTime_sq R hR x, lintegral_const,
        measure_univ, mul_one]
      simp)
  rw [hmain, lintegral_indicator_const (pairExitBefore_measurableSet x y k), one_mul]

theorem pathLaw_lintegral_pairTime_sub_sq (R : ℝ) (hR : 0 ≤ R) (x y : GenomicProbe) :
    ∫⁻ ω, (genealogyObservation 2 ω y 0 1 - genealogyObservation 2 ω x 0 1) ^ 2
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      2 * (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        {ω | genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1} := by
  have hXa : Measurable fun ω : EventPath => genealogyObservation 2 ω x 0 1 :=
    (measurable_pairTime x).comp (genealogyObservation_measurable 2)
  have hYa : Measurable fun ω : EventPath => genealogyObservation 2 ω y 0 1 :=
    (measurable_pairTime y).comp (genealogyObservation_measurable 2)
  have hE := pairExitBefore_measurableSet x y
  have hpt : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      (genealogyObservation 2 ω y 0 1 - genealogyObservation 2 ω x 0 1) ^ 2 =
          ∑' k, (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (genealogyObservation 2 ω y 0 1 - ENNReal.ofReal (ω (k + 1)).1.1) ^ 2 ∧
        {ω | genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω =
          ∑' k, (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    filter_upwards [eventProcess_pairTimePath R hR] with ω hω
    obtain ⟨Kx, hKx, hX⟩ := hω.exists_exit x
    obtain ⟨Ky, hKy, hY⟩ := hω.exists_exit y
    have h0 : 0 < Kx := (hKx 0).mpr (by rw [hω.1.1]; exact initial_mem_pairActive x)
    have hK1 : Kx - 1 + 1 = Kx := by omega
    have hmemE : ∀ k, ω ∈ pairExitBefore x y k ↔ k + 1 = Kx ∧ Kx < Ky := by
      intro k
      constructor
      · rintro ⟨h1, h2, h3⟩
        have a := (hKx k).mpr h1
        have b : ¬k + 1 < Kx := fun h => h2 ((hKx _).mp h)
        have c := (hKy _).mpr h3
        omega
      · rintro ⟨h1, h2⟩
        refine ⟨(hKx k).mp (by omega), fun h => ?_, (hKy _).mp (by omega)⟩
        have := (hKx _).mpr h
        omega
    by_cases hlt : Kx < Ky
    · have hne : ∀ k, k ≠ Kx - 1 → ω ∉ pairExitBefore x y k := by
        intro k hk h
        have := ((hmemE k).mp h).1
        omega
      have hin : ω ∈ pairExitBefore x y (Kx - 1) := (hmemE _).mpr ⟨hK1, hlt⟩
      have ht1 : (ω Kx).1.1 < (ω (Kx + 1)).1.1 := hω.time_lt_succ y ((hKy Kx).mp hlt)
      have ht2 : (ω (Kx + 1)).1.1 ≤ (ω Ky).1.1 := hω.1.time_monotone (by omega)
      have ht0 : 0 ≤ (ω Kx).1.1 := (hω.1.valid Kx).1
      have hXY : ω ∈ {ω | genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1} := by
        change genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1
        rw [hX, hY]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      constructor
      · rw [tsum_eq_single (Kx - 1) (fun k hk => by
          rw [Set.indicator_of_notMem (hne k hk), zero_mul]),
          Set.indicator_of_mem hin, one_mul, hK1, hX]
      · rw [tsum_eq_single (Kx - 1) (fun k hk => Set.indicator_of_notMem (hne k hk) _),
          Set.indicator_of_mem hin, Set.indicator_of_mem hXY]
    · have hne : ∀ k, ω ∉ pairExitBefore x y k := fun k h => hlt ((hmemE k).mp h).2
      have hYX : genealogyObservation 2 ω y 0 1 ≤ genealogyObservation 2 ω x 0 1 := by
        rw [hX, hY]
        exact ENNReal.ofReal_le_ofReal (hω.1.time_monotone (not_lt.mp hlt))
      constructor
      · rw [tsub_eq_zero_of_le hYX, ENNReal.tsum_eq_zero.mpr (fun k => by
          rw [Set.indicator_of_notMem (hne k), zero_mul])]
        simp
      · have hnot : ω ∉ {ω : EventPath |
            genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1} :=
          fun h => not_le.mpr (show genealogyObservation 2 ω x 0 1 <
            genealogyObservation 2 ω y 0 1 from h) hYX
        rw [ENNReal.tsum_eq_zero.mpr (fun k => Set.indicator_of_notMem (hne k) _),
          Set.indicator_of_notMem hnot]
  have hterm : ∀ k, Measurable fun ω : EventPath =>
      (pairExitBefore x y k).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (genealogyObservation 2 ω y 0 1 - ENNReal.ofReal (ω (k + 1)).1.1) ^ 2 := fun k =>
    (measurable_const.indicator (hE k)).mul
      ((hYa.sub ((ENNReal.measurable_ofReal.comp measurable_fst.fst).comp
        (measurable_pi_apply (k + 1)))).pow_const 2)
  have hμ : (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        {ω | genealogyObservation 2 ω x 0 1 < genealogyObservation 2 ω y 0 1} =
      ∑' k, (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        (pairExitBefore x y k) := by
    have h1 := lintegral_indicator_const
      (μ := (eventProcess false R).pathLaw (initialState 2, (0, .inl ())))
      (measurableSet_lt hXa hYa) (1 : ℝ≥0∞)
    rw [one_mul] at h1
    rw [← h1, lintegral_congr_ae (hpt.mono fun ω h => h.2),
      lintegral_tsum fun k => (measurable_const.indicator (hE k)).aemeasurable]
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator_const (hE k), one_mul]
  rw [lintegral_congr_ae (hpt.mono fun ω h => h.1),
    lintegral_tsum fun k => (hterm k).aemeasurable, hμ, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun k => pathLaw_lintegral_pairExitBefore_sub_sq R hR x y k

theorem fullARG_two_sample_pairTime_tsub_sq_lintegral (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) :
    ∫⁻ G, (G y 0 1 - G x 0 1) ^ 2 ∂fullARGGenealogyLaw 2 R =
      2 * fullARGGenealogyLaw 2 R {G | G x 0 1 < G y 0 1} := by
  have hm : Measurable fun G : Genealogy 2 => (G y 0 1 - G x 0 1) ^ 2 :=
    ((measurable_pairTime y).sub (measurable_pairTime x)).pow_const 2
  unfold fullARGGenealogyLaw
  rw [lintegral_map hm (genealogyObservation_measurable 2),
    Measure.map_apply (genealogyObservation_measurable 2)
      (measurableSet_lt (measurable_pairTime x) (measurable_pairTime y))]
  exact pathLaw_lintegral_pairTime_sub_sq R hR x y

/-- Source: mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_sub_sq_lintegral (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) :
    ∫⁻ G, ((G y 0 1 - G x 0 1) ^ 2 + (G x 0 1 - G y 0 1) ^ 2) ∂fullARGGenealogyLaw 2 R =
      2 * fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} := by
  have hset : {G : Genealogy 2 | G x 0 1 ≠ G y 0 1} =
      {G | G x 0 1 < G y 0 1} ∪ {G | G y 0 1 < G x 0 1} := by
    ext G
    exact lt_or_lt_iff_ne.symm
  have hdisj : Disjoint {G : Genealogy 2 | G x 0 1 < G y 0 1} {G | G y 0 1 < G x 0 1} :=
    Set.disjoint_left.mpr fun G h1 h2 => lt_asymm (show G x 0 1 < G y 0 1 from h1) h2
  have hm : Measurable fun G : Genealogy 2 => (G y 0 1 - G x 0 1) ^ 2 :=
    ((measurable_pairTime y).sub (measurable_pairTime x)).pow_const 2
  rw [lintegral_add_left hm,
    fullARG_two_sample_pairTime_tsub_sq_lintegral R hR x y,
    fullARG_two_sample_pairTime_tsub_sq_lintegral R hR y x, hset,
    measure_union hdisj (measurableSet_lt (measurable_pairTime y) (measurable_pairTime x)),
    mul_add]

theorem fullARG_two_sample_pairTime_mul_lintegral_eq_agreement (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) :
    ∫⁻ G, G x 0 1 * G y 0 1 ∂fullARGGenealogyLaw 2 R =
      1 + fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} := by
  have hx2 := (measurable_pairTime x).pow_const 2
  have hD : Measurable fun G : Genealogy 2 =>
      (G y 0 1 - G x 0 1) ^ 2 + (G x 0 1 - G y 0 1) ^ 2 :=
    (((measurable_pairTime y).sub (measurable_pairTime x)).pow_const 2).add
      (((measurable_pairTime x).sub (measurable_pairTime y)).pow_const 2)
  have hP : Measurable fun G : Genealogy 2 => G x 0 1 * G y 0 1 :=
    (measurable_pairTime x).mul (measurable_pairTime y)
  have hint := lintegral_congr (μ := fullARGGenealogyLaw 2 R)
    fun G : Genealogy 2 => ENNReal_sq_add_sq (G x 0 1) (G y 0 1)
  rw [lintegral_add_left hx2, fullARG_two_sample_pairTime_sq_lintegral R hR x,
    fullARG_two_sample_pairTime_sq_lintegral R hR y, lintegral_add_left hD,
    fullARG_two_sample_pairTime_sub_sq_lintegral R hR x y, lintegral_const_mul 2 hP] at hint
  have hcompl : fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} +
      fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} = 1 := by
    have h := measure_add_measure_compl (μ := fullARGGenealogyLaw 2 R)
      (twoSample_agreement_measurableSet x y)
    rw [measure_univ] at h
    exact h
  have hne : fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} ≠ ∞ := measure_ne_top _ _
  have h2 : (2 : ℝ≥0∞) * fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hne
  have hsum : 2 * ∫⁻ G, G x 0 1 * G y 0 1 ∂fullARGGenealogyLaw 2 R +
        2 * fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} =
      2 * (1 + fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1}) +
        2 * fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1} := by
    rw [add_comm, ← hint]
    calc (2 : ℝ≥0∞) + 2 = 2 * 1 + 2 * 1 := by ring
      _ = 2 * 1 + 2 * (fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} +
            fullARGGenealogyLaw 2 R {G | G x 0 1 ≠ G y 0 1}) := by rw [hcompl]
      _ = _ := by ring
  exact (ENNReal.mul_right_inj (by simp) (by simp)).mp ((ENNReal.add_left_inj h2).mp hsum)

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989. -/
theorem fullARG_two_sample_pairTime_mul_lintegral (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    ∫⁻ G, G x 0 1 * G y 0 1 ∂fullARGGenealogyLaw 2 R =
      ENNReal.ofReal
        (1 + (R * ((y.val : ℝ) - (x.val : ℝ)) + 18) /
          ((R * ((y.val : ℝ) - (x.val : ℝ))) ^ 2 + 13 * (R * ((y.val : ℝ) - (x.val : ℝ))) +
            18)) := by
  have hxy' : (x.val : ℝ) < (y.val : ℝ) := by exact_mod_cast hxy
  have hρ : 0 ≤ R * ((y.val : ℝ) - (x.val : ℝ)) := mul_nonneg hR (sub_nonneg.mpr hxy'.le)
  rw [fullARG_two_sample_pairTime_mul_lintegral_eq_agreement R hR x y,
    fullARG_two_sample_agreement_prob_explicit R hR x y hxy,
    ENNReal.ofReal_add zero_le_one (div_nonneg (add_nonneg hρ (by norm_num))
      (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hρ)) (by norm_num))),
    ENNReal.ofReal_one]

/-- Source: hudson1983, p. 188, eq. (10), p. 189; mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_integral (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    ∫ G, (G x 0 1).toReal ∂fullARGGenealogyLaw 2 R = 1 := by
  rw [integral_toReal (measurable_pairTime x).aemeasurable
    ((fullARGGenealogyLaw_ae_finite 2 R hR).mono fun G h => h x 0 1),
    fullARG_two_sample_pairTime_lintegral R hR x]
  simp

theorem fullARG_two_sample_pairTime_sq_integral (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    ∫ G, (G x 0 1).toReal ^ 2 ∂fullARGGenealogyLaw 2 R = 2 := by
  have h : (fun G : Genealogy 2 => (G x 0 1).toReal ^ 2) = fun G => (G x 0 1 ^ 2).toReal := by
    funext G
    rw [ENNReal.toReal_pow]
  rw [h, integral_toReal ((measurable_pairTime x).pow_const 2).aemeasurable
    ((fullARGGenealogyLaw_ae_finite 2 R hR).mono fun G h => ENNReal.pow_lt_top (h x 0 1)),
    fullARG_two_sample_pairTime_sq_lintegral R hR x]
  simp

theorem fullARG_two_sample_pairTime_memLp (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    MemLp (fun G : Genealogy 2 => (G x 0 1).toReal) 2 (fullARGGenealogyLaw 2 R) := by
  rw [memLp_two_iff_integrable_sq (measurable_pairTime x).ennreal_toReal.aestronglyMeasurable]
  have h : (fun G : Genealogy 2 => (G x 0 1).toReal ^ 2) = fun G => (G x 0 1 ^ 2).toReal := by
    funext G
    rw [ENNReal.toReal_pow]
  rw [h]
  refine integrable_toReal_of_lintegral_ne_top
    ((measurable_pairTime x).pow_const 2).aemeasurable ?_
  rw [fullARG_two_sample_pairTime_sq_lintegral R hR x]
  simp

/-- Source: hudson1983, p. 188, eq. (10), p. 189; mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_variance (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    Var[fun G : Genealogy 2 => (G x 0 1).toReal; fullARGGenealogyLaw 2 R] = 1 := by
  have h1 : ∫ G, ((fun G : Genealogy 2 => (G x 0 1).toReal) ^ 2) G
      ∂fullARGGenealogyLaw 2 R = 2 := fullARG_two_sample_pairTime_sq_integral R hR x
  rw [variance_eq_sub (fullARG_two_sample_pairTime_memLp R hR x), h1,
    fullARG_two_sample_pairTime_integral R hR x]
  norm_num

/-- Source: mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_covariance_eq_agreement (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) :
    cov[fun G : Genealogy 2 => (G x 0 1).toReal, fun G : Genealogy 2 => (G y 0 1).toReal;
        fullARGGenealogyLaw 2 R] = (fullARGGenealogyLaw 2 R).real {G | G x 0 1 = G y 0 1} := by
  have hfin := fullARGGenealogyLaw_ae_finite 2 R hR
  have h : (fun G : Genealogy 2 => (G x 0 1).toReal * (G y 0 1).toReal) =
      fun G => (G x 0 1 * G y 0 1).toReal := by
    funext G
    rw [ENNReal.toReal_mul]
  have h1 : ∫ G, ((fun G : Genealogy 2 => (G x 0 1).toReal) *
        (fun G : Genealogy 2 => (G y 0 1).toReal)) G ∂fullARGGenealogyLaw 2 R =
      1 + (fullARGGenealogyLaw 2 R).real {G | G x 0 1 = G y 0 1} := by
    change ∫ G : Genealogy 2, (G x 0 1).toReal * (G y 0 1).toReal
      ∂fullARGGenealogyLaw 2 R = _
    have hP : Measurable fun G : Genealogy 2 => G x 0 1 * G y 0 1 :=
      (measurable_pairTime x).mul (measurable_pairTime y)
    rw [h, integral_toReal hP.aemeasurable
      (hfin.mono fun G h => ENNReal.mul_lt_top (h x 0 1) (h y 0 1)),
      fullARG_two_sample_pairTime_mul_lintegral_eq_agreement R hR x y,
      ENNReal.toReal_add ENNReal.one_ne_top (measure_ne_top _ _), ENNReal.toReal_one,
      measureReal_def]
  rw [covariance_eq_sub (fullARG_two_sample_pairTime_memLp R hR x)
    (fullARG_two_sample_pairTime_memLp R hR y), h1,
    fullARG_two_sample_pairTime_integral R hR x, fullARG_two_sample_pairTime_integral R hR y]
  ring

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989. -/
theorem fullARG_two_sample_pairTime_covariance (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    cov[fun G : Genealogy 2 => (G x 0 1).toReal, fun G : Genealogy 2 => (G y 0 1).toReal;
        fullARGGenealogyLaw 2 R] =
      (R * ((y.val : ℝ) - (x.val : ℝ)) + 18) /
        ((R * ((y.val : ℝ) - (x.val : ℝ))) ^ 2 + 13 * (R * ((y.val : ℝ) - (x.val : ℝ))) +
          18) := by
  have hxy' : (x.val : ℝ) < (y.val : ℝ) := by exact_mod_cast hxy
  have hρ : 0 ≤ R * ((y.val : ℝ) - (x.val : ℝ)) := mul_nonneg hR (sub_nonneg.mpr hxy'.le)
  rw [fullARG_two_sample_pairTime_covariance_eq_agreement R hR x y, measureReal_def,
    fullARG_two_sample_agreement_prob_explicit R hR x y hxy,
    ENNReal.toReal_ofReal (div_nonneg (add_nonneg hρ (by norm_num))
      (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hρ)) (by norm_num)))]

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989. -/
theorem fullARG_two_sample_pairTime_correlation (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    cov[fun G : Genealogy 2 => (G x 0 1).toReal, fun G : Genealogy 2 => (G y 0 1).toReal;
        fullARGGenealogyLaw 2 R] /
      (Real.sqrt Var[fun G : Genealogy 2 => (G x 0 1).toReal; fullARGGenealogyLaw 2 R] *
        Real.sqrt Var[fun G : Genealogy 2 => (G y 0 1).toReal; fullARGGenealogyLaw 2 R]) =
      (R * ((y.val : ℝ) - (x.val : ℝ)) + 18) /
        ((R * ((y.val : ℝ) - (x.val : ℝ))) ^ 2 + 13 * (R * ((y.val : ℝ) - (x.val : ℝ))) +
          18) := by
  rw [fullARG_two_sample_pairTime_covariance R hR x y hxy,
    fullARG_two_sample_pairTime_variance R hR x, fullARG_two_sample_pairTime_variance R hR y,
    Real.sqrt_one, mul_one, div_one]

end Rhone.Coalescent.IntervalProcess
