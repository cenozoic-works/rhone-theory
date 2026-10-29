/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Dynkin
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # All moments of the absorption time are finite -/

@[expose] public section

namespace Rhone.Coalescent.BranchLengthMoments

open Finset TwoLocusGenealogy TypedAncestralChain LinearAlgebra.Recursion
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

section HitIndex

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sInf_eq_iff_of_pos {S : Set ℕ} {j : ℕ} (hj : 0 < j) :
    sInf S = j ↔ j ∈ S ∧ ∀ i < j, i ∉ S := by
  constructor
  · intro hS
    have hne : S.Nonempty := by
      rcases Set.eq_empty_or_nonempty S with rfl | hh
      · rw [Nat.sInf_empty] at hS
        omega
      · exact hh
    refine ⟨hS ▸ Nat.sInf_mem hne, fun i hi hiS => ?_⟩
    have := Nat.sInf_le hiS
    omega
  · rintro ⟨hjS, hlt⟩
    refine le_antisymm (Nat.sInf_le hjS) ?_
    by_contra hc
    exact hlt _ (not_le.1 hc) (Nat.sInf_mem ⟨j, hjS⟩)

theorem measurable_firstIndex {D : ℕ → Set Ω} (hD : ∀ k, MeasurableSet (D k)) :
    Measurable fun ω => sInf {k | ω ∈ D k} := by
  refine measurable_to_countable' fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hset : (fun ω => sInf {k | ω ∈ D k}) ⁻¹' {0} = D 0 ∪ ⋂ k, (D k)ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Nat.sInf_eq_zero, Set.mem_union,
        Set.mem_iInter, Set.mem_compl_iff, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq]
    rw [hset]
    exact (hD 0).union (MeasurableSet.iInter fun k => (hD k).compl)
  · have hset : (fun ω => sInf {k | ω ∈ D k}) ⁻¹' {j}
        = D j ∩ ⋂ i, ⋂ (_ : i < j), (D i)ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, sInf_eq_iff_of_pos hj,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [hset]
    exact (hD j).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hD i).compl)

end HitIndex

def notAbsAt (N : ℕ) : Set ((_ : ℕ) → TS n KA KB) := {ω | (ω N).st.1 ≠ ∅}

theorem measurableSet_notAbsAt (N : ℕ) :
    MeasurableSet (notAbsAt (n := n) (KA := KA) (KB := KB) N) := by
  have hpre : notAbsAt (n := n) (KA := KA) (KB := KB) N
      = (fun ω : (_ : ℕ) → TS n KA KB => ω N) ⁻¹' {t : TS n KA KB | t.st.1 ≠ ∅} := rfl
  rw [hpre]
  exact (measurable_pi_apply N) MeasurableSet.of_discrete

theorem measurable_absTime :
    Measurable (absTime : ((_ : ℕ) → TS n KA KB) → ℕ) := by
  refine measurable_firstIndex (D := fun k => {ω : (_ : ℕ) → TS n KA KB | (ω k).st.1 = ∅})
    fun k => ?_
  have hpre : {ω : (_ : ℕ) → TS n KA KB | (ω k).st.1 = ∅}
      = (fun ω : (_ : ℕ) → TS n KA KB => ω k) ⁻¹' {t : TS n KA KB | t.st.1 = ∅} := rfl
  rw [hpre]
  exact (measurable_pi_apply k) MeasurableSet.of_discrete

theorem lintegral_nat_eq_tsum_measure_gt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℕ} (hf : Measurable f) :
    (∫⁻ ω, (f ω : ℝ≥0∞) ∂μ) = ∑' j : ℕ, μ {ω | j < f ω} := by
  have hmset : ∀ j : ℕ, MeasurableSet {ω | j < f ω} := fun j =>
    hf (MeasurableSet.of_discrete (s := {k : ℕ | j < k}))
  have hpt : ∀ ω : Ω,
      ((f ω : ℕ) : ℝ≥0∞) = ∑' j : ℕ, Set.indicator {ω | j < f ω} (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    have hzero : ∀ j ∉ Finset.range (f ω),
        Set.indicator {ω | j < f ω} (1 : Ω → ℝ≥0∞) ω = 0 := by
      intro j hj
      have hnm : ω ∉ {ω' : Ω | j < f ω'} := by
        simpa using Finset.mem_range.not.1 hj
      rw [Set.indicator_of_notMem hnm (1 : Ω → ℝ≥0∞)]
    rw [tsum_eq_sum hzero]
    have hone : ∀ j ∈ Finset.range (f ω),
        Set.indicator {ω | j < f ω} (1 : Ω → ℝ≥0∞) ω = 1 := by
      intro j hj
      have hm : ω ∈ {ω' : Ω | j < f ω'} := Finset.mem_range.1 hj
      rw [Set.indicator_of_mem hm (1 : Ω → ℝ≥0∞), Pi.one_apply]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  calc (∫⁻ ω, (f ω : ℝ≥0∞) ∂μ)
      = ∫⁻ ω, ∑' j : ℕ, Set.indicator {ω | j < f ω} (1 : Ω → ℝ≥0∞) ω ∂μ :=
        lintegral_congr hpt
    _ = ∑' j : ℕ, ∫⁻ ω, Set.indicator {ω | j < f ω} (1 : Ω → ℝ≥0∞) ω ∂μ :=
        lintegral_tsum fun j => (measurable_one.indicator (hmset j)).aemeasurable
    _ = ∑' j : ℕ, μ {ω | j < f ω} :=
        tsum_congr fun j => lintegral_indicator_one (hmset j)

theorem tsum_geom_poly_ne_top (m c : ℕ) :
    (∑' k : ℕ, ((c * (k + 1) : ℕ) : ℝ≥0∞) ^ m * ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ≠ ⊤ := by
  have hg : Summable fun k : ℕ => (k : ℝ) ^ m * (1 / 2 : ℝ) ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one m (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hg1 : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ m * (1 / 2 : ℝ) ^ (k + 1) :=
    (summable_nat_add_iff 1).2 hg
  have hsum : Summable fun k : ℕ => ((c * (k + 1) : ℕ) : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
    refine (hg1.mul_left (2 * (c : ℝ) ^ m)).congr fun k => ?_
    have hcast : ((c * (k + 1) : ℕ) : ℝ) = (c : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast, mul_pow]
    ring
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ((c * (k + 1) : ℕ) : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
    intro k
    positivity
  have hconv : ∀ k : ℕ,
      ((c * (k + 1) : ℕ) : ℝ≥0∞) ^ m * ENNReal.ofReal ((1 / 2 : ℝ) ^ k)
        = ENNReal.ofReal (((c * (k + 1) : ℕ) : ℝ) ^ m * (1 / 2 : ℝ) ^ k) := by
    intro k
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((c * (k + 1) : ℕ) : ℝ) ^ m),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp only [hconv]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ENNReal.ofReal_ne_top

theorem surv_antitone (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) {M N : ℕ}
    (hMN : M ≤ N) {s : TS n KA KB} (hw : WF s.st.1) :
    surv θA θB ρ πA πB N s ≤ surv θA θB ρ πA πB M s := by
  rw [surv_eq h, surv_eq h, mstep_indAbs h, mstep_indAbs h]
  have := absN_mono_le hθA hθB h.rho hMN hw
  linarith

theorem exists_horizon_pos (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ t : TS n KA KB, WF t.st.1 → surv θA θB ρ πA πB N₀ t ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀⟩ := uniform_horizon h hθA hθB
  refine ⟨N₀ + 1, Nat.succ_pos _, fun t hwt => ?_⟩
  exact le_trans (surv_antitone h hθA hθB (Nat.le_succ N₀) hwt) (hN₀ t hwt)

theorem lintegral_absTime_pow_lt_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (m : ℕ) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, (absTime ω : ℝ≥0∞) ^ m ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  classical
  obtain ⟨N₀, hN₀pos, hN₀⟩ := exists_horizon_pos h hθA hθB
  set μ := argTrajT θA θB ρ πA πB h s with hμ
  have hAm : ∀ k : ℕ, MeasurableSet (notAbsAt (n := n) (KA := KA) (KB := KB) (k * N₀)) :=
    fun k => measurableSet_notAbsAt _
  have hAmeas : ∀ k : ℕ, μ (notAbsAt (n := n) (KA := KA) (KB := KB) (k * N₀))
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    rw [hμ, notAbsAt, measure_not_absorbed h (k * N₀) s]
    exact ENNReal.ofReal_le_ofReal (surv_pow_le h hN₀ k hw)
  have hpt : ∀ ω, (absTime ω : ℝ≥0∞) ^ m
      ≤ 1 + ∑' k : ℕ, ((N₀ * (k + 1) : ℕ) : ℝ≥0∞) ^ m *
        Set.indicator (notAbsAt (k * N₀)) (1 : ((_ : ℕ) → TS n KA KB) → ℝ≥0∞) ω := by
    intro ω
    rcases Nat.eq_zero_or_pos (absTime ω) with h0 | h0
    · refine le_trans ?_ le_self_add
      rw [h0]
      cases m with
      | zero => simp
      | succ m => simp
    · have hSne : {k | (ω k).st.1 = ∅}.Nonempty := by
        by_contra hc
        rw [Set.not_nonempty_iff_eq_empty] at hc
        rw [absTime, hc, Nat.sInf_empty] at h0
        omega
      have hle : (absTime ω - 1) / N₀ * N₀ ≤ absTime ω - 1 := Nat.div_mul_le_self _ _
      have hmod := Nat.div_add_mod (absTime ω - 1) N₀
      have hlt := Nat.mod_lt (absTime ω - 1) hN₀pos
      have hexp : N₀ * ((absTime ω - 1) / N₀ + 1) = N₀ * ((absTime ω - 1) / N₀) + N₀ := by
        ring
      have hTle : absTime ω ≤ N₀ * ((absTime ω - 1) / N₀ + 1) := by omega
      have hmem : ω ∈ notAbsAt (n := n) (KA := KA) (KB := KB) ((absTime ω - 1) / N₀ * N₀) := by
        intro hc
        have hcc : absTime ω ≤ (absTime ω - 1) / N₀ * N₀ := Nat.sInf_le hc
        omega
      have hterm : ((N₀ * ((absTime ω - 1) / N₀ + 1) : ℕ) : ℝ≥0∞) ^ m ≤ ∑' j : ℕ,
          ((N₀ * (j + 1) : ℕ) : ℝ≥0∞) ^ m *
            Set.indicator (notAbsAt (j * N₀)) (1 : ((_ : ℕ) → TS n KA KB) → ℝ≥0∞) ω := by
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ((absTime ω - 1) / N₀))
        rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      refine le_trans (le_trans ?_ hterm) le_add_self
      exact pow_le_pow_left' (Nat.cast_le.2 hTle) m
  have hmeasind : ∀ k : ℕ, Measurable fun ω => ((N₀ * (k + 1) : ℕ) : ℝ≥0∞) ^ m *
      Set.indicator (notAbsAt (k * N₀)) (1 : ((_ : ℕ) → TS n KA KB) → ℝ≥0∞) ω :=
    fun k => (measurable_one.indicator (hAm k)).const_mul _
  have hint : (∫⁻ ω, 1 + ∑' k : ℕ, ((N₀ * (k + 1) : ℕ) : ℝ≥0∞) ^ m *
        Set.indicator (notAbsAt (k * N₀)) (1 : ((_ : ℕ) → TS n KA KB) → ℝ≥0∞) ω ∂μ)
      = 1 + ∑' k : ℕ, ((N₀ * (k + 1) : ℕ) : ℝ≥0∞) ^ m *
        μ (notAbsAt (n := n) (KA := KA) (KB := KB) (k * N₀)) := by
    rw [lintegral_add_left measurable_const, lintegral_one, measure_univ,
      lintegral_tsum fun k => (hmeasind k).aemeasurable]
    refine congrArg (fun x => 1 + x) (tsum_congr fun k => ?_)
    rw [lintegral_const_mul _ (measurable_one.indicator (hAm k)),
      lintegral_indicator_one (hAm k)]
  have hfin : (1 : ℝ≥0∞) + ∑' k : ℕ, ((N₀ * (k + 1) : ℕ) : ℝ≥0∞) ^ m *
      μ (notAbsAt (n := n) (KA := KA) (KB := KB) (k * N₀)) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ?_⟩
    refine ne_top_of_le_ne_top (tsum_geom_poly_ne_top m N₀) ?_
    refine ENNReal.tsum_le_tsum fun k => ?_
    gcongr
    exact hAmeas k
  refine ne_top_of_le_ne_top hfin ?_
  rw [← hint]
  exact lintegral_mono hpt

theorem lintegral_absTime_lt_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, (absTime ω : ℝ≥0∞) ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  have hm := lintegral_absTime_pow_lt_top h hθA hθB 1 hw
  simpa using hm

theorem integrable_absTime (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) :
    Integrable (fun ω => (absTime ω : ℝ)) (argTrajT θA θB ρ πA πB h s) := by
  refine ⟨((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
    measurable_absTime).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : ∀ ω : (_ : ℕ) → TS n KA KB,
      ‖((absTime ω : ℕ) : ℝ)‖ₑ = (absTime ω : ℝ≥0∞) := by
    intro ω
    rw [Real.enorm_eq_ofReal (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp only [henorm]
  exact lt_of_le_of_ne le_top (lintegral_absTime_lt_top h hθA hθB hw)

theorem lintegral_absTime_eq_tsum (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    (∫⁻ ω, (absTime ω : ℝ≥0∞) ∂(argTrajT θA θB ρ πA πB h s))
      = ∑' j : ℕ, argTrajT θA θB ρ πA πB h s {ω | j < absTime ω} :=
  lintegral_nat_eq_tsum_measure_gt _ measurable_absTime

end Rhone.Coalescent.BranchLengthMoments
