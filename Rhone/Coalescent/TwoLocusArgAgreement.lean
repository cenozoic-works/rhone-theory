/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusArg
public import Rhone.Coalescent.FullARGTwoSample

/-!
# Paired-state exits of the recombination graph chain give the two-locus value

Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Filter Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy
open scoped ENNReal Topology

section Process

variable {S : Type*} [MeasurableSpace S]

theorem pathLaw_real_stayedIn_succ_le (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {c : ℝ} (hc : ∀ s ∈ A, (P.step s).real A ≤ c) (x : S) (n : ℕ) :
    (P.pathLaw x).real (IntervalProcess.stayedIn A (n + 1)) ≤
      c * (P.pathLaw x).real (IntervalProcess.stayedIn A n) := by
  have hsn := IntervalProcess.stayedIn_measurableSet_piLE hA n
  have hsn' := IntervalProcess.stayedIn_measurableSet hA n
  have hevA : MeasurableSet {ω : ℕ → S | ω (n + 1) ∈ A} := hA.preimage (measurable_pi_apply _)
  have hsplit : IntervalProcess.stayedIn A (n + 1) =
      IntervalProcess.stayedIn A n ∩ {ω | ω (n + 1) ∈ A} := by
    ext ω
    simp only [IntervalProcess.stayedIn, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro hω
      exact ⟨fun k hk => hω k (by omega), hω (n + 1) le_rfl⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact h1 k (by omega)
      · have : k = n + 1 := by omega
        rw [this]
        exact h2
  have hmass : Measurable fun ω : ℕ → S => (P.step (ω n)).real A :=
    ((P.step.measurable_coe hA).ennreal_toReal).comp (measurable_pi_apply n)
  have hmassI : Integrable (fun ω : ℕ → S => (P.step (ω n)).real A) (P.pathLaw x) :=
    Integrable.of_bound hmass.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have h2 : (P.pathLaw x).real (IntervalProcess.stayedIn A n ∩ {ω | ω (n + 1) ∈ A}) =
      ∫ ω in IntervalProcess.stayedIn A n, (P.step (ω n)).real A ∂P.pathLaw x := by
    have hone : ∫ ω in IntervalProcess.stayedIn A n,
        A.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        ∫ ω in IntervalProcess.stayedIn A n, ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂P.step (ω n)
          ∂P.pathLaw x :=
      P.setIntegral_eval_succ x n (measurable_const.indicator hA) (M := 1)
        (fun s => by
          by_cases hs : s ∈ A
          · rw [Set.indicator_of_mem hs, abs_one]
          · rw [Set.indicator_of_notMem hs, abs_zero]
            exact zero_le_one) hsn
    have hleft : ∫ ω in IntervalProcess.stayedIn A n,
        A.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        (P.pathLaw x).real (IntervalProcess.stayedIn A n ∩ {ω | ω (n + 1) ∈ A}) := by
      have : (fun ω : ℕ → S => A.indicator (fun _ => (1 : ℝ)) (ω (n + 1))) =
          {ω : ℕ → S | ω (n + 1) ∈ A}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp [Set.indicator]
      rw [this, setIntegral_indicator hevA, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hleft, hone]
    refine setIntegral_congr_fun hsn' fun ω _ => ?_
    exact integral_indicator_one hA
  rw [hsplit, h2]
  calc ∫ ω in IntervalProcess.stayedIn A n, (P.step (ω n)).real A ∂P.pathLaw x
      ≤ ∫ _ω in IntervalProcess.stayedIn A n, c ∂P.pathLaw x :=
        setIntegral_mono_on hmassI.integrableOn (integrable_const c).integrableOn hsn'
          (fun ω hω => hc _ (hω n le_rfl))
    _ = c * (P.pathLaw x).real (IntervalProcess.stayedIn A n) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]

theorem pathLaw_real_stayedIn_le_pow (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ s ∈ A, (P.step s).real A ≤ c)
    (x : S) (n : ℕ) : (P.pathLaw x).real (IntervalProcess.stayedIn A n) ≤ c ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact measureReal_le_one
  | succ n ih =>
    rw [pow_succ']
    exact (pathLaw_real_stayedIn_succ_le P hA hc x n).trans (mul_le_mul_of_nonneg_left ih hc0)

theorem pathLaw_real_firstExit_of_stayedIn (P : DiscreteProcess S) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B)
    {h : S → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ s, |h s| ≤ M)
    (hstep : ∀ s ∈ A, ∫ y, A.indicator h y ∂P.step s + (P.step s).real B = h s)
    (x : S) (hx : x ∈ A)
    (hlim : Tendsto (fun n => (P.pathLaw x).real (IntervalProcess.stayedIn A n)) atTop (𝓝 0)) :
    (P.pathLaw x).real {ω | ∃ n, (∀ k ≤ n, ω k ∈ A) ∧ ω (n + 1) ∈ B} = h x := by
  set μ := P.pathLaw x with hμ
  let F : ℕ → Set (ℕ → S) := fun n => IntervalProcess.stayedIn A n ∩ {ω | ω (n + 1) ∈ B}
  let a : ℕ → ℝ := fun n => ∫ ω in IntervalProcess.stayedIn A n, h (ω n) ∂μ
  have hFm : ∀ n, MeasurableSet (F n) := fun n =>
    (IntervalProcess.stayedIn_measurableSet hA n).inter (hB.preimage (measurable_pi_apply _))
  have hzero : ∀ᵐ ω ∂μ, ω 0 ∈ A ∧ h (ω 0) = h x := by
    have hset : MeasurableSet {y : S | y ∈ A ∧ h y = h x} :=
      hA.inter (hh (measurableSet_singleton (h x)))
    apply ae_of_ae_map (μ := μ) (f := fun ω : ℕ → S => ω 0)
      (p := fun y => y ∈ A ∧ h y = h x) (measurable_pi_apply 0).aemeasurable
    rw [hμ, P.map_eval_zero]
    exact (ae_dirac_iff hset).mpr ⟨hx, rfl⟩
  have ha0 : a 0 = h x := by
    change ∫ ω in IntervalProcess.stayedIn A 0, h (ω 0) ∂μ = h x
    rw [← integral_indicator (IntervalProcess.stayedIn_measurableSet hA 0)]
    have : (IntervalProcess.stayedIn A 0).indicator (fun ω : ℕ → S => h (ω 0)) =ᵐ[μ]
        fun _ => h x := by
      filter_upwards [hzero] with ω hω
      have hmem : ω ∈ IntervalProcess.stayedIn A 0 := by
        intro k hk
        have : k = 0 := by omega
        rw [this]
        exact hω.1
      rw [Set.indicator_of_mem hmem, hω.2]
    rw [integral_congr_ae this, integral_const, probReal_univ, one_smul]
  have hsum : ∀ n, ∑ k ∈ Finset.range n, μ.real (F k) = h x - a n := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have := IntervalProcess.pathLaw_stayedIn_succ P hA hB hh hM hstep x n
      change a (n + 1) = a n - μ.real (F n) at this
      linarith
  have habs : ∀ n, |a n| ≤ M * μ.real (IntervalProcess.stayedIn A n) := by
    intro n
    have h1 : ‖∫ ω in IntervalProcess.stayedIn A n, h (ω n) ∂μ‖ ≤
        M * μ.real (IntervalProcess.stayedIn A n) :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun ω _ => by simpa using hM (ω n))
    rw [Real.norm_eq_abs] at h1
    exact h1
  have ha : Tendsto a atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by simpa using habs n)
    simpa using hlim.const_mul M
  have hpart : Tendsto (fun n => ∑ k ∈ Finset.range n, μ.real (F k)) atTop (𝓝 (h x)) := by
    have : Tendsto (fun n => h x - a n) atTop (𝓝 (h x - 0)) := tendsto_const_nhds.sub ha
    rw [sub_zero] at this
    exact this.congr fun n => (hsum n).symm
  have hhas : HasSum (fun k => μ.real (F k)) (h x) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun _ => measureReal_nonneg) _).mpr hpart
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    have key : ∀ n m, n < m → Disjoint (F n) (F m) := by
      intro n m hnm
      rw [Set.disjoint_left]
      intro ω hn hm
      exact Set.disjoint_left.mp hAB (hm.1 (n + 1) hnm) hn.2
    intro n m hnm
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · exact key n m hlt
    · exact (key m n hgt).symm
  have hE : {ω : ℕ → S | ∃ n, (∀ k ≤ n, ω k ∈ A) ∧ ω (n + 1) ∈ B} = ⋃ n, F n := by
    ext ω
    simp [F, IntervalProcess.stayedIn]
  rw [hE, measureReal_def, measure_iUnion hdisj hFm,
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  exact hhas.tsum_eq

end Process

theorem sum_comp_eq_sum_card_mul {ι : Type*} (T : Finset ι) (κ : ι → ℕ) (v : ℕ → ℝ) (N : ℕ)
    (hκ : ∀ i ∈ T, κ i < N) :
    (∑ i ∈ T, v (κ i)) = ∑ c ∈ range N, ((T.filter fun i => κ i = c).card : ℝ) * v c := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := range N)
    (fun i hi => Finset.mem_range.2 (hκ i hi))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    nsmul_eq_mul]

theorem sum_trans_mul_of_pos {n : ℕ} (θA θB ρ : ℝ) (f : Finset (Lin n) → ℝ)
    {L : Finset (Lin n)} (hL : 0 < dtot θA θB ρ L) :
    (∑ M : Finset (Lin n), trans θA θB ρ L M * f M) =
      stepU θA θB ρ f L / dtot θA θB ρ L := by
  have hterm : ∀ M : Finset (Lin n), trans θA θB ρ L M * f M =
      stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L * f M / dtot θA θB ρ L := by
    intro M
    rw [trans_of_pos M hL]
    ring
  rw [Finset.sum_congr rfl fun M _ => hterm M, ← Finset.sum_div, sum_stepU_indicator_mul]

def IsPaired (M : Finset (Lin 2)) : Prop :=
  M = {({0}, {0}), ({1}, {1})} ∨ M = {({0}, {1}), ({1}, {0})} ∨
  M = {({0}, {0}), ({1}, ∅), (∅, {1})} ∨ M = {({1}, {1}), ({0}, ∅), (∅, {0})} ∨
  M = {({0}, {1}), ({1}, ∅), (∅, {0})} ∨ M = {({1}, {0}), ({0}, ∅), (∅, {1})} ∨
  M = {({0}, ∅), ({1}, ∅), (∅, {0}), (∅, {1})}

instance IsPaired.instDecidable (M : Finset (Lin 2)) : Decidable (IsPaired M) := by
  unfold IsPaired
  infer_instance

def pairedClass (M : Finset (Lin 2)) : ℕ :=
  if IsPaired M then tt M else if na M ≤ 1 ∧ nb M ≤ 1 then 3
  else if na M = 2 ∧ nb M = 2 then 4 else 5

def coalCount (s : Finset (Lin 2)) (c : ℕ) : ℕ :=
  ∑ p ∈ s, ((s.erase p).filter fun q => pairedClass (coalL s p q) = c).card

def recCount (s : Finset (Lin 2)) (c : ℕ) : ℕ :=
  ((carC s).filter fun p => pairedClass (recL s p) = c).card

/-- Source: wilton_carmi_hobolth2015, Figure S1. -/
def coalTable (t c : ℕ) : ℕ :=
  if t = 2 then (if c = 3 then 2 else 0)
  else if t = 1 then (if c = 2 then 2 else if c = 5 then 4 else 0)
  else (if c = 1 then 8 else if c = 5 then 4 else 0)

/-- Source: wilton_carmi_hobolth2015, Figure S1. -/
def recTable (t c : ℕ) : ℕ :=
  if t = 2 then (if c = 1 then 2 else 0) else if t = 1 then (if c = 0 then 1 else 0) else 0

theorem IsPaired.counts {s : Finset (Lin 2)} (hs : IsPaired s) :
    na s = 2 ∧ nb s = 2 ∧ s.card + tt s = 4 := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 8000 in
theorem IsPaired.moveCounts {s : Finset (Lin 2)} (hs : IsPaired s) :
    ∀ c ∈ range 6, coalCount s c = coalTable (tt s) c ∧ recCount s c = recTable (tt s) c := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem pairedClass_of_isPaired {s : Finset (Lin 2)} (hs : IsPaired s) :
    pairedClass s = tt s := ite_eq_left hs

theorem IsPaired.tt_le {s : Finset (Lin 2)} (hs : IsPaired s) : tt s ≤ 2 := by
  have h := tt_le_na s
  rw [hs.counts.1] at h
  exact h

theorem pairedClass_lt (M : Finset (Lin 2)) : pairedClass M < 6 := by
  unfold pairedClass
  split_ifs with h1 h2 h3
  · have := h1.tt_le
    omega
  · norm_num
  · norm_num
  · norm_num

theorem stepU_pairedClass (ρ : ℝ) (v : ℕ → ℝ) (s : Finset (Lin 2)) :
    stepU 0 0 ρ (fun M => v (pairedClass M)) s =
      ∑ c ∈ range 6, ((coalCount s c : ℝ) + ρ * (recCount s c : ℝ)) * v c := by
  have h1 : (∑ p ∈ s, ∑ q ∈ s.erase p, v (pairedClass (coalL s p q))) =
      ∑ c ∈ range 6, (coalCount s c : ℝ) * v c := by
    rw [Finset.sum_congr rfl fun p _ => sum_comp_eq_sum_card_mul (s.erase p)
      (fun q => pairedClass (coalL s p q)) v 6 (fun q _ => pairedClass_lt _), Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coalCount, Nat.cast_sum, Finset.sum_mul]
  have h2 : (∑ p ∈ carC s, v (pairedClass (recL s p))) =
      ∑ c ∈ range 6, (recCount s c : ℝ) * v c :=
    sum_comp_eq_sum_card_mul (carC s) (fun p => pairedClass (recL s p)) v 6
      (fun p _ => pairedClass_lt _)
  rw [stepU, h1, h2, zero_mul, zero_mul, add_zero, add_zero, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- Source: wilton_carmi_hobolth2015, Figure S1. -/
noncomputable def pairedStepValue (ρ : ℝ) (v : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 2 then (2 * v 3 + 2 * ρ * v 1) / (2 + 2 * ρ)
  else if t = 1 then (2 * v 2 + 4 * v 5 + ρ * v 0) / (6 + ρ)
  else (8 * v 1 + 4 * v 5) / 12

/-- Source: wilton_carmi_hobolth2015, Figure S1. -/
theorem sum_trans_mul_pairedClass (ρ : ℝ) (hρ : 0 ≤ ρ) (v : ℕ → ℝ) {s : Finset (Lin 2)}
    (hs : IsPaired s) :
    (∑ M : Finset (Lin 2), trans 0 0 ρ s M * v (pairedClass M)) =
      pairedStepValue ρ v (tt s) := by
  obtain ⟨-, -, hcard⟩ := hs.counts
  have htt := hs.tt_le
  have hcount := hs.moveCounts
  have hd : dtot 0 0 ρ s = ((s.card * (s.card - 1) : ℕ) : ℝ) + ρ * ((tt s : ℕ) : ℝ) := by
    rw [dtot]
    ring
  have hU : stepU 0 0 ρ (fun M => v (pairedClass M)) s =
      ∑ c ∈ range 6, ((coalTable (tt s) c : ℝ) + ρ * (recTable (tt s) c : ℝ)) * v c := by
    rw [stepU_pairedClass]
    exact Finset.sum_congr rfl fun c hc => by rw [(hcount c hc).1, (hcount c hc).2]
  obtain h | h | h : tt s = 0 ∨ tt s = 1 ∨ tt s = 2 := by omega
  · have hc : s.card = 4 := by omega
    have hdv : dtot 0 0 ρ s = 12 := by
      rw [hd, hc, h]
      norm_num
    rw [sum_trans_mul_of_pos 0 0 ρ _ (by rw [hdv]; norm_num), hdv, hU, h]
    simp [Finset.sum_range_succ, coalTable, recTable, pairedStepValue]
  · have hc : s.card = 3 := by omega
    have hdv : dtot 0 0 ρ s = 6 + ρ := by
      rw [hd, hc, h]
      norm_num
    rw [sum_trans_mul_of_pos 0 0 ρ _ (by rw [hdv]; positivity), hdv, hU, h]
    simp [Finset.sum_range_succ, coalTable, recTable, pairedStepValue]
    ring
  · have hc : s.card = 2 := by omega
    have hdv : dtot 0 0 ρ s = 2 + 2 * ρ := by
      rw [hd, hc, h]
      norm_num
      ring
    rw [sum_trans_mul_of_pos 0 0 ρ _ (by rw [hdv]; positivity), hdv, hU, h]
    simp [Finset.sum_range_succ, coalTable, recTable, pairedStepValue]
    ring

/-- Source: wilton_carmi_hobolth2015, Figure S1. -/
theorem integral_kernel_pairedClass (ρ : ℝ) (hρ : 0 ≤ ρ) (f : ASt 2 → ℝ) (v : ℕ → ℝ)
    (hv : ∀ M : ASt 2, f M = v (pairedClass M)) {s : ASt 2} (hs : IsPaired s) :
    ∫ y, f y ∂(argChain 0 0 ρ le_rfl le_rfl hρ).kernel s = pairedStepValue ρ v (tt s) := by
  rw [FinChain.integral_kernel, FinChain.expect_apply,
    Finset.sum_congr rfl fun M _ => by rw [hv M]]
  exact sum_trans_mul_pairedClass ρ hρ v hs

def pairedSet : Set (ASt 2) := {L | IsPaired L}

def doneSet : Set (ASt 2) := {L | na L ≤ 1 ∧ nb L ≤ 1}

def strayedSet : Set (ASt 2) := {L | ¬ IsPaired L ∧ na L = 2 ∧ nb L = 2}

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
noncomputable def exitValue (ρ : ℝ) (c : ℕ) : ℝ :=
  if c ≤ 2 then IntervalProcess.twoLocusValue ρ c else if c = 3 then 1 else 0

theorem pairedSet_indicator (M : ASt 2) :
    pairedSet.indicator (1 : ASt 2 → ℝ) M = if pairedClass M ≤ 2 then 1 else 0 := by
  by_cases h : IsPaired M
  · rw [Set.indicator_of_mem (show M ∈ pairedSet from h), pairedClass_of_isPaired h,
      ite_eq_left h.tt_le]
    rfl
  · rw [Set.indicator_of_notMem (show M ∉ pairedSet from h)]
    unfold pairedClass
    rw [ite_eq_right h]
    split_ifs <;> first | rfl | omega

theorem strayedSet_indicator (M : ASt 2) :
    strayedSet.indicator (1 : ASt 2 → ℝ) M = if pairedClass M = 4 then 1 else 0 := by
  by_cases h : IsPaired M
  · rw [Set.indicator_of_notMem (show M ∉ strayedSet from fun hm => hm.1 h),
      pairedClass_of_isPaired h, ite_eq_right (by have := h.tt_le; omega)]
  · unfold pairedClass
    rw [ite_eq_right h]
    by_cases h2 : na M ≤ 1 ∧ nb M ≤ 1
    · rw [ite_eq_left h2, Set.indicator_of_notMem (show M ∉ strayedSet from fun hm => by
        have := hm.2.1
        omega), ite_eq_right (by norm_num)]
    · rw [ite_eq_right h2]
      by_cases h3 : na M = 2 ∧ nb M = 2
      · rw [ite_eq_left h3, Set.indicator_of_mem (show M ∈ strayedSet from ⟨h, h3⟩),
          ite_eq_left rfl]
        rfl
      · rw [ite_eq_right h3, Set.indicator_of_notMem (show M ∉ strayedSet from fun hm => h3 hm.2),
          ite_eq_right (by norm_num)]

theorem exit_indicator (ρ : ℝ) (M : ASt 2) :
    pairedSet.indicator (fun L : ASt 2 => IntervalProcess.twoLocusValue ρ (tt L)) M +
      doneSet.indicator (1 : ASt 2 → ℝ) M = exitValue ρ (pairedClass M) := by
  by_cases h : IsPaired M
  · rw [Set.indicator_of_mem (show M ∈ pairedSet from h),
      Set.indicator_of_notMem (show M ∉ doneSet from fun hm => by
        have := h.counts.1
        have := hm.1
        omega), pairedClass_of_isPaired h, exitValue, ite_eq_left h.tt_le, add_zero]
  · rw [Set.indicator_of_notMem (show M ∉ pairedSet from h), zero_add]
    unfold pairedClass exitValue
    rw [ite_eq_right h]
    by_cases h2 : na M ≤ 1 ∧ nb M ≤ 1
    · rw [ite_eq_left h2, Set.indicator_of_mem (show M ∈ doneSet from h2),
        ite_eq_right (by norm_num), ite_eq_left rfl]
      rfl
    · rw [ite_eq_right h2, Set.indicator_of_notMem (show M ∉ doneSet from h2)]
      split_ifs <;> first | rfl | omega

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem pairedStepValue_exitValue (ρ : ℝ) (hρ : 0 ≤ ρ) {t : ℕ} (ht : t ≤ 2) :
    pairedStepValue ρ (exitValue ρ) t = IntervalProcess.twoLocusValue ρ t := by
  have hD : ρ ^ 2 + 13 * ρ + 18 ≠ 0 := by positivity
  have h1 : (2 : ℝ) + 2 * ρ ≠ 0 := by positivity
  have h2 : (6 : ℝ) + ρ ≠ 0 := by positivity
  interval_cases t
  · simp only [pairedStepValue, exitValue, IntervalProcess.twoLocusValue]
    norm_num
    field_simp
    ring
  · simp only [pairedStepValue, exitValue, IntervalProcess.twoLocusValue]
    norm_num
    field_simp
    ring
  · simp only [pairedStepValue, exitValue, IntervalProcess.twoLocusValue]
    norm_num
    field_simp
    ring

theorem pairedStepValue_stay_le (ρ : ℝ) (hρ : 0 ≤ ρ) {t : ℕ} (ht : t ≤ 2) :
    pairedStepValue ρ (fun c => if c ≤ 2 then 1 else 0) t ≤ (ρ + 2) / (ρ + 3) := by
  have h3 : (0 : ℝ) < ρ + 3 := by positivity
  interval_cases t
  · simp only [pairedStepValue]
    norm_num
    rw [div_le_div_iff₀ (by norm_num) h3]
    nlinarith
  · simp only [pairedStepValue]
    norm_num
    rw [div_le_div_iff₀ (by positivity) h3]
    nlinarith
  · simp only [pairedStepValue]
    norm_num
    rw [div_le_div_iff₀ (by positivity) h3]
    nlinarith

theorem tendsto_pathLaw_stayedIn_pairedSet (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ASt 2) :
    Tendsto (fun n => ((argChain 0 0 ρ le_rfl le_rfl hρ).toProcess.pathLaw L).real
      (IntervalProcess.stayedIn pairedSet n)) atTop (𝓝 0) := by
  have h3 : (0 : ℝ) < ρ + 3 := by positivity
  have hc0 : (0 : ℝ) ≤ (ρ + 2) / (ρ + 3) := by positivity
  have hc1 : (ρ + 2) / (ρ + 3) < 1 := by
    rw [div_lt_one h3]
    linarith
  have hstep : ∀ s ∈ pairedSet,
      ((argChain 0 0 ρ le_rfl le_rfl hρ).toProcess.step s).real pairedSet ≤
        (ρ + 2) / (ρ + 3) := by
    intro s hs
    change ((argChain 0 0 ρ le_rfl le_rfl hρ).kernel s).real pairedSet ≤ _
    rw [← integral_indicator_one (MeasurableSet.of_discrete),
      integral_kernel_pairedClass ρ hρ _ (fun c => if c ≤ 2 then 1 else 0)
        pairedSet_indicator hs]
    exact pairedStepValue_stay_le ρ hρ (IsPaired.tt_le hs)
  refine squeeze_zero (fun n => measureReal_nonneg)
    (fun n => pathLaw_real_stayedIn_le_pow _ MeasurableSet.of_discrete hc0 hstep L n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)

theorem twoSampleStart_mem_pairedSet : twoSampleStart ∈ pairedSet := Or.inl rfl

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem argTraj_real_paired_exit (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (argTraj 0 0 ρ le_rfl le_rfl hρ twoSampleStart).real
      {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ doneSet} =
      IntervalProcess.twoLocusValue ρ 2 := by
  have hAB : Disjoint pairedSet doneSet := by
    rw [Set.disjoint_left]
    intro M hM hd
    have := (IsPaired.counts hM).1
    have := hd.1
    omega
  have h := pathLaw_real_firstExit_of_stayedIn (argChain 0 0 ρ le_rfl le_rfl hρ).toProcess
    (A := pairedSet) (B := doneSet) MeasurableSet.of_discrete MeasurableSet.of_discrete hAB
    (h := fun L : ASt 2 => IntervalProcess.twoLocusValue ρ (tt L)) Measurable.of_discrete
    (M := 1)
    (fun s => abs_le.2 ⟨by
        have := IntervalProcess.twoLocusValue_nonneg ρ hρ (tt s)
        linarith, IntervalProcess.twoLocusValue_le_one ρ hρ _⟩)
    (fun s hs => by
      change ∫ y, pairedSet.indicator (fun L : ASt 2 => IntervalProcess.twoLocusValue ρ (tt L)) y
        ∂(argChain 0 0 ρ le_rfl le_rfl hρ).kernel s +
          ((argChain 0 0 ρ le_rfl le_rfl hρ).kernel s).real doneSet = _
      rw [← integral_indicator_one (MeasurableSet.of_discrete),
        ← integral_add Integrable.of_finite Integrable.of_finite,
        integral_kernel_pairedClass ρ hρ _ (exitValue ρ) (exit_indicator ρ) hs]
      exact pairedStepValue_exitValue ρ hρ (IsPaired.tt_le hs))
    twoSampleStart twoSampleStart_mem_pairedSet
    (tendsto_pathLaw_stayedIn_pairedSet ρ hρ twoSampleStart)
  refine h.trans ?_
  change IntervalProcess.twoLocusValue ρ (tt twoSampleSet) = _
  rw [twoSampleStart_card.2]

theorem argTraj_real_paired_stray (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (argTraj 0 0 ρ le_rfl le_rfl hρ twoSampleStart).real
      {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ strayedSet} = 0 := by
  have hAB : Disjoint pairedSet strayedSet := by
    rw [Set.disjoint_left]
    intro M hM hd
    exact hd.1 hM
  exact pathLaw_real_firstExit_of_stayedIn (argChain 0 0 ρ le_rfl le_rfl hρ).toProcess
    (A := pairedSet) (B := strayedSet) MeasurableSet.of_discrete MeasurableSet.of_discrete hAB
    (h := fun _ : ASt 2 => (0 : ℝ)) Measurable.of_discrete (M := 0)
    (fun s => by simp)
    (fun s hs => by
      change ∫ y, pairedSet.indicator (fun _ : ASt 2 => (0 : ℝ)) y
        ∂(argChain 0 0 ρ le_rfl le_rfl hρ).kernel s +
          ((argChain 0 0 ρ le_rfl le_rfl hρ).kernel s).real strayedSet = 0
      rw [← integral_indicator_one (MeasurableSet.of_discrete),
        integral_kernel_pairedClass ρ hρ _ (fun c => if c = 4 then 1 else 0)
          strayedSet_indicator hs]
      simp [pairedStepValue])
    twoSampleStart twoSampleStart_mem_pairedSet
    (tendsto_pathLaw_stayedIn_pairedSet ρ hρ twoSampleStart)

theorem stays_or_first_leaves {S : Type*} (A : Set S) (ω : ℕ → S) (h0 : ω 0 ∈ A) (m : ℕ) :
    (∀ j ≤ m, ω j ∈ A) ∨ ∃ i < m, (∀ j ≤ i, ω j ∈ A) ∧ ω (i + 1) ∉ A := by
  induction m with
  | zero =>
    left
    intro j hj
    have : j = 0 := by omega
    rw [this]
    exact h0
  | succ m ih =>
    rcases ih with h | ⟨i, hi, h1, h2⟩
    · by_cases hm : ω (m + 1) ∈ A
      · left
        intro j hj
        rcases Nat.lt_or_ge j (m + 1) with hlt | hge
        · exact h j (by omega)
        · have : j = m + 1 := by omega
          rw [this]
          exact hm
      · exact Or.inr ⟨m, by omega, h, hm⟩
    · exact Or.inr ⟨i, by omega, h1, h2⟩

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem argTraj_agreement_event (ρ : ℝ) (hρ : 0 ≤ ρ) :
    argTraj 0 0 ρ le_rfl le_rfl hρ twoSampleStart
      {ω | ∃ k, (∀ j ≤ k, na (ω j) = 2 ∧ nb (ω j) = 2) ∧
        na (ω (k + 1)) ≤ 1 ∧ nb (ω (k + 1)) ≤ 1} =
      ENNReal.ofReal (IntervalProcess.twoLocusValue ρ 2) := by
  set μ := argTraj 0 0 ρ le_rfl le_rfl hρ twoSampleStart with hμ
  have hE7 : μ {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ doneSet} =
      ENNReal.ofReal (IntervalProcess.twoLocusValue ρ 2) := by
    rw [← argTraj_real_paired_exit ρ hρ, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hF : μ {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ strayedSet} = 0 := by
    have h := argTraj_real_paired_stray ρ hρ
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at h
    exact h.resolve_right (measure_ne_top _ _)
  have hZ : μ {ω : ℕ → ASt 2 | ω 0 ∉ pairedSet} = 0 := by
    have h0 := (argChain 0 0 ρ le_rfl le_rfl hρ).toProcess.map_eval_zero twoSampleStart
    have h1 : μ {ω : ℕ → ASt 2 | ω 0 ∉ pairedSet} =
        Measure.dirac twoSampleStart pairedSetᶜ := by
      rw [← h0, Measure.map_apply (measurable_pi_apply 0) MeasurableSet.of_discrete]
      rfl
    rw [h1, Measure.dirac_apply' _ MeasurableSet.of_discrete,
      Set.indicator_of_notMem (show twoSampleStart ∉ pairedSetᶜ from
        fun h => h twoSampleStart_mem_pairedSet)]
  apply le_antisymm
  · have hsub : {ω : ℕ → ASt 2 | ∃ k, (∀ j ≤ k, na (ω j) = 2 ∧ nb (ω j) = 2) ∧
        na (ω (k + 1)) ≤ 1 ∧ nb (ω (k + 1)) ≤ 1} ⊆
        ({ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ doneSet} ∪
          {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ strayedSet}) ∪
          {ω : ℕ → ASt 2 | ω 0 ∉ pairedSet} := by
      rintro ω ⟨k, hk, hdone⟩
      by_cases h0 : ω 0 ∈ pairedSet
      · left
        rcases stays_or_first_leaves pairedSet ω h0 k with h | ⟨i, hi, h1, h2⟩
        · exact Or.inl ⟨k, h, hdone⟩
        · exact Or.inr ⟨i, h1, h2, hk (i + 1) (by omega)⟩
      · exact Or.inr h0
    calc μ _ ≤ μ _ := measure_mono hsub
      _ ≤ μ {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ doneSet} +
            μ {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ strayedSet} +
          μ {ω : ℕ → ASt 2 | ω 0 ∉ pairedSet} :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ = ENNReal.ofReal (IntervalProcess.twoLocusValue ρ 2) := by
        rw [hF, hZ, add_zero, add_zero, hE7]
  · rw [← hE7]
    refine measure_mono ?_
    rintro ω ⟨k, hk, hdone⟩
    exact ⟨k, fun j hj => ⟨(IsPaired.counts (hk j hj)).1, (IsPaired.counts (hk j hj)).2.1⟩,
      hdone⟩

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem argTraj_two_sample_agreement (R : ℝ) (hR : 0 ≤ R)
    (x y : IntervalProcess.GenomicProbe) (hxy : x.val < y.val) :
    argTraj 0 0 (R * ((y.val : ℝ) - (x.val : ℝ))) le_rfl le_rfl
        (mul_nonneg hR (sub_nonneg.2 (by exact_mod_cast hxy.le))) twoSampleStart
      {ω | ∃ k, (∀ j ≤ k, na (ω j) = 2 ∧ nb (ω j) = 2) ∧
        na (ω (k + 1)) ≤ 1 ∧ nb (ω (k + 1)) ≤ 1} =
    IntervalProcess.fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} := by
  rw [argTraj_agreement_event, IntervalProcess.fullARG_two_sample_agreement_prob_explicit R hR
    x y hxy]
  rfl

end Rhone.Coalescent
