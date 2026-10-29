/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.BranchLengthMoments.Moments

/-! # Occupation times are the Dynkin solutions -/

@[expose] public section

namespace Rhone.Coalescent.BranchLengthMoments

open Finset TwoLocusGenealogy TypedAncestralChain LinearAlgebra.Recursion
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem ofReal_iSup_of_tendsto {f : ℕ → ℝ} {L : ℝ} (hmono : Monotone f)
    (hlim : Filter.Tendsto f Filter.atTop (nhds L)) :
    (⨆ N, ENNReal.ofReal (f N)) = ENNReal.ofReal L := by
  have h1 : Filter.Tendsto (fun N => ENNReal.ofReal (f N)) Filter.atTop
      (nhds (ENNReal.ofReal L)) := (ENNReal.continuous_ofReal.tendsto _).comp hlim
  have h2 : Filter.Tendsto (fun N => ENNReal.ofReal (f N)) Filter.atTop
      (nhds (⨆ N, ENNReal.ofReal (f N))) :=
    tendsto_atTop_iSup fun a b hab => ENNReal.ofReal_le_ofReal (hmono hab)
  exact tendsto_nhds_unique h2 h1

theorem sum_transS_of_nonpos {s : TS n KA KB} (hz : ¬ 0 < dtotS θA θB ρ s)
    (v : TS n KA KB → ℝ) : (∑ t, transS θA θB ρ πA πB s t * v t) = v s := by
  have hval : ∀ t : TS n KA KB, transS θA θB ρ πA πB s t * v t
      = if t = s then v t else 0 := by
    intro t
    rw [transS_of_nonpos hz]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun t _ => hval t,
    Finset.sum_ite_eq' Finset.univ s v, ite_eq_left (Finset.mem_univ s)]

theorem sum_transS_eq {s : TS n KA KB} (hd : 0 < dtot θA θB ρ s.st.1) (v : TS n KA KB → ℝ) :
    (∑ t, transS θA θB ρ πA πB s t * v t)
      = stepT θA θB ρ πA πB (fun t' => v ⟨t'⟩) s.st / dtot θA θB ρ s.st.1 := by
  have hsum : (∑ t : TS n KA KB, transS θA θB ρ πA πB s t * v t)
      = ∑ t' : TSt n KA KB, transT θA θB ρ πA πB s.st t' * v ⟨t'⟩ :=
    Fintype.sum_equiv (TS.equivTSt (n := n) (KA := KA) (KB := KB)) _ _ fun _ => rfl
  have hlin : (∑ t' : TSt n KA KB, v ⟨t'⟩ *
      stepT θA θB ρ πA πB (fun w => if w = t' then 1 else 0) s.st)
      = stepT θA θB ρ πA πB (fun t' => v ⟨t'⟩) s.st := by
    rw [stepT_sum]
    congr 1
    funext w
    simp
  rw [hsum, ← hlin, Finset.sum_div]
  exact Finset.sum_congr rfl fun t' _ => by rw [transT_of_dtot_pos hd]; ring

def Closed (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (C : TS n KA KB → Prop) : Prop :=
  ∀ s t, C s → ¬ C t → transS θA θB ρ πA πB s t = 0

theorem closed_wf : Closed θA θB ρ πA πB fun t : TS n KA KB => WF t.st.1 :=
  fun _ _ hs ht => transS_eq_zero_of_not_wf hs ht

theorem Closed.inter {C D : TS n KA KB → Prop} (hC : Closed θA θB ρ πA πB C)
    (hD : Closed θA θB ρ πA πB D) : Closed θA θB ρ πA πB fun t => C t ∧ D t := by
  intro s t hs ht
  by_cases hCt : C t
  · exact hD s t hs.2 fun hDt => ht ⟨hCt, hDt⟩
  · exact hC s t hs.1 hCt

theorem mstep_add_fun (N : ℕ) (g₁ g₂ : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (fun t => g₁ t + g₂ t) s
      = mstep θA θB ρ πA πB N g₁ s + mstep θA θB ρ πA πB N g₂ s := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ, mstep_succ, mstep_succ, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]; ring

theorem mstep_congr_closed {C : TS n KA KB → Prop} (hC : Closed θA θB ρ πA πB C)
    {g₁ g₂ : TS n KA KB → ℝ} (hg : ∀ t, C t → g₁ t = g₂ t) (N : ℕ)
    {s : TS n KA KB} (hs : C s) :
    mstep θA θB ρ πA πB N g₁ s = mstep θA θB ρ πA πB N g₂ s := by
  induction N generalizing s with
  | zero => exact hg s hs
  | succ N ih =>
    rw [mstep_succ, mstep_succ]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hCt : C t
    · rw [ih hCt]
    · rw [hC s t hs hCt, zero_mul, zero_mul]

theorem tendsto_surv_zero (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) :
    Filter.Tendsto (fun N => surv θA θB ρ πA πB N s) Filter.atTop (nhds 0) := by
  obtain ⟨N₀, hN₀pos, hN₀⟩ := exists_horizon_pos h hθA hθB
  have hdiv : Filter.Tendsto (fun N : ℕ => N / N₀) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨b * N₀, fun N hN => ?_⟩
    exact (Nat.le_div_iff_mul_le hN₀pos).2 hN
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (N / N₀)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hdiv
  refine squeeze_zero (fun N => surv_nonneg h N s) (fun N => ?_) hpow
  calc surv θA θB ρ πA πB N s
      ≤ surv θA θB ρ πA πB (N / N₀ * N₀) s :=
        surv_antitone h hθA hθB (Nat.div_mul_le_self N N₀) hw
    _ ≤ (1 / 2 : ℝ) ^ (N / N₀) := surv_pow_le h hN₀ (N / N₀) hw

theorem tendsto_mstep_zero (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {u : TS n KA KB → ℝ} (hu0 : ∀ t, WF t.st.1 → t.st.1 = ∅ → u t = 0)
    {s : TS n KA KB} (hw : WF s.st.1) :
    Filter.Tendsto (fun N => mstep θA θB ρ πA πB N u s) Filter.atTop (nhds 0) := by
  obtain ⟨t₀, ht₀⟩ := Finite.exists_max fun t : TS n KA KB => |u t|
  have hbound : ∀ t : TS n KA KB, WF t.st.1 → |u t| ≤ |u t₀| * indNot t := by
    intro t hwt
    by_cases hab : t.st.1 = ∅
    · rw [indNot, ite_eq_left hab, mul_zero, hu0 t hwt hab, abs_zero]
    · rw [indNot, ite_eq_right hab, mul_one]
      exact ht₀ t
  have habs : ∀ N, ‖mstep θA θB ρ πA πB N u s‖ ≤ |u t₀| * surv θA θB ρ πA πB N s := by
    intro N
    rw [Real.norm_eq_abs]
    exact le_trans (abs_mstep_le h N u s) (mstep_le_mul h N hbound hw)
  have hlim : Filter.Tendsto (fun N => |u t₀| * surv θA θB ρ πA πB N s) Filter.atTop
      (nhds 0) := by
    have hs := (tendsto_surv_zero h hθA hθB hw).const_mul |u t₀|
    simpa using hs
  exact squeeze_zero_norm habs hlim

theorem mstep_step_eq {C : TS n KA KB → Prop} (hC : Closed θA θB ρ πA πB C)
    {g u : TS n KA KB → ℝ}
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    (N : ℕ) {s : TS n KA KB} (hs : C s) :
    mstep θA θB ρ πA πB N u s
      = mstep θA θB ρ πA πB N g s + mstep θA θB ρ πA πB (N + 1) u s := by
  have h1 : mstep θA θB ρ πA πB N u s
      = mstep θA θB ρ πA πB N (fun t => g t + mstep θA θB ρ πA πB 1 u t) s := by
    refine mstep_congr_closed hC (fun t hCt => ?_) N hs
    rw [hu t hCt, mstep_succ]
    simp only [mstep_zero]
  rw [h1, mstep_add_fun, ← mstep_succ']

theorem sum_mstep_eq {C : TS n KA KB → Prop} (hC : Closed θA θB ρ πA πB C)
    {g u : TS n KA KB → ℝ}
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    (N : ℕ) {s : TS n KA KB} (hs : C s) :
    (∑ k ∈ Finset.range N, mstep θA θB ρ πA πB k g s)
      = u s - mstep θA θB ρ πA πB N u s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep := mstep_step_eq hC hu N hs
    linarith

theorem tsum_ofReal_mstep_of_tendsto (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    {s : TS n KA KB}
    (hlim0 : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N u s) Filter.atTop (nhds 0))
    (hs : C s) :
    (∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s)) = ENNReal.ofReal (u s) := by
  have hnn : ∀ k, 0 ≤ mstep θA θB ρ πA πB k g s := fun k => mstep_nonneg h k hg s
  have hpart : ∀ N, (∑ k ∈ Finset.range N, mstep θA θB ρ πA πB k g s)
      = u s - mstep θA θB ρ πA πB N u s := fun N => sum_mstep_eq hC hu N hs
  have hmono : Monotone fun N => u s - mstep θA θB ρ πA πB N u s := by
    intro M N hMN
    dsimp only
    rw [← hpart M, ← hpart N]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hnn k
    exact fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hMN)
  have hlim : Filter.Tendsto (fun N => u s - mstep θA θB ρ πA πB N u s) Filter.atTop
      (nhds (u s)) := by
    simpa using (tendsto_const_nhds (x := u s) (f := Filter.atTop (α := ℕ))).sub hlim0
  calc (∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s))
      = ⨆ N, ∑ k ∈ Finset.range N, ENNReal.ofReal (mstep θA θB ρ πA πB k g s) :=
        ENNReal.tsum_eq_iSup_nat
    _ = ⨆ N, ENNReal.ofReal (∑ k ∈ Finset.range N, mstep θA θB ρ πA πB k g s) :=
        iSup_congr fun N => (ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k).symm
    _ = ⨆ N, ENNReal.ofReal (u s - mstep θA θB ρ πA πB N u s) := by simp only [hpart]
    _ = ENNReal.ofReal (u s) := ofReal_iSup_of_tendsto hmono hlim

theorem tsum_ofReal_mstep_le (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    (hunn : ∀ t, 0 ≤ u t) {s : TS n KA KB} (hs : C s) :
    (∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s)) ≤ ENNReal.ofReal (u s) := by
  have hnn : ∀ k, 0 ≤ mstep θA θB ρ πA πB k g s := fun k => mstep_nonneg h k hg s
  have hpart : ∀ N, (∑ k ∈ Finset.range N, mstep θA θB ρ πA πB k g s)
      = u s - mstep θA θB ρ πA πB N u s := fun N => sum_mstep_eq hC hu N hs
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k, hpart N]
  exact ENNReal.ofReal_le_ofReal (by linarith [mstep_nonneg h N hunn s])

noncomputable def occAll (g : TS n KA KB → ℝ) (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (g (ω k))

noncomputable def killed (g : TS n KA KB → ℝ) (t : TS n KA KB) : ℝ :=
  if t.st.1 = ∅ then 0 else g t

theorem killed_nonneg {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) (t : TS n KA KB) :
    0 ≤ killed g t := by
  rw [killed]
  split_ifs
  · exact le_rfl
  · exact hg t

@[simp] theorem killed_of_absorbed {g : TS n KA KB → ℝ} {t : TS n KA KB} (ht : t.st.1 = ∅) :
    killed g t = 0 := by rw [killed, ite_eq_left ht]

theorem killed_of_not_absorbed {g : TS n KA KB → ℝ} {t : TS n KA KB} (ht : t.st.1 ≠ ∅) :
    killed g t = g t := by rw [killed, ite_eq_right ht]

noncomputable def occ (g : TS n KA KB → ℝ) (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  occAll (killed g) ω

theorem occ_eq_occAll_killed (g : TS n KA KB → ℝ) (ω : (_ : ℕ) → TS n KA KB) :
    occ g ω = occAll (killed g) ω := rfl

noncomputable def occUpTo (g : TS n KA KB → ℝ) (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, if k < absTime ω then ENNReal.ofReal (g (ω k)) else 0

theorem occAll_add {g₁ g₂ : TS n KA KB → ℝ} (h₁ : ∀ t, 0 ≤ g₁ t) (h₂ : ∀ t, 0 ≤ g₂ t)
    (ω : (_ : ℕ) → TS n KA KB) :
    occAll (fun t => g₁ t + g₂ t) ω = occAll g₁ ω + occAll g₂ ω := by
  rw [occAll, occAll, occAll, ← ENNReal.tsum_add]
  exact tsum_congr fun k => ENNReal.ofReal_add (h₁ _) (h₂ _)

theorem occAll_finsetSum {ι : Type*} (s : Finset ι) (g : ι → TS n KA KB → ℝ)
    (hg : ∀ i t, 0 ≤ g i t) (ω : (_ : ℕ) → TS n KA KB) :
    occAll (fun t => ∑ i ∈ s, g i t) ω = ∑ i ∈ s, occAll (g i) ω := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [occAll]
  · intro a u ha ih
    have hs : ∀ t : TS n KA KB, 0 ≤ ∑ i ∈ u, g i t :=
      fun t => Finset.sum_nonneg fun i _ => hg i t
    simp only [Finset.sum_insert ha]
    rw [occAll_add (hg a) hs, ih]

theorem measurable_occAll (g : TS n KA KB → ℝ) :
    Measurable (occAll (n := n) (KA := KA) (KB := KB) g) :=
  Measurable.tsum fun k =>
    (Measurable.of_discrete (f := fun t : TS n KA KB => ENNReal.ofReal (g t))).comp
      (measurable_pi_apply k)

theorem lintegral_occAll_eq_tsum (h : Adm θA θB ρ πA πB) {g : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (s : TS n KA KB) :
    (∫⁻ ω, occAll g ω ∂(argTrajT θA θB ρ πA πB h s))
      = ∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s) := by
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (g (ω k)))
      (argTrajT θA θB ρ πA πB h s) := by
    intro k
    exact ((Measurable.of_discrete
      (f := fun t : TS n KA KB => ENNReal.ofReal (g t))).comp
        (measurable_pi_apply k)).aemeasurable
  calc (∫⁻ ω, occAll g ω ∂(argTrajT θA θB ρ πA πB h s))
      = ∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal (g (ω k))
          ∂(argTrajT θA θB ρ πA πB h s) := rfl
    _ = ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal (g (ω k))
          ∂(argTrajT θA θB ρ πA πB h s) := lintegral_tsum hmeas
    _ = ∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s) :=
        tsum_congr fun k => lintegral_argTrajT h k hg s

theorem lintegral_occAll_eq (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    {s : TS n KA KB}
    (hlim0 : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N u s) Filter.atTop (nhds 0))
    (hs : C s) :
    (∫⁻ ω, occAll g ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) := by
  rw [lintegral_occAll_eq_tsum h hg s]
  exact tsum_ofReal_mstep_of_tendsto h hC hg hu hlim0 hs

theorem lintegral_occAll_le (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, C t → u t = g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    (hunn : ∀ t, 0 ≤ u t) {s : TS n KA KB} (hs : C s) :
    (∫⁻ ω, occAll g ω ∂(argTrajT θA θB ρ πA πB h s)) ≤ ENNReal.ofReal (u s) := by
  rw [lintegral_occAll_eq_tsum h hg s]
  exact tsum_ofReal_mstep_le h hC hg hu hunn hs

theorem lintegral_occ_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, WF t.st.1 → u t = killed g t + ∑ t', transS θA θB ρ πA πB t t' * u t')
    (hu0 : ∀ t, WF t.st.1 → t.st.1 = ∅ → u t = 0)
    {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, occ g ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) :=
  lintegral_occAll_eq h closed_wf (killed_nonneg hg) hu
    (tendsto_mstep_zero h hθA hθB hu0 hw) hw

theorem ae_lt_absTime_iff (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) :
    ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s), ∀ k : ℕ, (k < absTime ω ↔ (ω k).st.1 ≠ ∅) := by
  have hms : MeasurableSet {ω : (_ : ℕ) → TS n KA KB | ∃ k, (ω k).st.1 = ∅} := by
    have hun : {ω : (_ : ℕ) → TS n KA KB | ∃ k, (ω k).st.1 = ∅}
        = ⋃ k : ℕ, (fun ω : (_ : ℕ) → TS n KA KB => ω k) ⁻¹'
          {t : TS n KA KB | t.st.1 = ∅} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hun]
    exact MeasurableSet.iUnion fun k =>
      (measurable_pi_apply k) MeasurableSet.of_discrete
  have hever : ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s), ∃ k, (ω k).st.1 = ∅ := by
    rw [MeasureTheory.ae_iff]
    have hcompl : {ω : (_ : ℕ) → TS n KA KB | ¬ ∃ k, (ω k).st.1 = ∅}
        = {ω : (_ : ℕ) → TS n KA KB | ∃ k, (ω k).st.1 = ∅}ᶜ := rfl
    rw [hcompl, prob_compl_eq_one_sub hms, measure_absorbed_ever h hθA hθB hw, tsub_self]
  filter_upwards [hever, ae_stay h absorbing_absorbed s] with ω hex hstay k
  constructor
  · intro hk hc
    have hle : absTime ω ≤ k := Nat.sInf_le hc
    omega
  · intro hk
    by_contra hc
    have hle : absTime ω ≤ k := by omega
    obtain ⟨j, hj⟩ := hex
    have hmem0 : absTime ω ∈ {m : ℕ | (ω m).st.1 = ∅} := Nat.sInf_mem ⟨j, hj⟩
    have hmem : ω (absTime ω) ∈ {t : TS n KA KB | t.st.1 = ∅} := hmem0
    exact hk (stay_le (E := {t : TS n KA KB | t.st.1 = ∅}) hstay hle hmem)

theorem occUpTo_ae_eq_occ (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (g : TS n KA KB → ℝ) {s : TS n KA KB} (hw : WF s.st.1) :
    occUpTo g =ᵐ[argTrajT θA θB ρ πA πB h s] occ g := by
  filter_upwards [ae_lt_absTime_iff h hθA hθB hw] with ω hω
  refine tsum_congr fun k => ?_
  by_cases hk : k < absTime ω
  · rw [ite_eq_left hk, killed_of_not_absorbed ((hω k).1 hk)]
  · rw [ite_eq_right hk]
    have hab : (ω k).st.1 = ∅ := by
      by_contra hc
      exact hk ((hω k).2 hc)
    rw [killed_of_absorbed hab, ENNReal.ofReal_zero]

theorem lintegral_occUpTo_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu0 : ∀ t, WF t.st.1 → t.st.1 = ∅ → u t = 0)
    (hu2 : ∀ t, Transient t → u t - (∑ t', transS θA θB ρ πA πB t t' * u t') = g t)
    {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, occUpTo g ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) := by
  have hu : ∀ t : TS n KA KB, WF t.st.1 →
      u t = killed g t + ∑ t', transS θA θB ρ πA πB t t' * u t' := by
    intro t hwt
    by_cases htr : Transient t
    · have hst := hu2 t htr
      rw [killed_of_not_absorbed htr.2]
      linarith
    · have hab : t.st.1 = ∅ := by
        by_contra hc
        exact htr ⟨hwt, hc⟩
      rw [sum_transS_of_not_transient hwt htr u, hu0 t hwt hab, killed_of_absorbed hab]
      ring
  rw [lintegral_congr_ae (occUpTo_ae_eq_occ h hθA hθB g hw)]
  exact lintegral_occ_eq h hθA hθB hg hu hu0 hw

theorem existsUnique_occPotential (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (g : TS n KA KB → ℝ) :
    ∃! u : TS n KA KB → ℝ, (∀ t, ¬ Transient t → u t = killed g t)
      ∧ ∀ t, Transient t →
        u t - (∑ t', transS θA θB ρ πA πB t t' * u t') = killed g t :=
  existsUnique_dynkin h hθA hθB (killed g)

theorem expected_occupation_eq_dynkin (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) {s : TS n KA KB} (hw : WF s.st.1) :
    ∃! u : TS n KA KB → ℝ, ((∀ t, ¬ Transient t → u t = killed g t)
      ∧ ∀ t, Transient t →
        u t - (∑ t', transS θA θB ρ πA πB t t' * u t') = killed g t)
      ∧ (∫⁻ ω, occUpTo g ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_occPotential h hθA hθB g
  have hu0 : ∀ t : TS n KA KB, WF t.st.1 → t.st.1 = ∅ → u t = 0 := by
    intro t hwt hab
    rw [hu.1 t (fun hc => hc.2 hab), killed_of_absorbed hab]
  have hu2 : ∀ t : TS n KA KB, Transient t →
      u t - (∑ t', transS θA θB ρ πA πB t t' * u t') = g t := by
    intro t htr
    rw [hu.2 t htr, killed_of_not_absorbed htr.2]
  exact ⟨u, ⟨hu, lintegral_occUpTo_eq h hθA hθB hg hu0 hu2 hw⟩, fun v hv => huniq v hv.1⟩

end Rhone.Coalescent.BranchLengthMoments
