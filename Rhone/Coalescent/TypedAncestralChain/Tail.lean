/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Sampling

/-! # The absorption time has a geometric tail -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem mstep_add (M N : ℕ) (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB (M + N) g s
      = mstep θA θB ρ πA πB M (mstep θA θB ρ πA πB N g) s := by
  induction M generalizing s with
  | zero => rw [Nat.zero_add, mstep_zero]
  | succ M ih =>
    rw [Nat.succ_add, mstep_succ, mstep_succ]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]

theorem mstep_const (h : Adm θA θB ρ πA πB) (N : ℕ) (c : ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (fun _ => c) s = c := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ]
    simp only [ih]
    rw [← Finset.sum_mul, sum_transS h.sumA h.sumB s, one_mul]

theorem mstep_of_nonpos {s : TS n KA KB} (hz : ¬ 0 < dtotS θA θB ρ s) (N : ℕ)
    (g : TS n KA KB → ℝ) : mstep θA θB ρ πA πB N g s = g s := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ]
    have hval : ∀ t : TS n KA KB, transS θA θB ρ πA πB s t
        * mstep θA θB ρ πA πB N g t
        = if t = s then mstep θA θB ρ πA πB N g t else 0 := by
      intro t
      rw [transS_of_nonpos hz]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun t _ => hval t,
      Finset.sum_ite_eq' Finset.univ s (fun t => mstep θA θB ρ πA πB N g t),
      ite_eq_left (Finset.mem_univ s), ih]

theorem transS_eq_zero_of_not_wf {s t : TS n KA KB} (hw : WF s.st.1) (ht : ¬ WF t.st.1) :
    transS θA θB ρ πA πB s t = 0 := by
  have hne : t.st ≠ s.st := fun hc => ht (by rw [hc]; exact hw)
  by_cases hd : 0 < dtot θA θB ρ s.st.1
  · rw [transS, transT_of_dtot_pos hd]
    have hz : stepT θA θB ρ πA πB (fun t' => if t' = t.st then 1 else 0) s.st = 0 := by
      have hcoal : ∀ p ∈ s.st.1, ∀ q ∈ s.st.1.erase p,
          ((coalL s.st.1 p q, s.st.2.1, s.st.2.2) : TSt n KA KB) ≠ t.st := by
        intro p hp q hq hc
        exact ht (by rw [← hc]; exact hw.coal hp (Finset.mem_of_mem_erase hq))
      have hmA : ∀ p ∈ carA s.st.1, ∀ i : Fin KA,
          ((mutAL s.st.1 p, setT s.st.2.1 p.1 i, s.st.2.2) : TSt n KA KB) ≠ t.st := by
        intro p hp i hc
        exact ht (by rw [← hc]; exact hw.mutA (carA_subset _ hp))
      have hmB : ∀ p ∈ carB s.st.1, ∀ j : Fin KB,
          ((mutBL s.st.1 p, s.st.2.1, setT s.st.2.2 p.2 j) : TSt n KA KB) ≠ t.st := by
        intro p hp j hc
        exact ht (by rw [← hc]; exact hw.mutB (carB_subset _ hp))
      have hrec : ∀ p ∈ carC s.st.1,
          ((recL s.st.1 p, s.st.2.1, s.st.2.2) : TSt n KA KB) ≠ t.st := by
        intro p hp hc
        obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
        exact ht (by rw [← hc]; exact hw.recomb hpL h1 h2)
      have e1 : (∑ p ∈ s.st.1, ∑ q ∈ s.st.1.erase p,
          if ((coalL s.st.1 p q, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ite_eq_right (hcoal p hp q hq)
      have e2 : (∑ p ∈ carA s.st.1, ∑ i, πA i *
          if ((mutAL s.st.1 p, setT s.st.2.1 p.1 i, s.st.2.2) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun i _ => by
          rw [ite_eq_right (hmA p hp i), mul_zero]
      have e3 : (∑ p ∈ carB s.st.1, ∑ j, πB j *
          if ((mutBL s.st.1 p, s.st.2.1, setT s.st.2.2 p.2 j) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun j _ => by
          rw [ite_eq_right (hmB p hp j), mul_zero]
      have e4 : (∑ p ∈ carC s.st.1,
          if ((recL s.st.1 p, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun p hp => ite_eq_right (hrec p hp)
      rw [stepT, e1, e2, e3, e4]
      ring
    rw [hz, zero_div]
  · rw [transS, transT_of_dtot_nonpos hd, ite_eq_right hne]

noncomputable def indAbs (t : TS n KA KB) : ℝ := if t.st.1 = ∅ then 1 else 0

noncomputable def indNot (t : TS n KA KB) : ℝ := if t.st.1 = ∅ then 0 else 1

theorem indNot_nonneg (t : TS n KA KB) : 0 ≤ indNot t := by
  rw [indNot]; split_ifs <;> norm_num

theorem indNot_le_one (t : TS n KA KB) : indNot t ≤ 1 := by
  rw [indNot]; split_ifs <;> norm_num

noncomputable def surv (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ)
    (s : TS n KA KB) : ℝ := mstep θA θB ρ πA πB N indNot s

theorem surv_nonneg (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    0 ≤ surv θA θB ρ πA πB N s :=
  mstep_nonneg h N (fun t => indNot_nonneg t) s

theorem surv_le_one (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    surv θA θB ρ πA πB N s ≤ 1 := by
  have hle : surv θA θB ρ πA πB N s ≤ mstep θA θB ρ πA πB N (fun _ => (1 : ℝ)) s := by
    refine mstep_mono h N (fun t => indNot_le_one t) s
  rwa [mstep_const h N 1 s] at hle

theorem surv_of_absorbed {s : TS n KA KB} (hs : s.st.1 = ∅) (N : ℕ) :
    surv θA θB ρ πA πB N s = 0 := by
  have hz : ¬ 0 < dtotS θA θB ρ s := by
    have : dtotS θA θB ρ s = 0 := by rw [dtotS, hs, dtot_empty]
    rw [this]
    exact lt_irrefl 0
  rw [surv, mstep_of_nonpos hz, indNot, ite_eq_left hs]

theorem mstep_le_mul (h : Adm θA θB ρ πA πB) (N : ℕ) {g : TS n KA KB → ℝ} {c : ℝ}
    (hgc : ∀ t, WF t.st.1 → g t ≤ c * indNot t)
    {s : TS n KA KB} (hw : WF s.st.1) :
    mstep θA θB ρ πA πB N g s ≤ c * surv θA θB ρ πA πB N s := by
  induction N generalizing s with
  | zero => exact hgc s hw
  | succ N ih =>
    have key : ∀ t : TS n KA KB, transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N g t
        ≤ c * (transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N indNot t) := by
      intro t
      by_cases hwt : WF t.st.1
      · have h2 : 0 ≤ transS θA θB ρ πA πB s t :=
          transS_nonneg h.thA h.thB h.rho h.piA h.piB s t
        calc transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N g t
            ≤ transS θA θB ρ πA πB s t * (c * mstep θA θB ρ πA πB N indNot t) :=
              mul_le_mul_of_nonneg_left (ih hwt) h2
          _ = c * (transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N indNot t) := by ring
      · rw [transS_eq_zero_of_not_wf hw hwt, zero_mul, zero_mul, mul_zero]
    calc mstep θA θB ρ πA πB (N + 1) g s
        = ∑ t, transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N g t :=
          mstep_succ θA θB ρ πA πB N g s
      _ ≤ ∑ t, c * (transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N indNot t) :=
          Finset.sum_le_sum fun t _ => key t
      _ = c * surv θA θB ρ πA πB (N + 1) s := by
          rw [← Finset.mul_sum, surv, mstep_succ]

theorem mstep_indAbs (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N indAbs s = absN θA θB ρ N s.st.1 := by
  have hdeg : ∀ (M : ℕ) (L : Finset (Lin n)), L ≠ ∅ → dtot θA θB ρ L = 0 →
      absN θA θB ρ M L = 0 := by
    intro M
    induction M with
    | zero => intro L hL _; rw [absN, ite_eq_right hL]
    | succ M _ =>
      intro L hL hd
      rw [absN, ite_eq_right hL, hd, div_zero]
  have hemp : ∀ (M : ℕ), absN θA θB ρ M (∅ : Finset (Lin n)) = 1 := by
    intro M; cases M <;> simp [absN]
  induction N generalizing s with
  | zero =>
    rw [mstep_zero, indAbs, absN]
  | succ N ih =>
    have hsum : (∑ t : TS n KA KB, transS θA θB ρ πA πB s t * absN θA θB ρ N t.st.1)
        = ∑ u : TSt n KA KB, transT θA θB ρ πA πB s.st u * absN θA θB ρ N u.1 :=
      Fintype.sum_equiv (TS.equivTSt (n := n) (KA := KA) (KB := KB)) _ _ (fun _ => rfl)
    rw [mstep_succ]
    simp only [ih]
    rw [hsum]
    by_cases hd : 0 < dtot θA θB ρ s.st.1
    · have hL : s.st.1 ≠ ∅ := by
        intro hc
        rw [hc, dtot_empty] at hd
        exact absurd hd (lt_irrefl 0)
      have key : (∑ u : TSt n KA KB,
          transT θA θB ρ πA πB s.st u * absN θA θB ρ N u.1)
          = stepT θA θB ρ πA πB (fun u => absN θA θB ρ N u.1) s.st / dtot θA θB ρ s.st.1 := by
        have hlin : (∑ u : TSt n KA KB, absN θA θB ρ N u.1
            * stepT θA θB ρ πA πB (fun t' => if t' = u then 1 else 0) s.st)
            = stepT θA θB ρ πA πB (fun u => absN θA θB ρ N u.1) s.st := by
          rw [stepT_sum]
          congr 1
          funext t'
          simp
        rw [← hlin, Finset.sum_div]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [transT_of_dtot_pos hd]
        ring
      rw [key, stepT_of_fst h.sumA h.sumB, absN, ite_eq_right hL]
    · have hz : dtot θA θB ρ s.st.1 = 0 := by
        rcases lt_trichotomy (dtot θA θB ρ s.st.1) 0 with hlt | heq | hgt
        · exact absurd (dtot_nonneg h.thA h.thB h.rho s.st.1) (not_le.2 hlt)
        · exact heq
        · exact absurd hgt hd
      have hval : ∀ u : TSt n KA KB, transT θA θB ρ πA πB s.st u * absN θA θB ρ N u.1
          = if u = s.st then absN θA θB ρ N u.1 else 0 := by
        intro u
        rw [transT_of_dtot_nonpos hd]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun u _ => hval u,
        Finset.sum_ite_eq' Finset.univ s.st (fun u => absN θA θB ρ N u.1),
        ite_eq_left (Finset.mem_univ s.st)]
      by_cases hL : s.st.1 = ∅
      · rw [hL, hemp, hemp]
      · rw [hdeg N _ hL hz, hdeg (N + 1) _ hL hz]

theorem mstep_sub (N : ℕ) (g₁ g₂ : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (fun t => g₁ t - g₂ t) s
      = mstep θA θB ρ πA πB N g₁ s - mstep θA θB ρ πA πB N g₂ s := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ, mstep_succ, mstep_succ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]; ring

theorem surv_eq (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    surv θA θB ρ πA πB N s = 1 - mstep θA θB ρ πA πB N indAbs s := by
  have hfun : (indNot : TS n KA KB → ℝ) = fun t => (1 : ℝ) - indAbs t := by
    funext t
    rw [indNot, indAbs]
    split_ifs <;> norm_num
  rw [surv, hfun, mstep_sub, mstep_const h N 1 s]

theorem absN_mono_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {M N : ℕ} (hMN : M ≤ N)
    {L : Finset (Lin n)} (hw : WF L) : absN θA θB ρ M L ≤ absN θA θB ρ N L := by
  have hm : Monotone (fun N => absN θA θB ρ N L) := by
    refine monotone_nat_of_le_succ fun N => ?_
    rw [absN_eq_hitN N L, absN_eq_hitN (N + 1) L]
    exact hitN_mono hθA hθB hρ (fun _ : Fin 1 => zero_le_one) (fun _ : Fin 1 => zero_le_one) N hw
  exact hm hMN

theorem uniform_horizon (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    ∃ N₀ : ℕ, ∀ s : TS n KA KB, WF s.st.1 → surv θA θB ρ πA πB N₀ s ≤ 1 / 2 := by
  have hex : ∀ s : TS n KA KB, ∃ N : ℕ,
      WF s.st.1 → (1 : ℝ) / 2 ≤ mstep θA θB ρ πA πB N indAbs s := by
    intro s
    by_cases hw : WF s.st.1
    · have h1 : (⨆ N, absN θA θB ρ N s.st.1) = 1 := absProb_eq_one hθA hθB h.rho hw
      have h2 : (1 : ℝ) / 2 < ⨆ N, absN θA θB ρ N s.st.1 := by rw [h1]; norm_num
      obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup h2
      exact ⟨N, fun _ => by rw [mstep_indAbs h N s]; exact hN.le⟩
    · exact ⟨0, fun hc => absurd hc hw⟩
  choose Nf hNf using hex
  refine ⟨Finset.univ.sup Nf, fun s hw => ?_⟩
  have hmono : mstep θA θB ρ πA πB (Nf s) indAbs s
      ≤ mstep θA θB ρ πA πB (Finset.univ.sup Nf) indAbs s := by
    rw [mstep_indAbs h, mstep_indAbs h]
    exact absN_mono_le hθA hθB h.rho (Finset.le_sup (Finset.mem_univ s)) hw
  rw [surv_eq h]
  have := hNf s hw
  linarith

theorem surv_pow_le (h : Adm θA θB ρ πA πB) {N₀ : ℕ}
    (hN₀ : ∀ t : TS n KA KB, WF t.st.1 → surv θA θB ρ πA πB N₀ t ≤ 1 / 2) (k : ℕ)
    {s : TS n KA KB} (hw : WF s.st.1) :
    surv θA θB ρ πA πB (k * N₀) s ≤ (1 / 2) ^ k := by
  induction k generalizing s with
  | zero =>
    rw [Nat.zero_mul, pow_zero, surv, mstep_zero]
    exact indNot_le_one s
  | succ k ih =>
    have harith : (k + 1) * N₀ = N₀ + k * N₀ := by ring
    have hgc : ∀ t : TS n KA KB, WF t.st.1 →
        surv θA θB ρ πA πB (k * N₀) t ≤ (1 / 2) ^ k * indNot t := by
      intro t hwt
      by_cases hab : t.st.1 = ∅
      · rw [surv_of_absorbed hab, indNot, ite_eq_left hab, mul_zero]
      · rw [indNot, ite_eq_right hab, mul_one]
        exact ih hwt
    have hstep : surv θA θB ρ πA πB (N₀ + k * N₀) s
        ≤ (1 / 2) ^ k * surv θA θB ρ πA πB N₀ s := by
      rw [surv, mstep_add]
      exact mstep_le_mul h N₀ hgc hw
    have hpos : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
    calc surv θA θB ρ πA πB ((k + 1) * N₀) s
        = surv θA θB ρ πA πB (N₀ + k * N₀) s := by rw [harith]
      _ ≤ (1 / 2) ^ k * surv θA θB ρ πA πB N₀ s := hstep
      _ ≤ (1 / 2) ^ k * (1 / 2) := mul_le_mul_of_nonneg_left (hN₀ s hw) hpos
      _ = (1 / 2) ^ (k + 1) := by ring

noncomputable def absTime (ω : (_ : ℕ) → TS n KA KB) : ℕ := sInf {k | (ω k).st.1 = ∅}

theorem measure_not_absorbed (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    argTrajT θA θB ρ πA πB h s {ω | (ω N).st.1 ≠ ∅}
      = ENNReal.ofReal (surv θA θB ρ πA πB N s) := by
  have hms : MeasurableSet {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅} := by
    have hpre : MeasurableSet ((fun ω : (_ : ℕ) → TS n KA KB => ω N) ⁻¹'
        {t : TS n KA KB | t.st.1 ≠ ∅}) :=
      (measurable_pi_apply N) MeasurableSet.of_discrete
    exact hpre
  have hfun : (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (indNot (ω N)))
      = Set.indicator {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅} 1 := by
    funext ω
    by_cases hc : (ω N).st.1 = ∅
    · have hc2 : ω ∉ {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅} := by simpa using hc
      rw [Set.indicator_of_notMem hc2, indNot, ite_eq_left hc, ENNReal.ofReal_zero]
    · have hc2 : ω ∈ {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅} := hc
      rw [Set.indicator_of_mem hc2, Pi.one_apply, indNot, ite_eq_right hc, ENNReal.ofReal_one]
  rw [surv, ← lintegral_argTrajT h N (fun t => indNot_nonneg t) s, hfun,
    lintegral_indicator_one hms]

theorem measure_absTime_gt (h : Adm θA θB ρ πA πB) {N₀ : ℕ}
    (hN₀ : ∀ t : TS n KA KB, WF t.st.1 → surv θA θB ρ πA πB N₀ t ≤ 1 / 2) (k : ℕ)
    {s : TS n KA KB} (hw : WF s.st.1) :
    argTrajT θA θB ρ πA πB h s {ω | k * N₀ < absTime ω} ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hsub : {ω : (_ : ℕ) → TS n KA KB | k * N₀ < absTime ω}
      ⊆ {ω : (_ : ℕ) → TS n KA KB | (ω (k * N₀)).st.1 ≠ ∅} := by
    intro ω hω hc
    exact absurd (Nat.sInf_le (show k * N₀ ∈ {m | (ω m).st.1 = ∅} from hc)) (not_le.2 hω)
  calc argTrajT θA θB ρ πA πB h s {ω | k * N₀ < absTime ω}
      ≤ argTrajT θA θB ρ πA πB h s {ω | (ω (k * N₀)).st.1 ≠ ∅} := measure_mono hsub
    _ = ENNReal.ofReal (surv θA θB ρ πA πB (k * N₀) s) := measure_not_absorbed h _ s
    _ ≤ ENNReal.ofReal ((1 / 2) ^ k) :=
        ENNReal.ofReal_le_ofReal (surv_pow_le h hN₀ k hw)

theorem absN_nonneg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ)
    {L : Finset (Lin n)} (hw : WF L) : 0 ≤ absN θA θB ρ N L := by
  rw [absN_eq_hitN N L, hitN_eq_fitN N hw (clean_one_allele L)]
  exact fitN_nonneg hθA hθB hρ (fun _ : Fin 1 => zero_le_one) (fun _ : Fin 1 => zero_le_one) N _

theorem absN_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ)
    {L : Finset (Lin n)} (hw : WF L) : absN θA θB ρ N L ≤ 1 := by
  rw [absN_eq_hitN N L]
  exact hitN_le_one hθA hθB hρ (fun _ : Fin 1 => zero_le_one) (by simp)
    (fun _ : Fin 1 => zero_le_one) (by simp) N hw

theorem measure_eval_absorbed (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) (N : ℕ) :
    argTrajT θA θB ρ πA πB h s {ω | ω N ∈ {t : TS n KA KB | t.st.1 = ∅}}
      = ENNReal.ofReal (absN θA θB ρ N s.st.1) := by
  have hms : MeasurableSet {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅} := by
    have hpre : MeasurableSet ((fun ω : (_ : ℕ) → TS n KA KB => ω N) ⁻¹'
        {t : TS n KA KB | t.st.1 ≠ ∅}) :=
      (measurable_pi_apply N) MeasurableSet.of_discrete
    exact hpre
  have hcompl : {ω : (_ : ℕ) → TS n KA KB | ω N ∈ {t : TS n KA KB | t.st.1 = ∅}}
      = {ω : (_ : ℕ) → TS n KA KB | (ω N).st.1 ≠ ∅}ᶜ := by
    ext ω
    simp
  have hx0 : 0 ≤ absN θA θB ρ N s.st.1 := absN_nonneg hθA hθB h.rho N hw
  have hx1 : absN θA θB ρ N s.st.1 ≤ 1 := absN_le_one hθA hθB h.rho N hw
  rw [hcompl, prob_compl_eq_one_sub hms, measure_not_absorbed h N s, surv_eq h,
    mstep_indAbs h N s, ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one,
    ENNReal.sub_sub_cancel (by simp) (ENNReal.ofReal_le_one.2 hx1)]

theorem measure_absorbed_ever (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hw : WF s.st.1) :
    argTrajT θA θB ρ πA πB h s {ω | ∃ k, (ω k).st.1 = ∅} = 1 := by
  have hset : {ω : (_ : ℕ) → TS n KA KB | ∃ k, (ω k).st.1 = ∅}
      = {ω : (_ : ℕ) → TS n KA KB | ∃ k, ω k ∈ {t : TS n KA KB | t.st.1 = ∅}} := rfl
  rw [hset, measure_ever_eq_iSup h absorbing_absorbed s]
  have hval : ∀ N, argTrajT θA θB ρ πA πB h s {ω | ω N ∈ {t : TS n KA KB | t.st.1 = ∅}}
      = ENNReal.ofReal (absN θA θB ρ N s.st.1) :=
    fun N => measure_eval_absorbed h hθA hθB hw N
  simp only [hval]
  rw [← ofReal_iSup_of_monotone (f := fun N => absN θA θB ρ N s.st.1)
      (fun M N hMN => absN_mono_le hθA hθB h.rho hMN hw)
      (fun N => absN_le_one hθA hθB h.rho N hw),
    absProb_eq_one hθA hθB h.rho hw, ENNReal.ofReal_one]

end Rhone.Coalescent.TypedAncestralChain
