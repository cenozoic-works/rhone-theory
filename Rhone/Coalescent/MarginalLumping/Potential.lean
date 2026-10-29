/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.MarginalLumping.Product

/-! # The second-moment potential of the unkilled graph exists -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem mstep_const_mul (N : ℕ) (c : ℝ) (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (fun t => c * g t) s = c * mstep θA θB ρ πA πB N g s := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ, mstep_succ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]; ring

theorem tsum_mstep_step (h : Adm θA θB ρ πA πB) {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (s : TS n KA KB) :
    (∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g s))
      = ENNReal.ofReal (g s)
        + ∑ t' : TS n KA KB, ENNReal.ofReal (transS θA θB ρ πA πB s t')
            * ∑' k : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB k g t') := by
  have hterm : ∀ m : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB (m + 1) g s)
      = ∑ t' : TS n KA KB, ENNReal.ofReal (transS θA θB ρ πA πB s t')
          * ENNReal.ofReal (mstep θA θB ρ πA πB m g t') := by
    intro m
    rw [mstep_succ, ENNReal.ofReal_sum_of_nonneg
      (fun t' _ => mul_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t')
        (mstep_nonneg h m hg t'))]
    exact Finset.sum_congr rfl fun t' _ =>
      ENNReal.ofReal_mul (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t')
  rw [tsum_eq_zero_add' (f := fun k => ENNReal.ofReal (mstep θA θB ρ πA πB k g s))
    ENNReal.summable]
  congr 1
  simp only [hterm]
  rw [tsum_sum_comm]
  exact Finset.sum_congr rfl fun t' _ => ENNReal.tsum_mul_left

noncomputable def srcAB (ρ : ℝ) (t : TS n KA KB) : ℝ :=
  holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlkB t + holdB (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t

theorem srcAB_nonneg (hρ : 0 ≤ ρ) (t : TS n KA KB) : 0 ≤ srcAB ρ t :=
  add_nonneg (mul_nonneg (holdA_nonneg le_rfl le_rfl hρ _ t) (uBlkB_nonneg t))
    (mul_nonneg (holdB_nonneg le_rfl le_rfl hρ _ t) (uBlk_nonneg t))

noncomputable def wSum (ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (t : TS n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (mstep (0 : ℝ) 0 ρ πA πB k (srcAB ρ) t)

theorem closed_covAB : Closed (0 : ℝ) 0 ρ πA πB (CovAB (n := n) (KA := KA) (KB := KB)) :=
  closed_wf_coverAB

theorem exists_pot_bound :
    ∃ MA MB : ℝ, 0 ≤ MA ∧ 0 ≤ MB ∧ (∀ t : TS n KA KB, uBlk t ≤ MA)
      ∧ (∀ t : TS n KA KB, uBlkB t ≤ MB) := by
  obtain ⟨t₁, ht₁⟩ := Finite.exists_max fun t : TS n KA KB => uBlk t
  obtain ⟨t₂, ht₂⟩ := Finite.exists_max fun t : TS n KA KB => uBlkB t
  exact ⟨uBlk t₁, uBlkB t₂, uBlk_nonneg t₁, uBlkB_nonneg t₂, ht₁, ht₂⟩

theorem wSum_le_of_bounds (h : Adm (0 : ℝ) 0 ρ πA πB) {MA MB : ℝ} (hMA0 : 0 ≤ MA)
    (hMB0 : 0 ≤ MB) (hMA : ∀ t : TS n KA KB, uBlk t ≤ MA) (hMB : ∀ t : TS n KA KB, uBlkB t ≤ MB)
    {t : TS n KA KB} (hCt : CovAB t) :
    wSum ρ πA πB t ≤ ENNReal.ofReal (MB * uBlk t + MA * uBlkB t) := by
  have hgnn : ∀ x : TS n KA KB,
      0 ≤ MB * holdA (0 : ℝ) 0 ρ (cladeFam n) x + MA * holdB (0 : ℝ) 0 ρ (cladeFam n) x :=
    fun x => add_nonneg (mul_nonneg hMB0 (holdA_nonneg le_rfl le_rfl h.rho _ x))
      (mul_nonneg hMA0 (holdB_nonneg le_rfl le_rfl h.rho _ x))
  have hvnn : ∀ x : TS n KA KB, 0 ≤ MB * uBlk x + MA * uBlkB x :=
    fun x => add_nonneg (mul_nonneg hMB0 (uBlk_nonneg x)) (mul_nonneg hMA0 (uBlkB_nonneg x))
  have hv : ∀ x : TS n KA KB, CovAB x →
      MB * uBlk x + MA * uBlkB x
        = (MB * holdA (0 : ℝ) 0 ρ (cladeFam n) x + MA * holdB (0 : ℝ) 0 ρ (cladeFam n) x)
          + ∑ t', transS (0 : ℝ) 0 ρ πA πB x t' * (MB * uBlk t' + MA * uBlkB t') := by
    intro x hCx
    have hA := uBlk_step_covAB h hCx
    have hB := uBlkB_step_covAB h hCx
    have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB x t' * (MB * uBlk t' + MA * uBlkB t'))
        = MB * (∑ t', transS (0 : ℝ) 0 ρ πA πB x t' * uBlk t')
          + MA * (∑ t', transS (0 : ℝ) 0 ρ πA πB x t' * uBlkB t') := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t' _ => by ring
    rw [hsum, hA, hB]
    ring
  have hgg : ∀ x : TS n KA KB, srcAB ρ x
      ≤ MB * holdA (0 : ℝ) 0 ρ (cladeFam n) x + MA * holdB (0 : ℝ) 0 ρ (cladeFam n) x := by
    intro x
    have h1 : holdA (0 : ℝ) 0 ρ (cladeFam n) x * uBlkB x
        ≤ holdA (0 : ℝ) 0 ρ (cladeFam n) x * MB :=
      mul_le_mul_of_nonneg_left (hMB x) (holdA_nonneg le_rfl le_rfl h.rho _ x)
    have h2 : holdB (0 : ℝ) 0 ρ (cladeFam n) x * uBlk x
        ≤ holdB (0 : ℝ) 0 ρ (cladeFam n) x * MA :=
      mul_le_mul_of_nonneg_left (hMA x) (holdB_nonneg le_rfl le_rfl h.rho _ x)
    rw [srcAB]
    nlinarith [h1, h2]
  calc wSum ρ πA πB t
      ≤ ∑' k : ℕ, ENNReal.ofReal (mstep (0 : ℝ) 0 ρ πA πB k
          (fun x => MB * holdA (0 : ℝ) 0 ρ (cladeFam n) x
            + MA * holdB (0 : ℝ) 0 ρ (cladeFam n) x) t) :=
        ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (mstep_mono h k hgg t)
    _ ≤ ENNReal.ofReal (MB * uBlk t + MA * uBlkB t) :=
        tsum_ofReal_mstep_le h closed_covAB
          (g := fun x => MB * holdA (0 : ℝ) 0 ρ (cladeFam n) x
            + MA * holdB (0 : ℝ) 0 ρ (cladeFam n) x)
          (u := fun x => MB * uBlk x + MA * uBlkB x) hgnn hv hvnn hCt

theorem wSum_ne_top (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hCt : CovAB t) :
    wSum ρ πA πB t ≠ ⊤ := by
  obtain ⟨MA, MB, hMA0, hMB0, hMA, hMB⟩ := exists_pot_bound (n := n) (KA := KA) (KB := KB)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (wSum_le_of_bounds h hMA0 hMB0 hMA hMB hCt)

open Classical in
noncomputable def wAB (ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (t : TS n KA KB) : ℝ :=
  if CovAB t then (wSum ρ πA πB t).toReal else 0

theorem wAB_of_covAB {t : TS n KA KB} (hCt : CovAB t) :
    wAB ρ πA πB t = (wSum ρ πA πB t).toReal := by
  rw [wAB, ite_eq_left hCt]

theorem wAB_of_not_covAB {t : TS n KA KB} (hCt : ¬ CovAB t) : wAB ρ πA πB t = 0 := by
  rw [wAB, ite_eq_right hCt]

theorem wAB_nonneg (t : TS n KA KB) : 0 ≤ wAB ρ πA πB t := by
  rw [wAB]
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem wAB_step (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hCt : CovAB t) :
    wAB ρ πA πB t = srcAB ρ t + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * wAB ρ πA πB t' := by
  have hstep := tsum_mstep_step h (srcAB_nonneg h.rho) t
  have hterm : ∀ t' : TS n KA KB,
      ENNReal.ofReal (transS (0 : ℝ) 0 ρ πA πB t t') * wSum ρ πA πB t'
        = ENNReal.ofReal (transS (0 : ℝ) 0 ρ πA πB t t' * wAB ρ πA πB t') := by
    intro t'
    have hp : 0 ≤ transS (0 : ℝ) 0 ρ πA πB t t' :=
      transS_nonneg h.thA h.thB h.rho h.piA h.piB t t'
    by_cases hC' : CovAB t'
    · rw [wAB_of_covAB hC', ENNReal.ofReal_mul hp,
        ENNReal.ofReal_toReal (wSum_ne_top h hC')]
    · have hz : transS (0 : ℝ) 0 ρ πA πB t t' = 0 := closed_covAB t t' hCt hC'
      rw [hz, ENNReal.ofReal_zero, zero_mul, zero_mul, ENNReal.ofReal_zero]
  have hnn : ∀ t' ∈ (Finset.univ : Finset (TS n KA KB)),
      0 ≤ transS (0 : ℝ) 0 ρ πA πB t t' * wAB ρ πA πB t' :=
    fun t' _ => mul_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB t t') (wAB_nonneg t')
  have hval : wSum ρ πA πB t
      = ENNReal.ofReal (srcAB ρ t + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * wAB ρ πA πB t') := by
    rw [ENNReal.ofReal_add (srcAB_nonneg h.rho t) (Finset.sum_nonneg hnn),
      ENNReal.ofReal_sum_of_nonneg hnn]
    simp only [wSum] at hstep ⊢
    rw [hstep]
    exact congrArg _ (Finset.sum_congr rfl fun t' _ => hterm t')
  rw [wAB_of_covAB hCt, hval,
    ENNReal.toReal_ofReal (add_nonneg (srcAB_nonneg h.rho t) (Finset.sum_nonneg hnn))]

theorem tendsto_mstep_wAB_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB} (hCs : CovAB s) :
    Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N (wAB ρ πA πB) s) Filter.atTop
      (nhds 0) := by
  obtain ⟨MA, MB, hMA0, hMB0, hMA, hMB⟩ := exists_pot_bound (n := n) (KA := KA) (KB := KB)
  have hbound : ∀ t : TS n KA KB, wAB ρ πA πB t ≤ MB * uBlk t + MA * uBlkB t := by
    intro t
    by_cases hCt : CovAB t
    · rw [wAB_of_covAB hCt]
      have hle := wSum_le_of_bounds h hMA0 hMB0 hMA hMB hCt
      have hnn : 0 ≤ MB * uBlk t + MA * uBlkB t :=
        add_nonneg (mul_nonneg hMB0 (uBlk_nonneg t)) (mul_nonneg hMA0 (uBlkB_nonneg t))
      calc (wSum ρ πA πB t).toReal
          ≤ (ENNReal.ofReal (MB * uBlk t + MA * uBlkB t)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
        _ = MB * uBlk t + MA * uBlkB t := ENNReal.toReal_ofReal hnn
    · rw [wAB_of_not_covAB hCt]
      exact add_nonneg (mul_nonneg hMB0 (uBlk_nonneg t)) (mul_nonneg hMA0 (uBlkB_nonneg t))
  have hlow : ∀ N : ℕ, 0 ≤ mstep (0 : ℝ) 0 ρ πA πB N (wAB ρ πA πB) s :=
    fun N => mstep_nonneg h N (fun t => wAB_nonneg t) s
  have hup : ∀ N : ℕ, mstep (0 : ℝ) 0 ρ πA πB N (wAB ρ πA πB) s
      ≤ MB * mstep (0 : ℝ) 0 ρ πA πB N uBlk s + MA * mstep (0 : ℝ) 0 ρ πA πB N uBlkB s := by
    intro N
    have hm := mstep_mono h N hbound s
    rwa [mstep_add_fun, mstep_const_mul, mstep_const_mul] at hm
  have hlim : Filter.Tendsto
      (fun N => MB * mstep (0 : ℝ) 0 ρ πA πB N uBlk s
        + MA * mstep (0 : ℝ) 0 ρ πA πB N uBlkB s) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_mstep_uBlk_zero h hCs.1).const_mul MB
    have h2 := (tendsto_mstep_uBlkB_zero h hCs.1).const_mul MA
    simpa using h1.add h2
  exact squeeze_zero hlow hup hlim

theorem expected_LA_LB_eq (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB} (hCs : CovAB s) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
          ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
            * holdB (0 : ℝ) 0 ρ (cladeFam n) t) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (wAB ρ πA πB s) :=
  expected_LA_LB_eq_of_secondMoment h (fun _ hCt => wAB_step h hCt)
    (tendsto_mstep_wAB_zero h hCs) hCs

theorem exists_secondMoment_unkilled (h : Adm (0 : ℝ) 0 ρ πA πB) :
    ∃ w : TS n KA KB → ℝ,
      (∀ t, CovAB t → w t = (holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlkB t
          + holdB (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t)
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t')
      ∧ (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
            ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
          + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
              * holdB (0 : ℝ) 0 ρ (cladeFam n) t) ω
              ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
        = ENNReal.ofReal (w ⟨initT n KA KB⟩) :=
  ⟨wAB ρ πA πB, fun _ hCt => wAB_step h hCt, expected_LA_LB_eq h covAB_initT⟩

theorem lintegral_branchLen_mul_ne_top_unkilled (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩)) ≠ ⊤ := by
  have hsum := expected_LA_LB_eq h (covAB_initT (n := n) (KA := KA) (KB := KB))
  have hle : (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      ≤ ENNReal.ofReal (wAB ρ πA πB ⟨initT n KA KB⟩) := by
    rw [← hsum]
    exact le_self_add
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Rhone.Coalescent.MarginalLumping
