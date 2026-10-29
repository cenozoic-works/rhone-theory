/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SecondMoments.Weights
public import Rhone.Coalescent.BranchLengthMoments.Length

/-! # `E[L_A²]` for the unkilled ancestral recombination graph -/

@[expose] public section

namespace Rhone.Coalescent.SecondMoments

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def qpot (k : ℕ) : ℝ := 4 * ∑ i ∈ Finset.range (k - 1), (1 : ℝ) / (i + 1) ^ 2

@[simp] theorem qpot_zero : qpot 0 = 0 := by simp [qpot]

@[simp] theorem qpot_one : qpot 1 = 0 := by simp [qpot]

theorem qpot_nonneg (k : ℕ) : 0 ≤ qpot k := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
  positivity

theorem qpot_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) : qpot k = 0 := by
  interval_cases k
  · exact qpot_zero
  · exact qpot_one

theorem qpot_succ_succ (m : ℕ) : qpot (m + 2) = qpot (m + 1) + 4 / (m + 1) ^ 2 := by
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [qpot, qpot, h1, h2, Finset.sum_range_succ]
  ring

noncomputable def w2f (k : ℕ) : ℝ := hpot k ^ 2 + qpot k

theorem w2f_nonneg (k : ℕ) : 0 ≤ w2f k := by
  have h1 : (0 : ℝ) ≤ hpot k ^ 2 := sq_nonneg _
  have h2 := qpot_nonneg k
  rw [w2f]
  linarith

theorem w2f_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) : w2f k = 0 := by
  rw [w2f, hpot_eq_zero_of_le_one hk, qpot_eq_zero_of_le_one hk]
  ring

theorem hpot_pos_of_two_le {k : ℕ} (hk : 2 ≤ k) : 0 < hpot k := by
  rw [hpot]
  refine mul_pos (by norm_num) (Finset.sum_pos (fun i _ => by positivity) ⟨0, ?_⟩)
  exact Finset.mem_range.2 (by omega)

theorem w2f_key (k : ℕ) :
    ((k * (k - 1) : ℕ) : ℝ) * (w2f k - w2f (k - 1))
      = 2 * (2 * (if 2 ≤ k then (k : ℝ) else 0) * hpot k) := by
  match k with
  | 0 => norm_num
  | 1 => norm_num
  | (m + 2) =>
    have h1 : m + 2 - 1 = m + 1 := by omega
    rw [h1, w2f, w2f, hpot_succ_succ m, qpot_succ_succ m,
      ite_eq_left (by omega : 2 ≤ m + 2)]
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem stepArg_w2f {L : Finset (Lin n)} (hw : WF L) :
    stepArg ρ (fun M => w2f ((partA M).card)) L
      = dtotArg ρ L * w2f ((partA L).card)
        - 2 * (2 * (if 2 ≤ (partA L).card then (((partA L).card : ℕ) : ℝ) else 0)
            * hpot ((partA L).card)) := by
  have hk := kingman_generator (ρ := ρ) hw fun P => w2f P.card
  have hinner : ∀ S ∈ partA L, ∀ T ∈ (partA L).erase S,
      w2f ((mergeP (partA L) S T).card) - w2f ((partA L).card)
        = w2f ((partA L).card - 1) - w2f ((partA L).card) := by
    intro S hS T hT
    have hc := card_mergeP_partA hw hS hT
    rw [show (mergeP (partA L) S T).card = (partA L).card - 1 by omega]
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl (hinner S hS),
    sum_pairs_const] at hk
  have hkey := w2f_key ((partA L).card)
  linear_combination hk - hkey

noncomputable def w2 (t : TS n KA KB) : ℝ := w2f (nblk t)

theorem w2_nonneg (t : TS n KA KB) : 0 ≤ w2 t := w2f_nonneg _

theorem w2_eq_zero_of_le_one {t : TS n KA KB} (ht : nblk t ≤ 1) : w2 t = 0 :=
  w2f_eq_zero_of_le_one ht

theorem nblk_le_one_of_uBlk_zero {t : TS n KA KB} (h0 : uBlk t = 0) : nblk t ≤ 1 := by
  by_contra hc
  have hpos : 0 < hpot (nblk t) := hpot_pos_of_two_le (by omega)
  rw [uBlk] at h0
  linarith

theorem w2_eq_zero_of_uBlk_zero {t : TS n KA KB} (h0 : uBlk t = 0) : w2 t = 0 :=
  w2_eq_zero_of_le_one (nblk_le_one_of_uBlk_zero h0)

theorem w2_step (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hw : WF t.st.1) :
    w2 t = (2 * rBlk t * uBlk t) / rateTotS (0 : ℝ) 0 ρ t
      + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w2 t' := by
  have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
  rw [dtotS] at h2
  by_cases hd : 0 < dtot (0 : ℝ) 0 ρ t.st.1
  · have hDpos : (0 : ℝ) < dtotArg ρ t.st.1 := by
      rw [← dtot_zero_eq_dtotArg]
      exact hd
    have hDne : dtotArg ρ t.st.1 ≠ 0 := ne_of_gt hDpos
    have hstep : stepT (0 : ℝ) 0 ρ πA πB
        (fun t' : TSt n KA KB => w2 (⟨t'⟩ : TS n KA KB)) t.st
        = stepArg ρ (fun M => w2f ((partA M).card)) t.st.1 := by
      rw [← stepU_zero_eq_stepArg]
      exact stepT_of_fst h.sumA h.sumB (fun L => w2f ((partA L).card)) t.st
    have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w2 t')
        = (dtotArg ρ t.st.1 * w2f ((partA t.st.1).card)
            - 2 * (2 * (if 2 ≤ (partA t.st.1).card
              then (((partA t.st.1).card : ℕ) : ℝ) else 0)
              * hpot ((partA t.st.1).card))) / dtotArg ρ t.st.1 := by
      rw [sum_transS_eq hd, hstep, stepArg_w2f hw, dtot_zero_eq_dtotArg]
    have hrate : rateTotS (0 : ℝ) 0 ρ t = dtotArg ρ t.st.1 / 2 := by
      rw [dtot_zero_eq_dtotArg] at h2
      linarith
    rw [hsum, hrate, w2, uBlk_eq, rBlk_eq, nblk]
    simp only [w2f]
    field_simp
    ring
  · have hz : ¬ 0 < dtotS (0 : ℝ) 0 ρ t := hd
    have hzz : dtot (0 : ℝ) 0 ρ t.st.1 = 0 :=
      le_antisymm (not_lt.1 hd) (dtot_nonneg le_rfl le_rfl h.rho _)
    have hrate : rateTotS (0 : ℝ) 0 ρ t = 0 := by
      rw [hzz] at h2
      linarith
    rw [sum_transS_of_nonpos hz, hrate, div_zero, zero_add]

theorem tendsto_mstep_w2_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) :
    Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N w2 s) Filter.atTop (nhds 0) := by
  obtain ⟨t₂, ht₂⟩ := Finite.exists_max fun t : TS n KA KB => w2 t
  have hmeasF : ∀ N : ℕ, Measurable
      fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (w2 (ω N)) :=
    fun N => (Measurable.of_discrete
      (f := fun t : TS n KA KB => ENNReal.ofReal (w2 t))).comp (measurable_pi_apply N)
  have hbound : ∀ N : ℕ, (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (w2 (ω N)))
      ≤ᵐ[argTrajT (0 : ℝ) 0 ρ πA πB h s] fun _ => ENNReal.ofReal (w2 t₂) := by
    intro N
    filter_upwards with ω
    exact ENNReal.ofReal_le_ofReal (ht₂ (ω N))
  have hbint : (∫⁻ _ω : (_ : ℕ) → TS n KA KB, ENNReal.ofReal (w2 t₂)
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  have haelim : ∀ᵐ ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s),
      Filter.Tendsto (fun N => ENNReal.ofReal (w2 (ω N))) Filter.atTop (nhds 0) := by
    filter_upwards [ae_eventually_uBlk_zero h hw] with ω hω
    obtain ⟨N₁, hN₁⟩ := hω
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
    filter_upwards [Filter.eventually_ge_atTop N₁] with N hN
    rw [w2_eq_zero_of_uBlk_zero (hN₁ N hN), ENNReal.ofReal_zero]
  have hdct := tendsto_lintegral_of_dominated_convergence
    (μ := argTrajT (0 : ℝ) 0 ρ πA πB h s) (fun _ => ENNReal.ofReal (w2 t₂))
    hmeasF hbound hbint haelim
  rw [lintegral_zero] at hdct
  have hval : ∀ N : ℕ, (∫⁻ ω, ENNReal.ofReal (w2 (ω N))
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (mstep (0 : ℝ) 0 ρ πA πB N w2 s) :=
    fun N => lintegral_argTrajT h N (fun t => w2_nonneg t) s
  simp only [hval] at hdct
  have hconv := (ENNReal.tendsto_toReal (by simp)).comp hdct
  simp only [Function.comp_def, ENNReal.toReal_zero] at hconv
  refine hconv.congr fun N => ?_
  exact ENNReal.toReal_ofReal (mstep_nonneg h N (fun t => w2_nonneg t) s)

theorem lintegral_branchLen_sq_w2 (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) (hcov : coverA s.st.1 = Finset.univ) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
          ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
            * holdA (0 : ℝ) 0 ρ (cladeFam n) t) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (w2 s) := by
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdA (0 : ℝ) 0 ρ (cladeFam n) t :=
    holdA_nonneg le_rfl le_rfl h.rho (cladeFam n)
  have hfg : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ) →
      uBlk t = holdA (0 : ℝ) 0 ρ (cladeFam n) t
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t' := by
    intro t hCt
    rw [holdA, ← rBlk_eq_rA hCt.1 hCt.2]
    exact uBlk_step h hCt.1
  have hfw : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ) →
      w2 t = (holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t
          + holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t)
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w2 t' := by
    intro t hCt
    have hstep := w2_step h hCt.1
    have harith : (2 * rBlk t * uBlk t) / rateTotS (0 : ℝ) 0 ρ t
        = holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t
          + holdA (0 : ℝ) 0 ρ (cladeFam n) t * uBlk t := by
      rw [holdA, ← rBlk_eq_rA hCt.1 hCt.2]
      ring
    rw [hstep, harith]
  have hmain := lintegral_occAll_mul_eq h closed_wf_cover hgnn hgnn
    (fun t => uBlk_nonneg t) (fun t => uBlk_nonneg t) hfg hfg
    (fun t hCt => tendsto_mstep_uBlk_zero h hCt.1) (fun t hCt => tendsto_mstep_uBlk_zero h hCt.1)
    hfw (tendsto_mstep_w2_zero h hw) ⟨hw, hcov⟩
  rw [← hmain]
  rfl

theorem expected_total_length_sq (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
          ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
        + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
            * holdA (0 : ℝ) 0 ρ (cladeFam n) t) ω
            ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      = ENNReal.ofReal ((2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) ^ 2
          + 4 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1) ^ 2) := by
  have hinit : (⟨initT n KA KB⟩ : TS n KA KB).st.1 = fullState n := rfl
  have hw : WF (⟨initT n KA KB⟩ : TS n KA KB).st.1 := by
    rw [hinit]
    exact fullState_wf
  have hcov : coverA (⟨initT n KA KB⟩ : TS n KA KB).st.1 = Finset.univ := by
    rw [hinit]
    exact coverA_fullState
  rw [lintegral_branchLen_sq_w2 h hw hcov, w2, nblk_initT, w2f, hpot, qpot]

theorem w2f_two : w2f 2 = 8 := by
  rw [w2f, hpot, qpot]
  norm_num

theorem w2f_three : w2f 3 = 14 := by
  rw [w2f, hpot, qpot]
  norm_num [Finset.sum_range_succ]

theorem closed_wf_coverAB : Closed (0 : ℝ) 0 ρ πA πB
    fun t : TS n KA KB => WF t.st.1 ∧ coverA t.st.1 = Finset.univ
      ∧ coverB t.st.1 = Finset.univ := by
  intro s t hs ht
  refine transS_eq_zero_of_move
    (P := fun L => WF L ∧ coverA L = Finset.univ ∧ coverB L = Finset.univ) ?_ ?_ hs ht
  · intro p hp q hq
    exact ⟨hs.1.coal hp (Finset.mem_of_mem_erase hq),
      by rw [coverA_coal hp hq]; exact hs.2.1, by rw [coverB_coal hp hq]; exact hs.2.2⟩
  · intro p hp
    obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
    exact ⟨hs.1.recomb hpL h1 h2, by rw [coverA_rec hs.1 hpL]; exact hs.2.1,
      by rw [coverB_rec hs.1 hpL]; exact hs.2.2⟩

theorem expected_LA_lB_eq_of_potential (h : Adm (0 : ℝ) 0 ρ πA πB)
    (G : Finset (Finset (Fin n))) {uB w : TS n KA KB → ℝ}
    (hBnn : ∀ t, 0 ≤ uB t)
    (hfB : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ
        ∧ coverB t.st.1 = Finset.univ) →
      uB t = holdB (0 : ℝ) 0 ρ G t + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uB t')
    (hlB : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ
        ∧ coverB t.st.1 = Finset.univ) →
      Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N uB t) Filter.atTop (nhds 0))
    (hfw : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ
        ∧ coverB t.st.1 = Finset.univ) →
      w t = (holdA (0 : ℝ) 0 ρ (cladeFam n) t * uB t + holdB (0 : ℝ) 0 ρ G t * uBlk t)
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t')
    {s : TS n KA KB}
    (hlw : Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N w s) Filter.atTop (nhds 0))
    (hw : WF s.st.1) (hcovA : coverA s.st.1 = Finset.univ)
    (hcovB : coverB s.st.1 = Finset.univ) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω * branchLenB (0 : ℝ) 0 ρ G ω
          ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA (0 : ℝ) 0 ρ (cladeFam n) t
            * holdB (0 : ℝ) 0 ρ G t) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (w s) := by
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdA (0 : ℝ) 0 ρ (cladeFam n) t :=
    holdA_nonneg le_rfl le_rfl h.rho (cladeFam n)
  have hunn : ∀ t : TS n KA KB, 0 ≤ holdB (0 : ℝ) 0 ρ G t :=
    holdB_nonneg le_rfl le_rfl h.rho G
  have hfg : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ
      ∧ coverB t.st.1 = Finset.univ) →
      uBlk t = holdA (0 : ℝ) 0 ρ (cladeFam n) t
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t' := by
    intro t hCt
    rw [holdA, ← rBlk_eq_rA hCt.1 hCt.2.1]
    exact uBlk_step h hCt.1
  have hmain := lintegral_occAll_mul_eq h closed_wf_coverAB hgnn hunn
    (fun t => uBlk_nonneg t) hBnn hfg hfB
    (fun t hCt => tendsto_mstep_uBlk_zero h hCt.1) hlB hfw hlw ⟨hw, hcovA, hcovB⟩
  rw [← hmain]
  rfl

end Rhone.Coalescent.SecondMoments
