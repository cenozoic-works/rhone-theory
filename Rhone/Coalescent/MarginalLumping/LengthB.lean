/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.MarginalLumping.SecondLocusLumping
public import Rhone.Coalescent.SecondMoments.Square

/-! # The `B`-marginal potential, and `E[L_B] = 2 H_{n-1}` -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def swapT (t : TS n KA KB) : TS n KB KA := ⟨(swapL t.st.1, t.st.2.2, t.st.2.1)⟩

@[simp] theorem swapT_fst (t : TS n KA KB) : (swapT t).st.1 = swapL t.st.1 := rfl

theorem wf_swapT {t : TS n KA KB} (hw : WF t.st.1) : WF (swapT t).st.1 := wf_swapL hw

theorem coverA_swapT (t : TS n KA KB) : coverA (swapT t).st.1 = coverB t.st.1 :=
  coverA_swapL t.st.1

def nblkB (t : TS n KA KB) : ℕ := (partB t.st.1).card

theorem nblkB_eq_nblk_swapT (t : TS n KA KB) : nblkB t = nblk (swapT t) := by
  rw [nblkB, nblk, swapT_fst, partB_eq_partA_swapL]

theorem nblkB_le_card (t : TS n KA KB) : nblkB t ≤ t.st.1.card := by
  rw [nblkB_eq_nblk_swapT]
  have h := nblk_le_card (swapT t)
  rwa [swapT_fst, card_swapL] at h

noncomputable def rBlkB (t : TS n KA KB) : ℝ := if 2 ≤ nblkB t then (nblkB t : ℝ) else 0

theorem rBlkB_eq (t : TS n KA KB) :
    rBlkB t = if 2 ≤ (partB t.st.1).card then (((partB t.st.1).card : ℕ) : ℝ) else 0 := rfl

theorem rBlkB_nonneg (t : TS n KA KB) : 0 ≤ rBlkB t := by
  rw [rBlkB]
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

theorem rBlkB_eq_rBlk_swapT (t : TS n KA KB) : rBlkB t = rBlk (swapT t) := by
  rw [rBlkB, rBlk, nblkB_eq_nblk_swapT]

noncomputable def uBlkB (t : TS n KA KB) : ℝ := hpot (nblkB t)

theorem uBlkB_eq (t : TS n KA KB) : uBlkB t = hpot ((partB t.st.1).card) := rfl

theorem uBlkB_nonneg (t : TS n KA KB) : 0 ≤ uBlkB t := hpot_nonneg _

theorem uBlkB_eq_zero_of_le_one {t : TS n KA KB} (ht : nblkB t ≤ 1) : uBlkB t = 0 :=
  hpot_eq_zero_of_le_one ht

theorem uBlkB_eq_uBlk_swapT (t : TS n KA KB) : uBlkB t = uBlk (swapT t) := by
  rw [uBlkB, uBlk, nblkB_eq_nblk_swapT]

theorem rB_eq_rA_swapT (F : Finset (Finset (Fin n))) (t : TS n KA KB) :
    rB F t = rA F (swapT t) := by
  rw [rB, rA, swapT_fst, swapL_filter_snd, card_swapL]

theorem rBlkB_eq_rB {t : TS n KA KB} (hw : WF t.st.1) (hcov : coverB t.st.1 = Finset.univ) :
    rBlkB t = rB (cladeFam n) t := by
  rw [rBlkB_eq_rBlk_swapT, rB_eq_rA_swapT]
  exact rBlk_eq_rA (wf_swapT hw) (by rw [coverA_swapT]; exact hcov)

theorem card_mergeP_partB {L : Finset (Lin n)} (hw : WF L) {S T : Finset (Fin n)}
    (hS : S ∈ partB L) (hT : T ∈ (partB L).erase S) :
    (mergeP (partB L) S T).card + 1 = (partB L).card := by
  have hS' : S ∈ partA (swapL L) := by rwa [← partB_eq_partA_swapL]
  have hT' : T ∈ (partA (swapL L)).erase S := by rwa [← partB_eq_partA_swapL]
  rw [partB_eq_partA_swapL]
  exact card_mergeP_partA (wf_swapL hw) hS' hT'

theorem stepArg_hpotB {L : Finset (Lin n)} (hw : WF L) :
    stepArg ρ (fun M => hpot ((partB M).card)) L
      = dtotArg ρ L * hpot ((partB L).card)
        - 2 * (if 2 ≤ (partB L).card then (((partB L).card : ℕ) : ℝ) else 0) := by
  have hk := kingman_generator_B (ρ := ρ) hw fun P => hpot P.card
  have hinner : ∀ S ∈ partB L, ∀ T ∈ (partB L).erase S,
      hpot ((mergeP (partB L) S T).card) - hpot ((partB L).card)
        = hpot ((partB L).card - 1) - hpot ((partB L).card) := by
    intro S hS T hT
    have hc := card_mergeP_partB hw hS hT
    rw [show (mergeP (partB L) S T).card = (partB L).card - 1 by omega]
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl (hinner S hS),
    sum_pairs_const] at hk
  have hkey := hpot_key ((partB L).card)
  linear_combination hk - hkey

theorem uBlkB_step (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hw : WF t.st.1) :
    uBlkB t = rBlkB t / rateTotS (0 : ℝ) 0 ρ t
      + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlkB t' := by
  have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
  rw [dtotS] at h2
  by_cases hd : 0 < dtot (0 : ℝ) 0 ρ t.st.1
  · have hDpos : (0 : ℝ) < dtotArg ρ t.st.1 := by
      rw [← dtot_zero_eq_dtotArg]
      exact hd
    have hDne : dtotArg ρ t.st.1 ≠ 0 := ne_of_gt hDpos
    have hstep : stepT (0 : ℝ) 0 ρ πA πB
        (fun t' : TSt n KA KB => uBlkB (⟨t'⟩ : TS n KA KB)) t.st
        = stepArg ρ (fun M => hpot ((partB M).card)) t.st.1 := by
      rw [← stepU_zero_eq_stepArg]
      exact stepT_of_fst h.sumA h.sumB (fun L => hpot ((partB L).card)) t.st
    have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlkB t')
        = (dtotArg ρ t.st.1 * hpot ((partB t.st.1).card)
            - 2 * (if 2 ≤ (partB t.st.1).card
              then (((partB t.st.1).card : ℕ) : ℝ) else 0)) / dtotArg ρ t.st.1 := by
      rw [sum_transS_eq hd, hstep, stepArg_hpotB hw, dtot_zero_eq_dtotArg]
    have hrate : rateTotS (0 : ℝ) 0 ρ t = dtotArg ρ t.st.1 / 2 := by
      rw [dtot_zero_eq_dtotArg] at h2
      linarith
    rw [hsum, hrate, uBlkB_eq, rBlkB_eq]
    field_simp
    ring
  · have hz : ¬ 0 < dtotS (0 : ℝ) 0 ρ t := hd
    have hzz : dtot (0 : ℝ) 0 ρ t.st.1 = 0 :=
      le_antisymm (not_lt.1 hd) (dtot_nonneg le_rfl le_rfl h.rho _)
    have hrate : rateTotS (0 : ℝ) 0 ρ t = 0 := by
      rw [hzz] at h2
      linarith
    rw [sum_transS_of_nonpos hz, hrate, div_zero, zero_add]

theorem one_le_rateTotS_of_two_le_B (hρ : 0 ≤ ρ) {t : TS n KA KB} (ht : 2 ≤ nblkB t) :
    1 ≤ rateTotS (0 : ℝ) 0 ρ t := by
  have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
  rw [dtotS, dtot] at h2
  have hcard : 2 ≤ t.st.1.card := le_trans ht (nblkB_le_card t)
  have hnat : 2 ≤ t.st.1.card * (t.st.1.card - 1) := by
    have h3 : 2 * 1 ≤ t.st.1.card * (t.st.1.card - 1) :=
      Nat.mul_le_mul hcard (by omega)
    omega
  have hc : (2 : ℝ) ≤ ((t.st.1.card * (t.st.1.card - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hr : (0 : ℝ) ≤ ρ * ((tt t.st.1 : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
  simp only [zero_mul, add_zero] at h2
  linarith

theorem exists_weight_lower_bound_B (hρ : 0 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : TS n KA KB, 2 ≤ nblkB t →
      c ≤ rBlkB t / rateTotS (0 : ℝ) 0 ρ t := by
  obtain ⟨t₁, ht₁⟩ := Finite.exists_max fun t : TS n KA KB => rateTotS (0 : ℝ) 0 ρ t
  have hCnn : (0 : ℝ) ≤ rateTotS (0 : ℝ) 0 ρ t₁ :=
    rateTotS_nonneg le_rfl le_rfl hρ t₁
  refine ⟨2 / (rateTotS (0 : ℝ) 0 ρ t₁ + 1), by positivity, fun t ht => ?_⟩
  have hr1 : 1 ≤ rateTotS (0 : ℝ) 0 ρ t := one_le_rateTotS_of_two_le_B hρ ht
  have hrpos : 0 < rateTotS (0 : ℝ) 0 ρ t := by linarith
  have hrC : rateTotS (0 : ℝ) 0 ρ t ≤ rateTotS (0 : ℝ) 0 ρ t₁ + 1 := by
    have := ht₁ t
    linarith
  have hCpos : (0 : ℝ) < rateTotS (0 : ℝ) 0 ρ t₁ + 1 := by linarith
  have hb : (2 : ℝ) ≤ rBlkB t := by
    rw [rBlkB, ite_eq_left ht]
    exact_mod_cast ht
  rw [div_le_div_iff₀ hCpos hrpos]
  nlinarith

theorem ae_eventually_uBlkB_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) :
    ∀ᵐ ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s),
      ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → uBlkB (ω N) = 0 := by
  obtain ⟨c, hcpos, hc⟩ := exists_weight_lower_bound_B (n := n) (KA := KA) (KB := KB) h.rho
  have hgnn : ∀ t : TS n KA KB, 0 ≤ rBlkB t / rateTotS (0 : ℝ) 0 ρ t :=
    fun t => div_nonneg (rBlkB_nonneg t) (rateTotS_nonneg le_rfl le_rfl h.rho t)
  have hle : (∫⁻ ω, occAll (fun t => rBlkB t / rateTotS (0 : ℝ) 0 ρ t) ω
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≤ ENNReal.ofReal (uBlkB s) :=
    lintegral_occAll_le h closed_wf hgnn (fun t hwt => uBlkB_step h hwt)
      (fun t => uBlkB_nonneg t) hw
  have hne : (∫⁻ ω, occAll (fun t => rBlkB t / rateTotS (0 : ℝ) 0 ρ t) ω
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae := ae_lt_top (measurable_occAll
    (fun t : TS n KA KB => rBlkB t / rateTotS (0 : ℝ) 0 ρ t)) hne
  filter_upwards [hae] with ω hω
  have hfin : {k : ℕ | ENNReal.ofReal c ≤
      ENNReal.ofReal (rBlkB (ω k) / rateTotS (0 : ℝ) 0 ρ (ω k))}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hω.ne
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hcpos)
  have hsub : {k : ℕ | 2 ≤ nblkB (ω k)} ⊆ {k : ℕ | ENNReal.ofReal c ≤
      ENNReal.ofReal (rBlkB (ω k) / rateTotS (0 : ℝ) 0 ρ (ω k))} :=
    fun k hk => ENNReal.ofReal_le_ofReal (hc (ω k) hk)
  obtain ⟨N₁, hN₁⟩ := (hfin.subset hsub).bddAbove
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  refine uBlkB_eq_zero_of_le_one ?_
  by_contra hc2
  have h2 : 2 ≤ nblkB (ω N) := by omega
  have hle : N ≤ N₁ := hN₁ h2
  omega

theorem tendsto_mstep_uBlkB_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) :
    Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N uBlkB s) Filter.atTop (nhds 0) := by
  obtain ⟨t₂, ht₂⟩ := Finite.exists_max fun t : TS n KA KB => uBlkB t
  have hmeasF : ∀ N : ℕ, Measurable
      fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (uBlkB (ω N)) :=
    fun N => (Measurable.of_discrete
      (f := fun t : TS n KA KB => ENNReal.ofReal (uBlkB t))).comp (measurable_pi_apply N)
  have hbound : ∀ N : ℕ, (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (uBlkB (ω N)))
      ≤ᵐ[argTrajT (0 : ℝ) 0 ρ πA πB h s] fun _ => ENNReal.ofReal (uBlkB t₂) := by
    intro N
    filter_upwards with ω
    exact ENNReal.ofReal_le_ofReal (ht₂ (ω N))
  have hbint : (∫⁻ _ω : (_ : ℕ) → TS n KA KB, ENNReal.ofReal (uBlkB t₂)
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  have haelim : ∀ᵐ ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s),
      Filter.Tendsto (fun N => ENNReal.ofReal (uBlkB (ω N))) Filter.atTop (nhds 0) := by
    filter_upwards [ae_eventually_uBlkB_zero h hw] with ω hω
    obtain ⟨N₁, hN₁⟩ := hω
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
    filter_upwards [Filter.eventually_ge_atTop N₁] with N hN
    rw [hN₁ N hN, ENNReal.ofReal_zero]
  have hdct := tendsto_lintegral_of_dominated_convergence
    (μ := argTrajT (0 : ℝ) 0 ρ πA πB h s) (fun _ => ENNReal.ofReal (uBlkB t₂))
    hmeasF hbound hbint haelim
  rw [lintegral_zero] at hdct
  have hval : ∀ N : ℕ, (∫⁻ ω, ENNReal.ofReal (uBlkB (ω N))
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (mstep (0 : ℝ) 0 ρ πA πB N uBlkB s) :=
    fun N => lintegral_argTrajT h N (fun t => uBlkB_nonneg t) s
  simp only [hval] at hdct
  have hconv := (ENNReal.tendsto_toReal (by simp)).comp hdct
  simp only [Function.comp_def, ENNReal.toReal_zero] at hconv
  refine hconv.congr fun N => ?_
  exact ENNReal.toReal_ofReal (mstep_nonneg h N (fun t => uBlkB_nonneg t) s)

theorem closed_wf_coverB : Closed (0 : ℝ) 0 ρ πA πB
    fun t : TS n KA KB => WF t.st.1 ∧ coverB t.st.1 = Finset.univ := by
  intro s t hs ht
  refine transS_eq_zero_of_move (P := fun L => WF L ∧ coverB L = Finset.univ) ?_ ?_ hs ht
  · intro p hp q hq
    exact ⟨hs.1.coal hp (Finset.mem_of_mem_erase hq), by rw [coverB_coal hp hq]; exact hs.2⟩
  · intro p hp
    obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
    exact ⟨hs.1.recomb hpL h1 h2, by rw [coverB_rec hs.1 hpL]; exact hs.2⟩

theorem coverB_fullState : coverB (fullState n) = Finset.univ := by
  ext k
  simp only [Finset.mem_univ, iff_true]
  exact mem_coverB.2 ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, Finset.mem_singleton_self k⟩

theorem partB_fullState :
    partB (fullState n) = Finset.univ.image fun k : Fin n => ({k} : Finset (Fin n)) := by
  have hcarB : carB (fullState n) = fullState n := by
    rw [carB, Finset.filter_true_of_mem]
    intro p hp
    obtain ⟨k, rfl⟩ := mem_fullState.1 hp
    exact Finset.singleton_nonempty k
  rw [partB, hcarB, fullState, Finset.image_image]
  rfl

theorem card_partB_fullState : (partB (fullState n)).card = n := by
  have hinj : Function.Injective fun k : Fin n => ({k} : Finset (Fin n)) := by
    intro k l hkl
    simpa using hkl
  rw [partB_fullState, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

theorem nblkB_initT : nblkB (⟨initT n KA KB⟩ : TS n KA KB) = n := card_partB_fullState

theorem lintegral_branchLenB_uBlkB (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) (hcov : coverB s.st.1 = Finset.univ) :
    (∫⁻ ω, branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (hpot (nblkB s)) := by
  have hC : Closed (0 : ℝ) 0 ρ πA πB
      fun t : TS n KA KB => WF t.st.1 ∧ coverB t.st.1 = Finset.univ := closed_wf_coverB
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdB (0 : ℝ) 0 ρ (cladeFam n) t :=
    holdB_nonneg le_rfl le_rfl h.rho (cladeFam n)
  have hu : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverB t.st.1 = Finset.univ) →
      uBlkB t = holdB (0 : ℝ) 0 ρ (cladeFam n) t
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlkB t' := by
    intro t hCt
    rw [holdB, ← rBlkB_eq_rB hCt.1 hCt.2]
    exact uBlkB_step h hCt.1
  have hmain := lintegral_occAll_eq h hC hgnn hu (tendsto_mstep_uBlkB_zero h hw) ⟨hw, hcov⟩
  have hb : ∀ ω : (_ : ℕ) → TS n KA KB, branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
      = occAll (holdB (0 : ℝ) 0 ρ (cladeFam n)) ω := fun _ => rfl
  rw [lintegral_congr hb, hmain, uBlkB]

theorem expected_total_length_B (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLenB (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      = ENNReal.ofReal (2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) := by
  have hinit : (⟨initT n KA KB⟩ : TS n KA KB).st.1 = fullState n := rfl
  have hw : WF (⟨initT n KA KB⟩ : TS n KA KB).st.1 := by
    rw [hinit]
    exact fullState_wf
  have hcov : coverB (⟨initT n KA KB⟩ : TS n KA KB).st.1 = Finset.univ := by
    rw [hinit]
    exact coverB_fullState
  rw [lintegral_branchLenB_uBlkB h hw hcov, nblkB_initT, hpot]

end Rhone.Coalescent.MarginalLumping
