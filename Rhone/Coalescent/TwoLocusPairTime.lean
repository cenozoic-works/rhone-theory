/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusLD
public import Rhone.Coalescent.MarginalLumping.Potential
public import Rhone.Coalescent.ContinuousTimeGenealogy.Second
public import Rhone.Coalescent.FullARGTwoSampleCovariance

/-!
# Stationary LD ratio as a pair-time covariance of the two-locus genealogy

Source: mcvean2002, eq. (9), (12), pp. 988–989; griffiths1981, sec. 6, p. 178; hudson1983, eq. (1),
p. 186; mcvean2002, eq. (9)–(12), pp. 988–989; wilton_carmi_hobolth2015, eq. (5), Figure S1. -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Filter Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy
  TypedAncestralChain MarginalLumping BranchLengthMoments SecondMoments ContinuousTimeGenealogy
  MarkovChain.WFAllocationLD
open scoped ENNReal Topology

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

set_option maxRecDepth 8000 in
theorem IsPaired.covers {s : Finset (Lin 2)} (hs : IsPaired s) :
    WF s ∧ coverA s = Finset.univ ∧ coverB s = Finset.univ ∧
      (partA s).card = 2 ∧ (partB s).card = 2 := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 8000 in
theorem IsPaired.moves {s : Finset (Lin 2)} (hs : IsPaired s) :
    (∀ p ∈ s, ∀ q ∈ s.erase p, IsPaired (coalL s p q) ∨
        (partA (coalL s p q)).card ≤ 1 ∨ (partB (coalL s p q)).card ≤ 1) ∧
      ∀ p ∈ carC s, IsPaired (recL s p) ∨
        (partA (recL s p)).card ≤ 1 ∨ (partB (recL s p)).card ≤ 1 := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem IsPaired.dtot_pos (ρ : ℝ) (hρ : 0 ≤ ρ) {s : Finset (Lin 2)} (hs : IsPaired s) :
    0 < dtot (0 : ℝ) 0 ρ s := by
  obtain ⟨-, -, hcard⟩ := hs.counts
  have htt := hs.tt_le
  have hd : dtot (0 : ℝ) 0 ρ s = ((s.card * (s.card - 1) : ℕ) : ℝ) + ρ * ((tt s : ℕ) : ℝ) := by
    rw [dtot]
    ring
  have hnat : 2 ≤ s.card * (s.card - 1) := by
    have h3 : 2 * 1 ≤ s.card * (s.card - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hc : (2 : ℝ) ≤ ((s.card * (s.card - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hr : (0 : ℝ) ≤ ρ * ((tt s : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
  rw [hd]
  linarith

theorem closed_marginalDone : Closed (0 : ℝ) 0 ρ πA πB
    fun t : TS n KA KB => WF t.st.1 ∧ ((partA t.st.1).card ≤ 1 ∨ (partB t.st.1).card ≤ 1) := by
  intro s t hs ht
  refine transS_eq_zero_of_move
    (P := fun L => WF L ∧ ((partA L).card ≤ 1 ∨ (partB L).card ≤ 1)) ?_ ?_ hs ht
  · intro p hp q hq
    refine ⟨hs.1.coal hp (Finset.mem_of_mem_erase hq), ?_⟩
    have hA : (partA (coalL s.st.1 p q)).card ≤ (partA s.st.1).card := by
      by_cases hb : p.1.Nonempty ∧ q.1.Nonempty
      · have := card_partA_coal hs.1 hp hq hb.1 hb.2
        omega
      · rw [partA_coal_not hs.1 hp hq hb]
    have hB : (partB (coalL s.st.1 p q)).card ≤ (partB s.st.1).card := by
      by_cases hb : p.2.Nonempty ∧ q.2.Nonempty
      · have := card_partB_coal hs.1 hp hq hb.1 hb.2
        omega
      · rw [partB_coal_deg hs.1 hp hq hb]
    rcases hs.2 with h | h
    · exact Or.inl (hA.trans h)
    · exact Or.inr (hB.trans h)
  · intro p hp
    obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
    refine ⟨hs.1.recomb hpL h1 h2, ?_⟩
    rw [partA_rec hs.1 hp, partB_rec hs.1 hp]
    exact hs.2

def pairTimeClass (t : TS 2 KA KB) : Prop :=
  CovAB t ∧ (IsPaired t.st.1 ∨ (partA t.st.1).card ≤ 1 ∨ (partB t.st.1).card ≤ 1)

theorem closed_pairTimeClass :
    Closed (0 : ℝ) 0 ρ πA πB (pairTimeClass (KA := KA) (KB := KB)) := by
  intro s t hs ht
  by_cases hcov : CovAB t
  · have hnt : ¬ (IsPaired t.st.1 ∨ (partA t.st.1).card ≤ 1 ∨ (partB t.st.1).card ≤ 1) :=
      fun hc => ht ⟨hcov, hc⟩
    rcases hs.2 with hp | hd
    · exact transS_eq_zero_of_move
        (P := fun L => IsPaired L ∨ (partA L).card ≤ 1 ∨ (partB L).card ≤ 1)
        hp.moves.1 hp.moves.2 (Or.inl hp) hnt
    · exact closed_marginalDone s t ⟨hs.1.1, hd⟩ fun hc => hnt (Or.inr hc.2)
  · exact closed_wf_coverAB s t hs.1 hcov

/-- Source: wilton_carmi_hobolth2015, eq. (5). -/
noncomputable def pairTimeValue (ρ : ℝ) (c : ℕ) : ℝ :=
  if c ≤ 2 then 4 * (1 + IntervalProcess.twoLocusValue ρ c) else 0

theorem pairTimeValue_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (c : ℕ) : 0 ≤ pairTimeValue ρ c := by
  rw [pairTimeValue]
  split_ifs
  · have := IntervalProcess.twoLocusValue_nonneg ρ hρ c
    linarith
  · exact le_rfl

theorem pairTimeValue_le (ρ : ℝ) (hρ : 0 ≤ ρ) (c : ℕ) : pairTimeValue ρ c ≤ 8 := by
  rw [pairTimeValue]
  split_ifs
  · have := IntervalProcess.twoLocusValue_le_one ρ hρ c
    linarith
  · norm_num

theorem pairTimeValue_pairedClass_of_not (ρ : ℝ) {M : Finset (Lin 2)} (hM : ¬ IsPaired M) :
    pairTimeValue ρ (pairedClass M) = 0 := by
  rw [pairedClass, ite_eq_right hM, pairTimeValue]
  split_ifs <;> simp_all

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem pairTimeValue_step (ρ : ℝ) (hρ : 0 ≤ ρ) {s : Finset (Lin 2)} (hs : IsPaired s) :
    pairTimeValue ρ (tt s) =
      16 / dtot (0 : ℝ) 0 ρ s + pairedStepValue ρ (pairTimeValue ρ) (tt s) := by
  obtain ⟨-, -, hcard⟩ := hs.counts
  have htt := hs.tt_le
  have hd : dtot (0 : ℝ) 0 ρ s = ((s.card * (s.card - 1) : ℕ) : ℝ) + ρ * ((tt s : ℕ) : ℝ) := by
    rw [dtot]
    ring
  have hD : ρ ^ 2 + 13 * ρ + 18 ≠ 0 := by positivity
  have h1 : (2 : ℝ) + 2 * ρ ≠ 0 := by positivity
  have h2 : (6 : ℝ) + ρ ≠ 0 := by positivity
  obtain h | h | h : tt s = 0 ∨ tt s = 1 ∨ tt s = 2 := by omega
  · have hc : s.card = 4 := by omega
    rw [hd, hc, h]
    norm_num [pairTimeValue, pairedStepValue, IntervalProcess.twoLocusValue]
    field_simp
    ring
  · have hc : s.card = 3 := by omega
    rw [hd, hc, h]
    norm_num [pairTimeValue, pairedStepValue, IntervalProcess.twoLocusValue]
    field_simp
    ring
  · have hc : s.card = 2 := by omega
    rw [hd, hc, h]
    norm_num [pairTimeValue, pairedStepValue, IntervalProcess.twoLocusValue]
    field_simp
    ring

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989; wilton_carmi_hobolth2015, eq. (5). -/
theorem ctLaw_paired_branch_mul {KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS 2 KA KB} (ht : IsPaired t.st.1) :
    ∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam 2)) z * ctBranch (0 : ℝ) 0 ρ (rB (cladeFam 2)) z
        ∂(ctLaw (0 : ℝ) 0 ρ πA πB h t) =
      ENNReal.ofReal (4 * (1 + IntervalProcess.twoLocusValue ρ (tt t.st.1))) := by
  have hρ := h.rho
  let w : TS 2 KA KB → ℝ := fun t => pairTimeValue ρ (pairedClass t.st.1)
  have hcov : ∀ t : TS 2 KA KB, IsPaired t.st.1 → CovAB t := fun t hp =>
    ⟨hp.covers.1, hp.covers.2.1, hp.covers.2.2.1⟩
  have hwnn : ∀ t, 0 ≤ w t := fun t => pairTimeValue_nonneg ρ hρ _
  have hwle : ∀ t, w t ≤ 4 * uBlk t := by
    intro t
    by_cases hp : IsPaired t.st.1
    · have hu : uBlk t = 2 := by rw [uBlk_eq, hp.covers.2.2.2.1, hpot_two]
      have := pairTimeValue_le ρ hρ (pairedClass t.st.1)
      rw [hu]
      linarith
    · have hz : w t = 0 := pairTimeValue_pairedClass_of_not ρ hp
      have := uBlk_nonneg t
      rw [hz]
      linarith
  have hfw : ∀ t : TS 2 KA KB, pairTimeClass t →
      w t = (holdA (0 : ℝ) 0 ρ (cladeFam 2) t * uBlkB t
          + holdB (0 : ℝ) 0 ρ (cladeFam 2) t * uBlk t)
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t' := by
    intro t hC
    by_cases hp : IsPaired t.st.1
    · have hpA : (partA t.st.1).card = 2 := hp.covers.2.2.2.1
      have hpB : (partB t.st.1).card = 2 := hp.covers.2.2.2.2
      have hrA : rA (cladeFam 2) t = 2 := by
        rw [← rBlk_eq_rA hC.1.1 hC.1.2.1, rBlk_eq, hpA]
        norm_num
      have hrB : rB (cladeFam 2) t = 2 := by
        rw [← rBlkB_eq_rB hC.1.1 hC.1.2.2, rBlkB_eq, hpB]
        norm_num
      have huA : uBlk t = 2 := by rw [uBlk_eq, hpA, hpot_two]
      have huB : uBlkB t = 2 := by rw [uBlkB_eq, hpB, hpot_two]
      have hdpos : 0 < dtot (0 : ℝ) 0 ρ t.st.1 := hp.dtot_pos ρ hρ
      have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
      rw [dtotS] at h2
      have hr : rateTotS (0 : ℝ) 0 ρ t = dtot (0 : ℝ) 0 ρ t.st.1 / 2 := by linarith
      have hstep : stepT (0 : ℝ) 0 ρ πA πB (fun t' : TSt 2 KA KB => w (⟨t'⟩ : TS 2 KA KB)) t.st
          = stepU (0 : ℝ) 0 ρ (fun M => pairTimeValue ρ (pairedClass M)) t.st.1 :=
        stepT_of_fst h.sumA h.sumB (fun M => pairTimeValue ρ (pairedClass M)) t.st
      have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t')
          = pairedStepValue ρ (pairTimeValue ρ) (tt t.st.1) := by
        rw [sum_transS_eq hdpos w, hstep, ← sum_trans_mul_of_pos 0 0 ρ _ hdpos]
        exact sum_trans_mul_pairedClass ρ hρ (pairTimeValue ρ) hp
      have hwt : w t = pairTimeValue ρ (tt t.st.1) := by
        change pairTimeValue ρ (pairedClass t.st.1) = _
        rw [pairedClass_of_isPaired hp]
      rw [hsum, hwt, pairTimeValue_step ρ hρ hp, holdA, holdB, hrA, hrB, huA, huB, hr]
      have hne : dtot (0 : ℝ) 0 ρ t.st.1 ≠ 0 := ne_of_gt hdpos
      field_simp
      ring
    · have hd : (partA t.st.1).card ≤ 1 ∨ (partB t.st.1).card ≤ 1 := by
        rcases hC.2 with hc | hc
        · exact absurd hc hp
        · exact hc
      have hz : w t = 0 := pairTimeValue_pairedClass_of_not ρ hp
      have hsrc : holdA (0 : ℝ) 0 ρ (cladeFam 2) t * uBlkB t
          + holdB (0 : ℝ) 0 ρ (cladeFam 2) t * uBlk t = 0 := by
        rcases hd with hA | hB
        · have hr0 : rA (cladeFam 2) t = 0 := by
            rw [← rBlk_eq_rA hC.1.1 hC.1.2.1, rBlk_eq, ite_eq_right (by omega)]
          have hu0 : uBlk t = 0 := uBlk_eq_zero_of_le_one hA
          rw [holdA, hr0, hu0]
          ring
        · have hr0 : rB (cladeFam 2) t = 0 := by
            rw [← rBlkB_eq_rB hC.1.1 hC.1.2.2, rBlkB_eq, ite_eq_right (by omega)]
          have hu0 : uBlkB t = 0 := uBlkB_eq_zero_of_le_one hB
          rw [holdB, hr0, hu0]
          ring
      have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * w t') = 0 := by
        refine Finset.sum_eq_zero fun t' _ => ?_
        by_cases hp' : IsPaired t'.st.1
        · have hz' : transS (0 : ℝ) 0 ρ πA πB t t' = 0 := by
            refine closed_marginalDone t t' ⟨hC.1.1, hd⟩ fun hc => ?_
            have hA' := hp'.covers.2.2.2.1
            have hB' := hp'.covers.2.2.2.2
            rcases hc.2 with hcA | hcB
            · omega
            · omega
          rw [hz', zero_mul]
        · have hz' : w t' = 0 := pairTimeValue_pairedClass_of_not ρ hp'
          rw [hz', mul_zero]
      rw [hz, hsrc, hsum, add_zero]
  have hlim : Tendsto (fun N => 4 * mstep (0 : ℝ) 0 ρ πA πB N uBlk t) atTop (𝓝 0) := by
    simpa using (tendsto_mstep_uBlk_zero h (hcov t ht).1).const_mul 4
  have hlw : Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N w t) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun N => mstep_nonneg h N hwnn t) fun N => ?_
    change mstep (0 : ℝ) 0 ρ πA πB N w t ≤ 4 * mstep (0 : ℝ) 0 ρ πA πB N uBlk t
    rw [← mstep_const_mul]
    exact mstep_mono h N hwle t
  have hmain := lintegral_occAll_mul_eq h closed_pairTimeClass
    (holdA_nonneg le_rfl le_rfl hρ (cladeFam 2)) (holdB_nonneg le_rfl le_rfl hρ (cladeFam 2))
    (fun t => uBlk_nonneg t) (fun t => uBlkB_nonneg t)
    (fun t hC => uBlk_step_covAB h hC.1) (fun t hC => uBlkB_step_covAB h hC.1)
    (fun t hC => tendsto_mstep_uBlk_zero h hC.1.1)
    (fun t hC => tendsto_mstep_uBlkB_zero h hC.1.1)
    hfw hlw ⟨hcov t ht, Or.inl ht⟩
  have hwt : w t = 4 * (1 + IntervalProcess.twoLocusValue ρ (tt t.st.1)) := by
    change pairTimeValue ρ (pairedClass t.st.1) = _
    rw [pairedClass_of_isPaired ht, pairTimeValue, ite_eq_left ht.tt_le]
  rw [lintegral_ctBranch_mul h (cladeFam 2) (cladeFam 2) t, ← hwt]
  exact hmain

theorem ctLaw_paired_branch {KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS 2 KA KB} (ht : IsPaired t.st.1) :
    ∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam 2)) z ∂(ctLaw (0 : ℝ) 0 ρ πA πB h t) = 2 := by
  rw [lintegral_ctBranch h (cladeFam 2) t,
    lintegral_branchLen_uBlk h ht.covers.1 ht.covers.2.1]
  have hk : nblk t = 2 := ht.covers.2.2.2.1
  rw [hk, hpot_two]
  simp

theorem initT_two_isPaired {KA KB : ℕ} :
    IsPaired (⟨initT 2 KA KB⟩ : TS 2 KA KB).st.1 ∧ tt (⟨initT 2 KA KB⟩ : TS 2 KA KB).st.1 = 2 := by
  have hinit : (⟨initT 2 KA KB⟩ : TS 2 KA KB).st.1 = fullState 2 := rfl
  have hfull : fullState 2 = ({({0}, {0}), ({1}, {1})} : Finset (Lin 2)) := by decide
  rw [hinit, hfull]
  exact ⟨Or.inl rfl, by decide⟩

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1)–(4), p. 186; mcvean2002, eq. (9)–(12),
pp. 988–989. -/
theorem ctLaw_two_sample_branch_mul_eq_fullARG {KA KB : ℕ} {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (R : ℝ) (hR : 0 ≤ R) (x y : IntervalProcess.GenomicProbe)
    (hxy : x.val < y.val)
    (h : Adm (0 : ℝ) 0 (R * ((y.val : ℝ) - (x.val : ℝ))) πA πB) :
    ∫⁻ z, ctBranch (0 : ℝ) 0 (R * ((y.val : ℝ) - (x.val : ℝ))) (rA (cladeFam 2)) z *
        ctBranch (0 : ℝ) 0 (R * ((y.val : ℝ) - (x.val : ℝ))) (rB (cladeFam 2)) z
        ∂(ctLaw (0 : ℝ) 0 (R * ((y.val : ℝ) - (x.val : ℝ))) πA πB h
          (⟨initT 2 KA KB⟩ : TS 2 KA KB)) =
      4 * ∫⁻ G, G x 0 1 * G y 0 1 ∂IntervalProcess.fullARGGenealogyLaw 2 R := by
  rw [ctLaw_paired_branch_mul h initT_two_isPaired.1, initT_two_isPaired.2,
    IntervalProcess.fullARG_two_sample_pairTime_mul_lintegral R hR x y hxy,
    ENNReal.ofReal_mul (by norm_num)]
  simp [IntervalProcess.twoLocusValue]

/-- Source: mcvean2002, eq. (9), p. 988. -/
noncomputable def pairTimeCov {KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) (t : TS 2 KA KB) : ℝ :=
  (∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam 2)) z * ctBranch (0 : ℝ) 0 ρ (rB (cladeFam 2)) z
      ∂(ctLaw (0 : ℝ) 0 ρ πA πB h t)).toReal / 4 - 1

/--
Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989; wilton_carmi_hobolth2015, eq. (5). -/
theorem pairTimeCov_eq {KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS 2 KA KB} (ht : IsPaired t.st.1) :
    pairTimeCov h t = IntervalProcess.twoLocusValue ρ (tt t.st.1) := by
  have hnn := IntervalProcess.twoLocusValue_nonneg ρ h.rho (tt t.st.1)
  rw [pairTimeCov, ctLaw_paired_branch_mul h ht, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Source: mcvean2002, eq. (9), (12), pp. 988–989; ohta_kimura1971_ld, eq. (9), p. 574. -/
theorem ld_stationary_sigma_limit_eq_pairTimeCovariance (N : ℕ → ℕ) (u : ℕ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hN : ∀ n, 3 ≤ N n) (hc : ∀ n, R / (2 * (N n : ℝ)) ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → Rhone.MarkovChain.AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a *
      forcedCountKernel (N n) (R / (2 * (N n : ℝ))) (u n) a b = π n b)
    (hlarge : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hrare : Tendsto (fun n => u n * (N n : ℝ)) atTop (𝓝 0))
    {KA KB : ℕ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (h : Adm (0 : ℝ) 0 R πA πB)
    {t₂ t₁ t₀ : TS 2 KA KB} (h₂ : IsPaired t₂.st.1) (h₁ : IsPaired t₁.st.1)
    (h₀ : IsPaired t₀.st.1) (ht₂ : tt t₂.st.1 = 2) (ht₁ : tt t₁.st.1 = 1)
    (ht₀ : tt t₀.st.1 = 0) :
    Tendsto (fun n => ldStationaryMoments (N n) (π n) 2 / ldStationaryMoments (N n) (π n) 0)
      atTop (𝓝 ((pairTimeCov h t₂ - 2 * pairTimeCov h t₁ + pairTimeCov h t₀) /
        (1 + pairTimeCov h t₀))) := by
  rw [pairTimeCov_eq h h₂, pairTimeCov_eq h h₁, pairTimeCov_eq h h₀, ht₂, ht₁, ht₀,
    twoLocusValue_sigma R hR]
  exact ld_stationary_sigma_limit N u R hR hN hc hu0 hu1 π hπ hnorm hstat hlarge hrare

theorem pairTime_instance (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Adm (0 : ℝ) 0 ρ (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) ∧
      ∃ t₂ t₁ t₀ : TS 2 1 1, IsPaired t₂.st.1 ∧ IsPaired t₁.st.1 ∧ IsPaired t₀.st.1 ∧
        tt t₂.st.1 = 2 ∧ tt t₁.st.1 = 1 ∧ tt t₀.st.1 = 0 := by
  obtain ⟨h2, h1, h0, e2, e1, e0⟩ := pairedExit_instance
  exact ⟨⟨le_rfl, le_rfl, hρ, fun _ => zero_le_one, fun _ => zero_le_one, by simp, by simp⟩,
    ⟨(_, noneT 2 1, noneT 2 1)⟩, ⟨(_, noneT 2 1, noneT 2 1)⟩, ⟨(_, noneT 2 1, noneT 2 1)⟩,
    h2, h1, h0, e2, e1, e0⟩

end Rhone.Coalescent
