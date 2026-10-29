/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Kingman
public import Rhone.Coalescent.BranchLengthMoments.Branch

/-! # `E[L_A] = 2 H_{n−1}`: the first quantitative coalescent identity -/

@[expose] public section

namespace Rhone.Coalescent.BranchLengthMoments

open Finset TwoLocusGenealogy TypedAncestralChain LinearAlgebra.Recursion
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem dtot_zero_eq_dtotArg (L : Finset (Lin n)) :
    dtot (0 : ℝ) 0 ρ L = dtotArg ρ L := by
  rw [dtot, dtotArg]
  ring

theorem stepU_zero_eq_stepArg (f : Finset (Lin n) → ℝ) (L : Finset (Lin n)) :
    stepU (0 : ℝ) 0 ρ f L = stepArg ρ f L := by
  rw [stepU, stepArg]
  ring

noncomputable def hpot (k : ℕ) : ℝ := 2 * ∑ i ∈ Finset.range (k - 1), (1 : ℝ) / (i + 1)

@[simp] theorem hpot_zero : hpot 0 = 0 := by simp [hpot]

@[simp] theorem hpot_one : hpot 1 = 0 := by simp [hpot]

theorem hpot_nonneg (k : ℕ) : 0 ≤ hpot k := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
  positivity

theorem hpot_eq_zero_of_le_one {k : ℕ} (hk : k ≤ 1) : hpot k = 0 := by
  interval_cases k
  · exact hpot_zero
  · exact hpot_one

theorem hpot_succ_succ (m : ℕ) : hpot (m + 2) = hpot (m + 1) + 2 / (m + 1) := by
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [hpot, hpot, h1, h2, Finset.sum_range_succ]
  ring

theorem hpot_key (k : ℕ) :
    ((k * (k - 1) : ℕ) : ℝ) * (hpot k - hpot (k - 1))
      = 2 * (if 2 ≤ k then (k : ℝ) else 0) := by
  match k with
  | 0 => norm_num
  | 1 => norm_num
  | (m + 2) =>
    have h1 : m + 2 - 1 = m + 1 := by omega
    rw [h1, hpot_succ_succ m, ite_eq_left (by omega : 2 ≤ m + 2), add_sub_cancel_left]
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp

def nblk (t : TS n KA KB) : ℕ := (partA t.st.1).card

theorem nblk_le_card (t : TS n KA KB) : nblk t ≤ t.st.1.card := by
  refine le_trans ?_ (Finset.card_le_card (carA_subset t.st.1))
  rw [nblk, partA]
  exact Finset.card_image_le

noncomputable def rBlk (t : TS n KA KB) : ℝ := if 2 ≤ nblk t then (nblk t : ℝ) else 0

theorem rBlk_eq (t : TS n KA KB) :
    rBlk t = if 2 ≤ (partA t.st.1).card then (((partA t.st.1).card : ℕ) : ℝ) else 0 := rfl

theorem rBlk_nonneg (t : TS n KA KB) : 0 ≤ rBlk t := by
  rw [rBlk]
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

noncomputable def uBlk (t : TS n KA KB) : ℝ := hpot (nblk t)

theorem uBlk_eq (t : TS n KA KB) : uBlk t = hpot ((partA t.st.1).card) := rfl

theorem uBlk_nonneg (t : TS n KA KB) : 0 ≤ uBlk t := hpot_nonneg _

theorem uBlk_eq_zero_of_le_one {t : TS n KA KB} (ht : nblk t ≤ 1) : uBlk t = 0 :=
  hpot_eq_zero_of_le_one ht

theorem card_mergeP_partA {L : Finset (Lin n)} (hw : WF L) {S T : Finset (Fin n)}
    (hS : S ∈ partA L) (hT : T ∈ (partA L).erase S) :
    (mergeP (partA L) S T).card + 1 = (partA L).card := by
  obtain ⟨p, hpA, hpS⟩ := mem_partA.1 hS
  obtain ⟨q, hqA, hqT⟩ := mem_partA.1 (Finset.mem_of_mem_erase hT)
  obtain ⟨hpL, h1⟩ := mem_carA.1 hpA
  obtain ⟨hqL, h2⟩ := mem_carA.1 hqA
  have hTS : T ≠ S := Finset.ne_of_mem_erase hT
  have hqp : q ≠ p := by
    intro hc
    exact hTS (by rw [← hqT, hc, hpS])
  have hqe : q ∈ L.erase p := Finset.mem_erase.2 ⟨hqp, hqL⟩
  have hmerge : partA (coalL L p q) = mergeP (partA L) S T := by
    rw [partA_coal_both hw hpL hqe h1 h2, hpS, hqT]
  rw [← hmerge]
  exact card_partA_coal hw hpL hqe h1 h2

theorem stepArg_hpot {L : Finset (Lin n)} (hw : WF L) :
    stepArg ρ (fun M => hpot ((partA M).card)) L
      = dtotArg ρ L * hpot ((partA L).card)
        - 2 * (if 2 ≤ (partA L).card then (((partA L).card : ℕ) : ℝ) else 0) := by
  have hk := kingman_generator (ρ := ρ) hw fun P => hpot P.card
  have hinner : ∀ S ∈ partA L, ∀ T ∈ (partA L).erase S,
      hpot ((mergeP (partA L) S T).card) - hpot ((partA L).card)
        = hpot ((partA L).card - 1) - hpot ((partA L).card) := by
    intro S hS T hT
    have hc := card_mergeP_partA hw hS hT
    rw [show (mergeP (partA L) S T).card = (partA L).card - 1 by omega]
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl (hinner S hS),
    sum_pairs_const] at hk
  have hkey := hpot_key ((partA L).card)
  linear_combination hk - hkey

theorem uBlk_step (h : Adm (0 : ℝ) 0 ρ πA πB) {t : TS n KA KB} (hw : WF t.st.1) :
    uBlk t = rBlk t / rateTotS (0 : ℝ) 0 ρ t
      + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t' := by
  have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
  rw [dtotS] at h2
  by_cases hd : 0 < dtot (0 : ℝ) 0 ρ t.st.1
  · have hDpos : (0 : ℝ) < dtotArg ρ t.st.1 := by
      rw [← dtot_zero_eq_dtotArg]
      exact hd
    have hDne : dtotArg ρ t.st.1 ≠ 0 := ne_of_gt hDpos
    have hstep : stepT (0 : ℝ) 0 ρ πA πB
        (fun t' : TSt n KA KB => uBlk (⟨t'⟩ : TS n KA KB)) t.st
        = stepArg ρ (fun M => hpot ((partA M).card)) t.st.1 := by
      rw [← stepU_zero_eq_stepArg]
      exact stepT_of_fst h.sumA h.sumB (fun L => hpot ((partA L).card)) t.st
    have hsum : (∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t')
        = (dtotArg ρ t.st.1 * hpot ((partA t.st.1).card)
            - 2 * (if 2 ≤ (partA t.st.1).card
              then (((partA t.st.1).card : ℕ) : ℝ) else 0)) / dtotArg ρ t.st.1 := by
      rw [sum_transS_eq hd, hstep, stepArg_hpot hw, dtot_zero_eq_dtotArg]
    have hrate : rateTotS (0 : ℝ) 0 ρ t = dtotArg ρ t.st.1 / 2 := by
      rw [dtot_zero_eq_dtotArg] at h2
      linarith
    rw [hsum, hrate, uBlk_eq, rBlk_eq]
    field_simp
    ring
  · have hz : ¬ 0 < dtotS (0 : ℝ) 0 ρ t := hd
    have hzz : dtot (0 : ℝ) 0 ρ t.st.1 = 0 :=
      le_antisymm (not_lt.1 hd) (dtot_nonneg le_rfl le_rfl h.rho _)
    have hrate : rateTotS (0 : ℝ) 0 ρ t = 0 := by
      rw [hzz] at h2
      linarith
    rw [sum_transS_of_nonpos hz, hrate, div_zero, zero_add]

theorem one_le_rateTotS_of_two_le (hρ : 0 ≤ ρ) {t : TS n KA KB} (ht : 2 ≤ nblk t) :
    1 ≤ rateTotS (0 : ℝ) 0 ρ t := by
  have h2 := two_mul_rateTotS (θA := (0 : ℝ)) (θB := (0 : ℝ)) (ρ := ρ) t
  rw [dtotS, dtot] at h2
  have hcard : 2 ≤ t.st.1.card := le_trans ht (nblk_le_card t)
  have hnat : 2 ≤ t.st.1.card * (t.st.1.card - 1) := by
    have h3 : 2 * 1 ≤ t.st.1.card * (t.st.1.card - 1) :=
      Nat.mul_le_mul hcard (by omega)
    omega
  have hc : (2 : ℝ) ≤ ((t.st.1.card * (t.st.1.card - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hr : (0 : ℝ) ≤ ρ * ((tt t.st.1 : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
  simp only [zero_mul, add_zero] at h2
  linarith

theorem exists_weight_lower_bound (hρ : 0 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : TS n KA KB, 2 ≤ nblk t →
      c ≤ rBlk t / rateTotS (0 : ℝ) 0 ρ t := by
  obtain ⟨t₁, ht₁⟩ := Finite.exists_max fun t : TS n KA KB => rateTotS (0 : ℝ) 0 ρ t
  have hCnn : (0 : ℝ) ≤ rateTotS (0 : ℝ) 0 ρ t₁ :=
    rateTotS_nonneg le_rfl le_rfl hρ t₁
  refine ⟨2 / (rateTotS (0 : ℝ) 0 ρ t₁ + 1), by positivity, fun t ht => ?_⟩
  have hr1 : 1 ≤ rateTotS (0 : ℝ) 0 ρ t := one_le_rateTotS_of_two_le hρ ht
  have hrpos : 0 < rateTotS (0 : ℝ) 0 ρ t := by linarith
  have hrC : rateTotS (0 : ℝ) 0 ρ t ≤ rateTotS (0 : ℝ) 0 ρ t₁ + 1 := by
    have := ht₁ t
    linarith
  have hCpos : (0 : ℝ) < rateTotS (0 : ℝ) 0 ρ t₁ + 1 := by linarith
  have hb : (2 : ℝ) ≤ rBlk t := by
    rw [rBlk, ite_eq_left ht]
    exact_mod_cast ht
  rw [div_le_div_iff₀ hCpos hrpos]
  nlinarith

theorem ae_eventually_uBlk_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) :
    ∀ᵐ ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s),
      ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → uBlk (ω N) = 0 := by
  obtain ⟨c, hcpos, hc⟩ := exists_weight_lower_bound (n := n) (KA := KA) (KB := KB) h.rho
  have hgnn : ∀ t : TS n KA KB, 0 ≤ rBlk t / rateTotS (0 : ℝ) 0 ρ t :=
    fun t => div_nonneg (rBlk_nonneg t) (rateTotS_nonneg le_rfl le_rfl h.rho t)
  have hle : (∫⁻ ω, occAll (fun t => rBlk t / rateTotS (0 : ℝ) 0 ρ t) ω
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≤ ENNReal.ofReal (uBlk s) :=
    lintegral_occAll_le h closed_wf hgnn (fun t hwt => uBlk_step h hwt)
      (fun t => uBlk_nonneg t) hw
  have hne : (∫⁻ ω, occAll (fun t => rBlk t / rateTotS (0 : ℝ) 0 ρ t) ω
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae := ae_lt_top (measurable_occAll
    (fun t : TS n KA KB => rBlk t / rateTotS (0 : ℝ) 0 ρ t)) hne
  filter_upwards [hae] with ω hω
  have hfin : {k : ℕ | ENNReal.ofReal c ≤
      ENNReal.ofReal (rBlk (ω k) / rateTotS (0 : ℝ) 0 ρ (ω k))}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hω.ne
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hcpos)
  have hsub : {k : ℕ | 2 ≤ nblk (ω k)} ⊆ {k : ℕ | ENNReal.ofReal c ≤
      ENNReal.ofReal (rBlk (ω k) / rateTotS (0 : ℝ) 0 ρ (ω k))} :=
    fun k hk => ENNReal.ofReal_le_ofReal (hc (ω k) hk)
  obtain ⟨N₁, hN₁⟩ := (hfin.subset hsub).bddAbove
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  refine uBlk_eq_zero_of_le_one ?_
  by_contra hc2
  have h2 : 2 ≤ nblk (ω N) := by omega
  have hle : N ≤ N₁ := hN₁ h2
  omega

theorem tendsto_mstep_uBlk_zero (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) :
    Filter.Tendsto (fun N => mstep (0 : ℝ) 0 ρ πA πB N uBlk s) Filter.atTop (nhds 0) := by
  obtain ⟨t₂, ht₂⟩ := Finite.exists_max fun t : TS n KA KB => uBlk t
  have hmeasF : ∀ N : ℕ, Measurable
      fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (uBlk (ω N)) :=
    fun N => (Measurable.of_discrete
      (f := fun t : TS n KA KB => ENNReal.ofReal (uBlk t))).comp (measurable_pi_apply N)
  have hbound : ∀ N : ℕ, (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (uBlk (ω N)))
      ≤ᵐ[argTrajT (0 : ℝ) 0 ρ πA πB h s] fun _ => ENNReal.ofReal (uBlk t₂) := by
    intro N
    filter_upwards with ω
    exact ENNReal.ofReal_le_ofReal (ht₂ (ω N))
  have hbint : (∫⁻ _ω : (_ : ℕ) → TS n KA KB, ENNReal.ofReal (uBlk t₂)
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s)) ≠ ⊤ := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  have haelim : ∀ᵐ ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s),
      Filter.Tendsto (fun N => ENNReal.ofReal (uBlk (ω N))) Filter.atTop (nhds 0) := by
    filter_upwards [ae_eventually_uBlk_zero h hw] with ω hω
    obtain ⟨N₁, hN₁⟩ := hω
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
    filter_upwards [Filter.eventually_ge_atTop N₁] with N hN
    rw [hN₁ N hN, ENNReal.ofReal_zero]
  have hdct := tendsto_lintegral_of_dominated_convergence
    (μ := argTrajT (0 : ℝ) 0 ρ πA πB h s) (fun _ => ENNReal.ofReal (uBlk t₂))
    hmeasF hbound hbint haelim
  rw [lintegral_zero] at hdct
  have hval : ∀ N : ℕ, (∫⁻ ω, ENNReal.ofReal (uBlk (ω N))
      ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (mstep (0 : ℝ) 0 ρ πA πB N uBlk s) :=
    fun N => lintegral_argTrajT h N (fun t => uBlk_nonneg t) s
  simp only [hval] at hdct
  have hconv := (ENNReal.tendsto_toReal (by simp)).comp hdct
  simp only [Function.comp_def, ENNReal.toReal_zero] at hconv
  refine hconv.congr fun N => ?_
  exact ENNReal.toReal_ofReal (mstep_nonneg h N (fun t => uBlk_nonneg t) s)

theorem transS_eq_zero_of_move {P : Finset (Lin n) → Prop} {s t : TS n KA KB}
    (hcoal : ∀ p ∈ s.st.1, ∀ q ∈ s.st.1.erase p, P (coalL s.st.1 p q))
    (hrec : ∀ p ∈ carC s.st.1, P (recL s.st.1 p))
    (hself : P s.st.1) (ht : ¬ P t.st.1) :
    transS (0 : ℝ) 0 ρ πA πB s t = 0 := by
  have hne : t.st ≠ s.st := fun hc => ht (by rw [hc]; exact hself)
  by_cases hd : 0 < dtot (0 : ℝ) 0 ρ s.st.1
  · rw [transS, transT_of_dtot_pos hd]
    have hz : stepT (0 : ℝ) 0 ρ πA πB (fun t' => if t' = t.st then 1 else 0) s.st = 0 := by
      have e1 : (∑ p ∈ s.st.1, ∑ q ∈ s.st.1.erase p,
          if ((coalL s.st.1 p q, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
          ite_eq_right fun hcc => ?_
        exact ht (by rw [← congrArg Prod.fst hcc]; exact hcoal p hp q hq)
      have e4 : (∑ p ∈ carC s.st.1,
          if ((recL s.st.1 p, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st
            then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ite_eq_right fun hcc => ?_
        exact ht (by rw [← congrArg Prod.fst hcc]; exact hrec p hp)
      rw [stepT, e1, e4]
      ring
    rw [hz, zero_div]
  · rw [transS, transT_of_dtot_nonpos hd, ite_eq_right hne]

theorem closed_wf_cover : Closed (0 : ℝ) 0 ρ πA πB
    fun t : TS n KA KB => WF t.st.1 ∧ coverA t.st.1 = Finset.univ := by
  intro s t hs ht
  refine transS_eq_zero_of_move (P := fun L => WF L ∧ coverA L = Finset.univ) ?_ ?_ hs ht
  · intro p hp q hq
    exact ⟨hs.1.coal hp (Finset.mem_of_mem_erase hq), by rw [coverA_coal hp hq]; exact hs.2⟩
  · intro p hp
    obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
    exact ⟨hs.1.recomb hpL h1 h2, by rw [coverA_rec hs.1 hpL]; exact hs.2⟩

theorem rBlk_eq_rA {t : TS n KA KB} (hw : WF t.st.1)
    (hcov : coverA t.st.1 = Finset.univ) : rBlk t = rA (cladeFam n) t := by
  classical
  have hcard : nblk t = na t.st.1 := card_partA hw
  have hfilter : (t.st.1.filter fun p => p.1 ∈ cladeFam n) ⊆ carA t.st.1 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact mem_carA.2 ⟨hp.1, (mem_cladeFam.1 hp.2).1⟩
  by_cases ht : 2 ≤ nblk t
  · have hsets : (t.st.1.filter fun p => p.1 ∈ cladeFam n) = carA t.st.1 := by
      refine Finset.Subset.antisymm hfilter fun p hp => ?_
      obtain ⟨hpL, hpne⟩ := mem_carA.1 hp
      have hcard2 : 1 < (carA t.st.1).card := by
        rw [na] at hcard
        omega
      obtain ⟨q, hq, hqp⟩ : ∃ q ∈ carA t.st.1, q ≠ p := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard2
        by_cases hap : a = p
        · exact ⟨b, hb, fun hc => hab (by rw [hap, ← hc])⟩
        · exact ⟨a, ha, hap⟩
      obtain ⟨hqL, hqne⟩ := mem_carA.1 hq
      obtain ⟨k, hk⟩ := hqne
      have hdisj := hw.disjA q hqL p hpL hqp
      have hknp : k ∉ p.1 := fun hc => (Finset.disjoint_left.1 hdisj) hk hc
      refine Finset.mem_filter.2 ⟨hpL, mem_cladeFam.2 ⟨hpne, fun hc => ?_⟩⟩
      exact hknp (by rw [hc]; exact Finset.mem_univ k)
    rw [rBlk, ite_eq_left ht, rA, hsets, hcard, na]
  · have hz : nblk t ≤ 1 := by omega
    have hempty : (t.st.1.filter fun p => p.1 ∈ cladeFam n) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      rw [Finset.mem_filter] at hp
      obtain ⟨hpne, hpne2⟩ := mem_cladeFam.1 hp.2
      have hpA : p ∈ carA t.st.1 := mem_carA.2 ⟨hp.1, hpne⟩
      have hone : (carA t.st.1).card = 1 := by
        have h1 : 1 ≤ (carA t.st.1).card := Finset.card_pos.2 ⟨p, hpA⟩
        rw [na] at hcard
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hone
      have hpa : p = a := Finset.mem_singleton.1 (ha ▸ hpA)
      have hcv : coverA t.st.1 = p.1 := by
        refine Finset.Subset.antisymm (fun k hk => ?_) (fun k hk => ?_)
        · obtain ⟨q, hqL, hkq⟩ := mem_coverA.1 hk
          have hqA : q ∈ carA t.st.1 := mem_carA.2 ⟨hqL, ⟨k, hkq⟩⟩
          have : q = a := Finset.mem_singleton.1 (ha ▸ hqA)
          rw [hpa, ← this]
          exact hkq
        · exact mem_coverA.2 ⟨p, hp.1, hk⟩
      exact hpne2 (by rw [← hcv, hcov])
    rw [rBlk, ite_eq_right ht, rA, hempty, Finset.card_empty, Nat.cast_zero]

theorem coverA_fullState : coverA (fullState n) = Finset.univ := by
  ext k
  simp only [Finset.mem_univ, iff_true]
  exact mem_coverA.2 ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, Finset.mem_singleton_self k⟩

theorem partA_fullState :
    partA (fullState n) = Finset.univ.image fun k : Fin n => ({k} : Finset (Fin n)) := by
  have hcarA : carA (fullState n) = fullState n := by
    rw [carA, Finset.filter_true_of_mem]
    intro p hp
    obtain ⟨k, rfl⟩ := mem_fullState.1 hp
    exact Finset.singleton_nonempty k
  rw [partA, hcarA, fullState, Finset.image_image]
  rfl

theorem card_partA_fullState : (partA (fullState n)).card = n := by
  have hinj : Function.Injective fun k : Fin n => ({k} : Finset (Fin n)) := by
    intro k l hkl
    simpa using hkl
  rw [partA_fullState, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

theorem nblk_initT : nblk (⟨initT n KA KB⟩ : TS n KA KB) = n := card_partA_fullState

theorem lintegral_branchLen_uBlk (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB}
    (hw : WF s.st.1) (hcov : coverA s.st.1 = Finset.univ) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω ∂(argTrajT (0 : ℝ) 0 ρ πA πB h s))
      = ENNReal.ofReal (hpot (nblk s)) := by
  have hC : Closed (0 : ℝ) 0 ρ πA πB
      fun t : TS n KA KB => WF t.st.1 ∧ coverA t.st.1 = Finset.univ := closed_wf_cover
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdA (0 : ℝ) 0 ρ (cladeFam n) t :=
    holdA_nonneg le_rfl le_rfl h.rho (cladeFam n)
  have hu : ∀ t : TS n KA KB, (WF t.st.1 ∧ coverA t.st.1 = Finset.univ) →
      uBlk t = holdA (0 : ℝ) 0 ρ (cladeFam n) t
        + ∑ t', transS (0 : ℝ) 0 ρ πA πB t t' * uBlk t' := by
    intro t hCt
    rw [holdA, ← rBlk_eq_rA hCt.1 hCt.2]
    exact uBlk_step h hCt.1
  have hmain := lintegral_occAll_eq h hC hgnn hu (tendsto_mstep_uBlk_zero h hw) ⟨hw, hcov⟩
  have hb : ∀ ω : (_ : ℕ) → TS n KA KB, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
      = occAll (holdA (0 : ℝ) 0 ρ (cladeFam n)) ω := fun _ => rfl
  rw [lintegral_congr hb, hmain, uBlk]

theorem expected_total_length (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩))
      = ENNReal.ofReal (2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) := by
  have hinit : (⟨initT n KA KB⟩ : TS n KA KB).st.1 = fullState n := rfl
  have hw : WF (⟨initT n KA KB⟩ : TS n KA KB).st.1 := by
    rw [hinit]
    exact fullState_wf
  have hcov : coverA (⟨initT n KA KB⟩ : TS n KA KB).st.1 = Finset.univ := by
    rw [hinit]
    exact coverA_fullState
  rw [lintegral_branchLen_uBlk h hw hcov, nblk_initT, hpot]

theorem lintegral_branchLen_ne_top (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ ω, branchLen (0 : ℝ) 0 ρ (cladeFam n) ω
        ∂(argTrajT (0 : ℝ) 0 ρ πA πB h ⟨initT n KA KB⟩)) ≠ ⊤ := by
  rw [expected_total_length h]
  exact ENNReal.ofReal_ne_top

theorem hpot_two : hpot 2 = 2 := by
  rw [hpot]
  norm_num

theorem hpot_three : hpot 3 = 3 := by
  rw [hpot]
  norm_num [Finset.sum_range_succ]

end Rhone.Coalescent.BranchLengthMoments
