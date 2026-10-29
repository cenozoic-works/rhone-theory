/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusCountChain
public import Rhone.Coalescent.TwoLocusCountLumping
public import Rhone.Coalescent.VariableSizeCoalescent
public import Rhone.Analysis.ExpNegMoment

/-!
# Joint Laplace transform of the two locus times of the labelled two-locus process

Source: griffiths1991_two_locus_graph, Thm 5, eq. (2.9), pp. 109–110. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy MeasureTheory Filter Topology
  Analysis.ExpNegMoment
open scoped ENNReal

variable {N : ℕ}

def startState (N : ℕ) : Finset (Lin N) :=
  Finset.univ.image fun i : Fin N => (({i} : Finset (Fin N)), ({i} : Finset (Fin N)))

theorem startState_wf (N : ℕ) : WF (startState N : Finset (Lin N)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact Or.inl (Finset.singleton_nonempty i)
  · intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun e => hpq (by rw [e])
    exact Finset.disjoint_singleton.2 hij
  · intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun e => hpq (by rw [e])
    exact Finset.disjoint_singleton.2 hij

theorem astCounts_startState (N : ℕ) :
    astCounts (startState N : Finset (Lin N)) = (0, 0, N) := by
  have hinj : Function.Injective
      fun i : Fin N => (({i} : Finset (Fin N)), ({i} : Finset (Fin N))) :=
    fun i j h => Finset.singleton_injective (congrArg Prod.fst h)
  have hcard : (startState N : Finset (Lin N)).card = N := by
    rw [startState, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have htype : ∀ p ∈ (startState N : Finset (Lin N)), linType p = (true, true) := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    simp [linType]
  have hc : ∀ t, linCount t (startState N : Finset (Lin N)) =
      if (true, true) = t then N else 0 := by
    intro t
    unfold linCount
    rw [Finset.sum_congr rfl (g := fun _ => if (true, true) = t then 1 else 0)
      fun p hp => by rw [htype p hp], Finset.sum_const, smul_eq_mul, hcard]
    split_ifs <;> simp
  simp [astCounts, hc]

theorem na_le_of_wf {L : Finset (Lin N)} (h : WF L) : na L ≤ N := by
  classical
  have hdisj := Finset.card_biUnion (s := carA L) (t := Prod.fst) (by
    intro p hp q hq hpq
    exact h.disjA p (carA_subset L hp) q (carA_subset L hq) hpq)
  have hle : ((carA L).biUnion Prod.fst).card ≤ N :=
    (Finset.card_le_univ _).trans (by simp)
  have hge : (carA L).card ≤ ∑ p ∈ carA L, p.1.card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p hp => Finset.card_pos.2 (mem_carA.1 hp).2
  unfold na
  omega

theorem nb_le_of_wf {L : Finset (Lin N)} (h : WF L) : nb L ≤ N := by
  classical
  have hdisj := Finset.card_biUnion (s := carB L) (t := Prod.snd) (by
    intro p hp q hq hpq
    exact h.disjB p (carB_subset L hp) q (carB_subset L hq) hpq)
  have hle : ((carB L).biUnion Prod.snd).card ≤ N :=
    (Finset.card_le_univ _).trans (by simp)
  have hge : (carB L).card ≤ ∑ p ∈ carB L, p.2.card := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun p hp => Finset.card_pos.2 (mem_carB.1 hp).2
  unfold nb
  omega

def wfBox {L : Finset (Lin N)} (h : WF L) : CountBox N :=
  (⟨(astCounts L).1, by have := na_le_of_wf h; rw [na_eq_astCounts] at this; omega⟩,
   ⟨(astCounts L).2.1, by have := nb_le_of_wf h; rw [nb_eq_astCounts] at this; omega⟩,
   ⟨(astCounts L).2.2, by have := na_le_of_wf h; rw [na_eq_astCounts] at this; omega⟩)

theorem boxVal_wfBox {L : Finset (Lin N)} (h : WF L) : boxVal (wfBox h) = astCounts L := rfl

theorem stepU_indicator_eq_zero_of_wf (ρ : ℝ) {L M : Finset (Lin N)} (h : WF L)
    (hM : ¬ WF M) : stepU (0 : ℝ) 0 ρ (fun M' => if M' = M then 1 else 0) L = 0 := by
  have h1 : ∑ p ∈ L, ∑ q ∈ L.erase p, (if coalL L p q = M then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      ite_eq_right fun (e : coalL L p q = M) =>
        absurd (e ▸ h.coal hp (Finset.mem_of_mem_erase hq) : WF M) hM
  have h4 : ∑ p ∈ carC L, (if recL L p = M then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun p hp => ite_eq_right fun (e : recL L p = M) => by
      obtain ⟨hpL, hp1, hp2⟩ := mem_carC.1 hp
      exact absurd (e ▸ h.recomb hpL hp1 hp2 : WF M) hM
  simp only [stepU]
  rw [h1, h4]
  simp

theorem argRateChain_Q_eq_zero_of_not_wf (ρ : ℝ) (hρ : 0 ≤ ρ) {L M : ASt N}
    (h : WF (L : Finset (Lin N))) (hM : ¬ WF (M : Finset (Lin N))) :
    (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M = 0 := by
  have hLM : (L : Finset (Lin N)) ≠ M := fun e => hM (e ▸ h)
  rw [argRateChain_Q_of_ne le_rfl le_rfl hρ hLM, stepU_indicator_eq_zero_of_wf ρ h hM,
    zero_div]

noncomputable def labCost (lam mu : ℝ) (L : ASt N) : ℝ :=
  countCost lam mu (astCounts (L : Finset (Lin N)))

theorem argRateChain_Q_eq_zero_of_cost (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) {L M : ASt N} (h : WF (L : Finset (Lin N))) (hL : labCost lam mu L = 0)
    (hM : labCost lam mu M ≠ 0) : (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M = 0 := by
  classical
  set g : Counts → ℝ := fun j => if countCost lam mu j = 0 then 0 else 1 with hg
  have hgen : countGen ρ g (astCounts (L : Finset (Lin N))) = 0 := by
    rw [countGen_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hc : coef ρ (astCounts (L : Finset (Lin N))) i = 0
    · rw [hc, zero_mul]
    · have hL' : countCost lam mu (astCounts (n := N) L) = 0 := hL
      have ht := countCost_tgt_eq_zero hl hm hL' hc
      simp [hg, ht, hL']
  have hsum := argRateChain_generator ρ hρ h g
  rw [hgen] at hsum
  have hterm : ∀ M' : ASt N, 0 ≤ (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M' *
      g (astCounts (M' : Finset (Lin N))) := by
    intro M'
    by_cases hLM : L = M'
    · subst hLM
      have : g (astCounts (L : Finset (Lin N))) = 0 := by
        simp only [hg]
        exact ite_eq_left hL
      rw [this, mul_zero]
    · exact mul_nonneg ((argRateChain 0 0 ρ le_rfl le_rfl hρ).off_diag_nonneg L M' hLM)
        (by simp only [hg]; split_ifs <;> norm_num)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun M' _ => hterm M').1 hsum M (mem_univ M)
  have hgM : g (astCounts (M : Finset (Lin N))) = 1 := by
    simp only [hg]
    exact ite_eq_right hM
  rwa [hgM, mul_one] at hz

noncomputable def wfSet (N : ℕ) : Finset (ASt N) := by
  classical exact univ.filter fun L : ASt N => WF (L : Finset (Lin N))

theorem mem_wfSet {L : ASt N} : L ∈ wfSet N ↔ WF (L : Finset (Lin N)) := by
  simp [wfSet]

noncomputable def wfZeroSet (N : ℕ) (lam mu : ℝ) : Finset (ASt N) := by
  classical exact univ.filter fun L : ASt N => WF (L : Finset (Lin N)) ∧ labCost lam mu L = 0

theorem mem_wfZeroSet {lam mu : ℝ} {L : ASt N} :
    L ∈ wfZeroSet N lam mu ↔ WF (L : Finset (Lin N)) ∧ labCost lam mu L = 0 := by
  simp [wfZeroSet]

theorem isClosedSet_wfSet (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (argRateChain (n := N) 0 0 ρ le_rfl le_rfl hρ).jumpChain.IsClosedSet (wfSet N) :=
  RateChain.isClosedSet_jumpChain _ fun _ hL _ hM =>
    argRateChain_Q_eq_zero_of_not_wf ρ hρ (mem_wfSet.1 hL) (mt mem_wfSet.2 hM)

theorem isClosedSet_wfZeroSet (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu) :
    (argRateChain (n := N) 0 0 ρ le_rfl le_rfl hρ).jumpChain.IsClosedSet
      (wfZeroSet N lam mu) := by
  refine RateChain.isClosedSet_jumpChain _ fun L hL M hM => ?_
  obtain ⟨hw, h0⟩ := mem_wfZeroSet.1 hL
  by_cases hwM : WF (M : Finset (Lin N))
  · have hcM : labCost lam mu M ≠ 0 := fun e => hM (mem_wfZeroSet.2 ⟨hwM, e⟩)
    exact argRateChain_Q_eq_zero_of_cost ρ hρ hl hm hw h0 hcM
  · exact argRateChain_Q_eq_zero_of_not_wf ρ hρ hw hwM

theorem argRateChain_rate_ne_zero_of_cost (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} {L : ASt N}
    (hc : labCost lam mu L ≠ 0) : (argRateChain 0 0 ρ le_rfl le_rfl hρ).rate L ≠ 0 := by
  have h2 : 2 ≤ (L : Finset (Lin N)).card := by
    by_contra hlt
    apply hc
    have hA := na_le_card (L : Finset (Lin N))
    have hB := nb_le_card (L : Finset (Lin N))
    rw [na_eq_astCounts (n := N) L] at hA
    rw [nb_eq_astCounts (n := N) L] at hB
    unfold labCost countCost
    rw [ite_eq_right fun h2 => absurd h2 (by omega), ite_eq_right fun h2 => absurd h2 (by omega),
      add_zero]
  rw [argRateChain_rate]
  unfold rateTot
  have hcc : (2 : ℝ) ≤ (((L : Finset (Lin N)).card * ((L : Finset (Lin N)).card - 1) : ℕ) : ℝ) := by
    have : 2 ≤ (L : Finset (Lin N)).card * ((L : Finset (Lin N)).card - 1) := by
      have h1 : 1 ≤ (L : Finset (Lin N)).card - 1 := by omega
      nlinarith
    exact_mod_cast this
  have htt : 0 ≤ ρ / 2 * ((tt (L : Finset (Lin N)) : ℕ) : ℝ) := by positivity
  refine (?_ : (0 : ℝ) < _).ne'
  simp only [zero_div, zero_mul, add_zero]
  linarith

noncomputable def countPsi (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (lam mu : ℝ) : CountBox N → ℝ :=
  (countChain ρ hρ N).laplace fun k => countCost lam mu (boxVal k)

theorem labCost_mul_countPsi_eq (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam) (hm : 0 ≤ mu)
    {L : Finset (Lin N)} (h : WF L) :
    labCost lam mu L * boxExt (countPsi ρ hρ N lam mu) (astCounts (L : Finset (Lin N))) =
      ∑ M : ASt N, (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M *
        boxExt (countPsi ρ hρ N lam mu) (astCounts (M : Finset (Lin N))) := by
  rw [argRateChain_generator ρ hρ h]
  change countCost lam mu (astCounts L) * _ = _
  rw [← boxVal_wfBox h, boxExt_boxVal]
  have ha : (boxVal (wfBox h)).1 + (boxVal (wfBox h)).2.2 ≤ N := by
    rw [boxVal_wfBox h, ← na_eq_astCounts L]; exact na_le_of_wf h
  have hb : (boxVal (wfBox h)).2.1 + (boxVal (wfBox h)).2.2 ≤ N := by
    rw [boxVal_wfBox h, ← nb_eq_astCounts L]; exact nb_le_of_wf h
  exact countCost_mul_laplace_eq_countGen ρ hρ hl hm ha hb

theorem argRateChain_laplace_eq_countPsi (ρ : ℝ) (hρ : 0 ≤ ρ) {lam mu : ℝ} (hl : 0 ≤ lam)
    (hm : 0 ≤ mu) {L : ASt N} (h : WF (L : Finset (Lin N))) :
    (argRateChain 0 0 ρ le_rfl le_rfl hρ).laplace (labCost lam mu) L =
      boxExt (countPsi ρ hρ N lam mu) (astCounts (L : Finset (Lin N))) := by
  set C := argRateChain (n := N) 0 0 ρ le_rfl le_rfl hρ with hC
  have hc : ∀ M : ASt N, 0 ≤ labCost lam mu M := fun M => countCost_nonneg hl hm _
  refine C.eqOn_of_holdFactor_fixed (u := C.laplace (labCost lam mu))
    (v := fun M : ASt N => boxExt (countPsi ρ hρ N lam mu) (astCounts (n := N) M)) hc
    (isClosedSet_wfSet ρ hρ)
    (fun M _ hM => argRateChain_rate_ne_zero_of_cost ρ hρ hM)
    (fun M _ => C.laplace_eq_holdFactor_mul hc M)
    (fun M hM => C.eq_holdFactor_mul_of_generator
      (u := fun M : ASt N => boxExt (countPsi ρ hρ N lam mu) (astCounts (n := N) M)) (hc M)
      fun _ => labCost_mul_countPsi_eq ρ hρ hl hm (mem_wfSet.1 hM))
    (fun M hM h0 => ?_) L (mem_wfSet.2 h)
  have hw := mem_wfSet.1 hM
  have h0' : countCost lam mu (boxVal (wfBox hw)) = 0 := h0
  rw [C.laplace_eq_one_of_isClosedSet hc (isClosedSet_wfZeroSet ρ hρ hl hm)
      (fun M' hM' => (mem_wfZeroSet.1 hM').2) (mem_wfZeroSet.2 ⟨hw, h0⟩)]
  change 1 = boxExt (countPsi ρ hρ N lam mu) (boxVal (wfBox hw))
  rw [boxExt_boxVal]
  exact (countChain_laplace_eq_one ρ hρ hl hm h0').symm

def lowA (N : ℕ) : Finset (ASt N) :=
  Finset.univ.filter fun L : ASt N => (carA (n := N) L).card ≤ 1

def lowB (N : ℕ) : Finset (ASt N) :=
  Finset.univ.filter fun L : ASt N => (carB (n := N) L).card ≤ 1

theorem labCost_eq (lam mu : ℝ) (L : ASt N) :
    labCost lam mu L =
      lam * (if L ∈ lowA N then 0 else 1) + mu * (if L ∈ lowB N then 0 else 1) := by
  have hA : L ∈ lowA N ↔ ¬ 2 ≤ (astCounts (L : Finset (Lin N))).1 +
      (astCounts (L : Finset (Lin N))).2.2 := by
    rw [← na_eq_astCounts (n := N) L]
    simp only [lowA, Finset.mem_filter, Finset.mem_univ, true_and, na]
    omega
  have hB : L ∈ lowB N ↔ ¬ 2 ≤ (astCounts (L : Finset (Lin N))).2.1 +
      (astCounts (L : Finset (Lin N))).2.2 := by
    rw [← nb_eq_astCounts (n := N) L]
    simp only [lowB, Finset.mem_filter, Finset.mem_univ, true_and, nb]
    omega
  unfold labCost countCost
  by_cases h1 : 2 ≤ (astCounts (L : Finset (Lin N))).1 + (astCounts (L : Finset (Lin N))).2.2 <;>
    by_cases h2 : 2 ≤ (astCounts (L : Finset (Lin N))).2.1 +
      (astCounts (L : Finset (Lin N))).2.2 <;>
    simp [h1, h2, hA, hB]

variable (R : RateChain (ASt N))

theorem discount_eq_expNeg (lam mu : ℕ) (p : (ℕ → ASt N) × (ℕ → ℝ)) (k : ℕ)
    (hp : 0 ≤ R.holdTime p k) :
    R.discount (labCost lam mu) p k =
      expNeg (if p.1 k ∈ lowA N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) ^ lam *
        expNeg (if p.1 k ∈ lowB N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) ^ mu := by
  have key : ∀ (b : Prop) [Decidable b],
      (if b then (0 : ℝ≥0∞) else ENNReal.ofReal (1 * R.holdTime p k)) =
        ENNReal.ofReal ((if b then 0 else 1) * R.holdTime p k) := by
    intro b _
    split_ifs <;> simp
  have hi : ∀ (b : Prop) [Decidable b], (0 : ℝ) ≤ if b then 0 else 1 := by
    intro b _
    split_ifs <;> norm_num
  rw [key, key, expNeg_ofReal (mul_nonneg (hi _) hp), expNeg_ofReal (mul_nonneg (hi _) hp),
    ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (pow_nonneg (Real.exp_pos _).le _)]
  unfold RateChain.discount
  rw [labCost_eq lam mu (p.1 k)]
  congr 1
  have hc : 0 ≤ ((lam : ℝ) * (if p.1 k ∈ lowA N then 0 else 1) +
      (mu : ℝ) * (if p.1 k ∈ lowB N then 0 else 1)) * R.holdTime p k :=
    mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hi _))
      (mul_nonneg (Nat.cast_nonneg _) (hi _))) hp
  rw [max_eq_right hc, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem laplaceCost_eq_expNeg_timeBefore (lam mu : ℕ) (p : (ℕ → ASt N) × (ℕ → ℝ))
    (hp : ∀ k, 0 ≤ p.2 k) :
    R.laplaceCost (labCost lam mu) p =
      expNeg (R.timeBefore (lowA N) p) ^ lam * expNeg (R.timeBefore (lowB N) p) ^ mu := by
  have ha : ∀ k, 0 ≤ R.holdTime p k := fun k => div_nonneg (hp k) (R.rate_nonneg _)
  have hfin : ∀ n, R.discountUpTo (labCost lam mu) p n =
      expNeg (∑ k ∈ range n,
          if p.1 k ∈ lowA N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) ^ lam *
        expNeg (∑ k ∈ range n,
          if p.1 k ∈ lowB N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) ^ mu := by
    intro n
    induction n with
    | zero => simp [RateChain.discountUpTo, expNeg_zero]
    | succ n ih =>
      have hs : R.discountUpTo (labCost lam mu) p (n + 1) =
          R.discountUpTo (labCost lam mu) p n * R.discount (labCost lam mu) p n :=
        prod_range_succ _ _
      rw [hs, ih, discount_eq_expNeg R lam mu p n (ha n), sum_range_succ, sum_range_succ,
        expNeg_add, expNeg_add, mul_pow, mul_pow]
      ring
  have hlimL : Tendsto (fun n => R.discountUpTo (labCost lam mu) p n) atTop
      (𝓝 (R.laplaceCost (labCost lam mu) p)) :=
    tendsto_atTop_iInf (R.discountUpTo_antitone (labCost lam mu) p)
  have hA : Tendsto (fun n => ∑ k ∈ range n,
      if p.1 k ∈ lowA N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) atTop
      (𝓝 (R.timeBefore (lowA N) p)) :=
    ENNReal.tendsto_nat_tsum _
  have hB : Tendsto (fun n => ∑ k ∈ range n,
      if p.1 k ∈ lowB N then 0 else ENNReal.ofReal (1 * R.holdTime p k)) atTop
      (𝓝 (R.timeBefore (lowB N) p)) :=
    ENNReal.tendsto_nat_tsum _
  have hA' := ((ENNReal.continuous_pow lam).tendsto _).comp
    ((continuous_expNeg.tendsto _).comp hA)
  have hB' := ((ENNReal.continuous_pow mu).tendsto _).comp
    ((continuous_expNeg.tendsto _).comp hB)
  have hR := ENNReal.Tendsto.mul hA' (Or.inr (ENNReal.pow_ne_top (expNeg_ne_top _))) hB'
    (Or.inr (ENNReal.pow_ne_top (expNeg_ne_top _)))
  exact tendsto_nhds_unique hlimL (hR.congr fun n => (hfin n).symm)

theorem ae_clock_nonneg_of_jumpHoldLaw (L : ASt N) :
    ∀ᵐ p ∂(R.jumpHoldLaw L), ∀ k, 0 ≤ p.2 k :=
  Measure.quasiMeasurePreserving_snd.ae Rhone.Coalescent.ae_clockLaw_nonneg

theorem lintegral_expNeg_timeBefore (ρ : ℝ) (hρ : 0 ≤ ρ) (lam mu : ℕ) {L : ASt N}
    (h : WF (L : Finset (Lin N))) :
    ∫⁻ p, expNeg ((argRateChain 0 0 ρ le_rfl le_rfl hρ).timeBefore (lowA N) p) ^ lam *
        expNeg ((argRateChain 0 0 ρ le_rfl le_rfl hρ).timeBefore (lowB N) p) ^ mu
        ∂((argRateChain 0 0 ρ le_rfl le_rfl hρ).jumpHoldLaw L) =
      ENNReal.ofReal (boxExt (countPsi ρ hρ N lam mu) (astCounts (n := N) L)) := by
  set C := argRateChain (n := N) 0 0 ρ le_rfl le_rfl hρ with hC
  have hint : ∫⁻ p, expNeg (C.timeBefore (lowA N) p) ^ lam *
      expNeg (C.timeBefore (lowB N) p) ^ mu ∂(C.jumpHoldLaw L) =
      ∫⁻ p, C.laplaceCost (labCost lam mu) p ∂(C.jumpHoldLaw L) :=
    lintegral_congr_ae ((ae_clock_nonneg_of_jumpHoldLaw C L).mono fun p hp =>
      (laplaceCost_eq_expNeg_timeBefore C lam mu p hp).symm)
  have hle : ∫⁻ p, C.laplaceCost (labCost lam mu) p ∂(C.jumpHoldLaw L) ≤ 1 :=
    (lintegral_mono fun p => iInf_le _ 0).trans (C.lintegral_discountUpTo_le_one _ _ 0)
  rw [hint, ← argRateChain_laplace_eq_countPsi ρ hρ (Nat.cast_nonneg lam) (Nat.cast_nonneg mu) h,
    RateChain.laplace, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]

theorem lintegral_expNeg_timeBefore_startState (ρ : ℝ) (hρ : 0 ≤ ρ) (lam mu : ℕ) :
    ∫⁻ p, expNeg ((argRateChain 0 0 ρ le_rfl le_rfl hρ).timeBefore (lowA N) p) ^ lam *
        expNeg ((argRateChain 0 0 ρ le_rfl le_rfl hρ).timeBefore (lowB N) p) ^ mu
        ∂((argRateChain 0 0 ρ le_rfl le_rfl hρ).jumpHoldLaw (startState N)) =
      ENNReal.ofReal (boxExt (countPsi ρ hρ N lam mu) (0, 0, N)) := by
  rw [lintegral_expNeg_timeBefore ρ hρ lam mu (startState_wf N), astCounts_startState]

end Rhone.Coalescent.IntervalCounts
