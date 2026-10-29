/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusArgJumpHold
public import Rhone.Coalescent.TwoLocusIntervalGenerator
public import Rhone.Coalescent.FullARGMrcaPath
public import Rhone.MarkovChain.FullARGWeightedExit
public import Rhone.Coalescent.FullARGPairTimeKernel
public import Rhone.Coalescent.FullARGTermination

/-!
# Joint Laplace transform of the two MRCA times of the unrestricted backward sampler

Source: griffiths1991_two_locus_graph, Thm 5, eq. (2.9), pp. 109–110. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open Finset MeasureTheory Filter Topology Rhone.LinearAlgebra MarkovChain IntervalProcess
  MarkovChain.IntervalProcess SmcSupport Analysis.ExpNegMoment
open scoped ENNReal

theorem eventKernel_lintegral_time_mul (R : ℝ) (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {g : State → ℝ≥0∞} (hg : Measurable g)
    (hgt : ∀ t s, g (atTime t s) = g s) :
    ∫⁻ w, f w.1.1 * g w.1 ∂eventKernel false R z =
      (∫⁻ u, f (z.1.1 - Real.log u / (totalRate false R z.1 : ℝ)) ∂unitUniform) *
        ∫⁻ w, g w.1 ∂eventKernel false R z := by
  classical
  set lam := (totalRate false R z.1 : ℝ) with hlam
  have hF : Measurable fun w : AugmentedState => f w.1.1 * g w.1 :=
    (hf.comp measurable_fst.fst).mul (hg.comp measurable_fst)
  have hG : Measurable fun w : AugmentedState => g w.1 := hg.comp measurable_fst
  have htime : ∀ (a : ActionIndex z.1) (v : ℝ × ℝ),
      (argActionStep R z a v).1.1 = z.1.1 - Real.log v.1 / lam := by
    intro a v
    cases a <;> rfl
  have hstate : ∀ (a : ActionIndex z.1) (v : ℝ × ℝ),
      g (argActionStep R z a v).1 = g (argActionStep R z a (1, v.2)).1 := by
    intro a v
    cases a <;> simp only [argActionStep, hgt]
  have hGa : ∀ a : ActionIndex z.1, Measurable fun v2 : ℝ => g (argActionStep R z a (1, v2)).1 :=
    fun a => hg.comp (measurable_fst.comp
      ((argActionStep_measurable R z a).comp (measurable_const.prodMk measurable_id)))
  have hft : Measurable fun u : ℝ => f (z.1.1 - Real.log u / lam) :=
    hf.comp (measurable_const.sub (Real.measurable_log.div_const _))
  have hone : ∀ a : ActionIndex z.1,
      ∫⁻ w, f w.1.1 * g w.1 ∂(unitUniform.prod unitUniform).map (argActionStep R z a) =
        (∫⁻ u, f (z.1.1 - Real.log u / lam) ∂unitUniform) *
          ∫⁻ v2, g (argActionStep R z a (1, v2)).1 ∂unitUniform := by
    intro a
    rw [lintegral_map hF (argActionStep_measurable R z a)]
    have e : ∀ v : ℝ × ℝ, f (argActionStep R z a v).1.1 * g (argActionStep R z a v).1 =
        f (z.1.1 - Real.log v.1 / lam) * g (argActionStep R z a (1, v.2)).1 := fun v => by
      rw [htime a v, hstate a v]
    rw [lintegral_congr e]
    exact lintegral_prod_mul (f := fun u => f (z.1.1 - Real.log u / lam))
      (g := fun v2 => g (argActionStep R z a (1, v2)).1) hft.aemeasurable (hGa a).aemeasurable
  have htwo : ∀ a : ActionIndex z.1,
      ∫⁻ w, g w.1 ∂(unitUniform.prod unitUniform).map (argActionStep R z a) =
        ∫⁻ v2, g (argActionStep R z a (1, v2)).1 ∂unitUniform := by
    intro a
    rw [lintegral_map hG (argActionStep_measurable R z a), lintegral_congr (hstate a)]
    have e2 := lintegral_prod_mul (μ := unitUniform) (ν := unitUniform)
      (f := fun _ : ℝ => (1 : ℝ≥0∞)) (g := fun v2 => g (argActionStep R z a (1, v2)).1)
      aemeasurable_const (hGa a).aemeasurable
    simp only [one_mul, lintegral_one, measure_univ] at e2
    exact e2
  rw [eventKernel_ARG_action_mixture R z (by omega), lintegral_finsetSum_measure,
    lintegral_finsetSum_measure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lintegral_smul_measure, lintegral_smul_measure, hone a, htwo a, smul_eq_mul, smul_eq_mul]
  ring

theorem lintegral_clockDiscount (t lam c : ℝ) (hlam : 0 < lam) (hc : 0 ≤ c) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(c * ((t - Real.log u / lam) - t)))) ∂unitUniform =
      ENNReal.ofReal (lam / (lam + c)) := by
  have hr : -1 < c / lam := by
    have := div_nonneg hc hlam.le
    linarith
  have hpt : Set.EqOn (fun u : ℝ => ENNReal.ofReal (Real.exp (-(c * ((t - Real.log u / lam) - t)))))
      (fun u : ℝ => ENNReal.ofReal (u ^ (c / lam))) (Set.Ioo 0 1) := by
    intro u hu
    simp only
    rw [Real.rpow_def_of_pos hu.1]
    congr 2
    field_simp
    ring
  have hint : IntegrableOn (fun u : ℝ => u ^ (c / lam)) (Set.Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' hr)
  rw [unitUniform, setLIntegral_congr_fun measurableSet_Ioo hpt,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => (Real.rpow_pos_of_pos hu.1 _).le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith)]
  field_simp
  ring

noncomputable def samplerCost (x y : ℝ) (lam mu : ℕ) (s : State) : ℕ :=
  (if 2 ≤ carrierCount x s then lam else 0) + (if 2 ≤ carrierCount y s then mu else 0)

theorem samplerCost_measurable (x y : ℝ) (lam mu : ℕ) : Measurable (samplerCost x y lam mu) :=
  (measurable_of_countable
    (fun p : ℕ × ℕ => (if 2 ≤ p.1 then lam else 0) + (if 2 ≤ p.2 then mu else 0))).comp
    ((carrierCount_measurable x).prodMk (carrierCount_measurable y))

theorem samplerCost_eq (x y : ℝ) (lam mu : ℕ) (s : State) :
    (samplerCost x y lam mu s : ℝ) = countCost lam mu (typeCounts x y s) := by
  unfold samplerCost countCost
  rw [← carrierCount_eq_typeCounts_fst x y s, ← carrierCount_eq_typeCounts_snd x y s]
  split_ifs <;> simp

theorem samplerCost_le (x y : ℝ) (lam mu : ℕ) (s : State) :
    samplerCost x y lam mu s ≤ lam + mu := by
  unfold samplerCost
  split_ifs <;> omega

theorem countPsi_mem_Icc (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (lam mu : ℝ) (k : CountBox N) :
    0 ≤ countPsi ρ hρ N lam mu k ∧ countPsi ρ hρ N lam mu k ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold countPsi RateChain.laplace
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (((lintegral_mono fun p => iInf_le _ 0).trans
      ((countChain ρ hρ N).lintegral_discountUpTo_le_one _ _ 0)).trans_eq
      ENNReal.ofReal_one.symm)

theorem boxExt_countPsi_mem_Icc (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (lam mu : ℝ) (t : Counts) :
    0 ≤ boxExt (countPsi ρ hρ N lam mu) t ∧ boxExt (countPsi ρ hρ N lam mu) t ≤ 1 := by
  unfold boxExt
  split_ifs
  · exact countPsi_mem_Icc ρ hρ N lam mu _
  · exact ⟨le_rfl, zero_le_one⟩

noncomputable def samplerPsi (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (x y : ℝ) (lam mu : ℕ)
    (s : State) : ℝ :=
  boxExt (countPsi ρ hρ N lam mu) (typeCounts x y s)

theorem samplerPsi_measurable (ρ : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) (x y : ℝ) (lam mu : ℕ) :
    Measurable (samplerPsi ρ hρ N x y lam mu) :=
  (measurable_of_countable _).comp (typeCounts_measurable x y)

noncomputable def stateBox {N : ℕ} {x y : ℝ} {s : State} (hx : carrierCount x s ≤ N)
    (hy : carrierCount y s ≤ N) : CountBox N :=
  (⟨(typeCounts x y s).1, by rw [carrierCount_eq_typeCounts_fst x y s] at hx; omega⟩,
   ⟨(typeCounts x y s).2.1, by rw [carrierCount_eq_typeCounts_snd x y s] at hy; omega⟩,
   ⟨(typeCounts x y s).2.2, by rw [carrierCount_eq_typeCounts_fst x y s] at hx; omega⟩)

theorem boxVal_stateBox {N : ℕ} {x y : ℝ} {s : State} (hx : carrierCount x s ≤ N)
    (hy : carrierCount y s ≤ N) : boxVal (stateBox hx hy) = typeCounts x y s := rfl

theorem samplerPsi_eq_one (ρ : ℝ) (hρ : 0 ≤ ρ) {N : ℕ} {x y : ℝ} (lam mu : ℕ) {s : State}
    (hx : carrierCount x s ≤ N) (hy : carrierCount y s ≤ N) (hx1 : carrierCount x s ≤ 1)
    (hy1 : carrierCount y s ≤ 1) : samplerPsi ρ hρ N x y lam mu s = 1 := by
  have h0 : countCost lam mu (boxVal (stateBox hx hy)) = 0 := by
    rw [boxVal_stateBox, ← samplerCost_eq]
    unfold samplerCost
    rw [ite_eq_right fun h => absurd h (by omega), ite_eq_right fun h => absurd h (by omega)]
    simp
  unfold samplerPsi
  rw [← boxVal_stateBox hx hy, boxExt_boxVal]
  exact countChain_laplace_eq_one ρ hρ (Nat.cast_nonneg lam) (Nat.cast_nonneg mu) h0

theorem eventKernel_discount_samplerPsi (R : ℝ) (hR : 0 ≤ R) {x y : ℝ} (hxy : x < y)
    (hρ : 0 ≤ R * (y - x)) (N lam mu : ℕ) (z : AugmentedState)
    (hzx : carrierCount x z.1 ≤ N) (hzy : carrierCount y z.1 ≤ N) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-((samplerCost x y lam mu z.1 : ℝ) * (w.1.1 - z.1.1)))) *
        ENNReal.ofReal (samplerPsi (R * (y - x)) hρ N x y lam mu w.1) ∂eventKernel false R z =
      ENNReal.ofReal (samplerPsi (R * (y - x)) hρ N x y lam mu z.1) := by
  classical
  set ψ := samplerPsi (R * (y - x)) hρ N x y lam mu with hψ
  set c : ℝ := (samplerCost x y lam mu z.1 : ℝ) with hcdef
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hψm : Measurable ψ := samplerPsi_measurable _ hρ N x y lam mu
  have hbd : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1 := fun s => boxExt_countPsi_mem_Icc _ hρ N _ _ _
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(c * (t - z.1.1)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_id.sub_const _).const_mul c).neg)
  have hg : Measurable fun s : State => ENNReal.ofReal (ψ s) := ENNReal.measurable_ofReal.comp hψm
  by_cases hm : 2 ≤ z.1.2.2.1
  · have ht : 0 < (totalRate false R z.1 : ℝ) := by
      exact_mod_cast unrestricted_totalRate_positive R z.1 hm
    rw [eventKernel_lintegral_time_mul R z hm hf hg (fun t s => rfl),
      lintegral_clockDiscount z.1.1 _ c ht hc]
    have hint : Integrable (fun w : AugmentedState => ψ w.1) (eventKernel false R z) :=
      (integrable_const (1 : ℝ)).mono' (hψm.comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hbd _).1]
          exact (hbd _).2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => (hbd w.1).1),
      ← ENNReal.ofReal_mul (div_nonneg ht.le (by linarith))]
    congr 1
    have hgen := totalRate_mul_eventKernel_sub_eq_countGen R hR x y hxy z hm
      (boxExt (countPsi (R * (y - x)) hρ N lam mu))
      ⟨1, fun k => by
        rw [abs_of_nonneg (boxExt_countPsi_mem_Icc _ hρ N _ _ k).1]
        exact (boxExt_countPsi_mem_Icc _ hρ N _ _ k).2⟩
    have heq : countCost lam mu (boxVal (stateBox hzx hzy)) *
        countPsi (R * (y - x)) hρ N lam mu (stateBox hzx hzy) =
          countGen (R * (y - x)) (boxExt (countPsi (R * (y - x)) hρ N lam mu))
            (boxVal (stateBox hzx hzy)) := by
      have ha : (boxVal (stateBox hzx hzy)).1 + (boxVal (stateBox hzx hzy)).2.2 ≤ N := by
        rw [boxVal_stateBox, ← carrierCount_eq_typeCounts_fst]
        exact hzx
      have hb : (boxVal (stateBox hzx hzy)).2.1 + (boxVal (stateBox hzx hzy)).2.2 ≤ N := by
        rw [boxVal_stateBox, ← carrierCount_eq_typeCounts_snd]
        exact hzy
      exact countCost_mul_laplace_eq_countGen _ hρ (Nat.cast_nonneg lam) (Nat.cast_nonneg mu)
        ha hb
    have hψz : ψ z.1 = countPsi (R * (y - x)) hρ N lam mu (stateBox hzx hzy) := by
      rw [hψ, samplerPsi, ← boxVal_stateBox hzx hzy, boxExt_boxVal]
    rw [boxVal_stateBox, ← samplerCost_eq, ← hψz] at heq
    have hgen' : (totalRate false R z.1 : ℝ) * (∫ w, ψ w.1 ∂eventKernel false R z - ψ z.1) =
        c * ψ z.1 := by
      rw [hcdef, heq]
      exact hgen
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
    linear_combination hgen'
  · have hstep : ∀ u, sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := fun u => by
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    have hF : Measurable fun w : AugmentedState =>
        ENNReal.ofReal (Real.exp (-(c * (w.1.1 - z.1.1)))) * ENNReal.ofReal (ψ w.1) :=
      (hf.comp measurable_fst.fst).mul (hg.comp measurable_fst)
    have hs : Measurable fun u : Noise => sampleStep false R z.1 u :=
      (sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)
    rw [eventKernel_apply, lintegral_map hF hs]
    simp only [hstep, sub_self, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      lintegral_const, measure_univ, mul_one]

theorem pathLaw_lintegral_mul_sum_eval_succ {S : Type*} [MeasurableSpace S]
    (P : DiscreteProcess S) (x0 : S) (n : ℕ) (s : Finset ℕ) {a b : ℕ → S → ℝ≥0∞}
    (ha : ∀ j, Measurable (a j)) (hb : ∀ j, Measurable (b j)) {W : (ℕ → S) → ℝ≥0∞}
    (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] W) :
    ∫⁻ ω, W ω * ∑ j ∈ s, a j (ω n) * b j (ω (n + 1)) ∂P.pathLaw x0 =
      ∫⁻ ω, W ω * ∑ j ∈ s, a j (ω n) * ∫⁻ v, b j v ∂P.step (ω n) ∂P.pathLaw x0 := by
  have hle := (Filtration.piLE (X := fun _ : ℕ => S)).le n
  have hWm : Measurable W := hW.mono hle le_rfl
  have hWj : ∀ j, Measurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      fun ω => W ω * a j (ω n) := fun j =>
    hW.mul ((ha j).comp (DiscreteProcess.measurable_eval_piLE n))
  have hm1 : ∀ j, Measurable fun ω : ℕ → S => W ω * a j (ω n) * b j (ω (n + 1)) := fun j =>
    (hWm.mul ((ha j).comp (measurable_pi_apply n))).mul ((hb j).comp (measurable_pi_apply _))
  have hm2 : ∀ j, Measurable fun ω : ℕ → S =>
      W ω * a j (ω n) * ∫⁻ v, b j v ∂P.step (ω n) := fun j =>
    (hWm.mul ((ha j).comp (measurable_pi_apply n))).mul
      ((hb j).lintegral_kernel.comp (measurable_pi_apply n))
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [lintegral_finsetSum _ fun j _ => hm1 j, lintegral_finsetSum _ fun j _ => hm2 j]
  exact Finset.sum_congr rfl fun j _ => pathLaw_lintegral_mul_eval_succ P x0 n (hb j) (hWj j)

noncomputable def samplerDiscount (x y : ℝ) (lam mu : ℕ) (ω : EventPath) (n : ℕ) : ℝ≥0∞ :=
  ∏ k ∈ range n, ENNReal.ofReal (Real.exp
    (-((samplerCost x y lam mu (ω k).1 : ℝ) * ((ω (k + 1)).1.1 - (ω k).1.1))))

theorem samplerDiscount_measurable (x y : ℝ) (lam mu : ℕ) (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      fun ω => samplerDiscount x y lam mu ω n := by
  have hev : ∀ k ≤ n, Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      fun ω : EventPath => ω k := fun k hk =>
    (DiscreteProcess.measurable_eval_piLE k).mono
      ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).mono hk) le_rfl
  have hc : Measurable fun s : State => (samplerCost x y lam mu s : ℝ) :=
    (measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (samplerCost_measurable x y lam mu)
  unfold samplerDiscount
  refine Finset.measurable_prod _ fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hc.comp (measurable_fst.comp (hev k (by omega)))).mul
      ((measurable_fst.fst.comp (hev (k + 1) hk')).sub
        (measurable_fst.fst.comp (hev k (by omega))))).neg)

theorem discountFactor_eq_sum (x y : ℝ) (lam mu : ℕ) (z w : AugmentedState) (p : ℝ) :
    ENNReal.ofReal (Real.exp (-((samplerCost x y lam mu z.1 : ℝ) * (w.1.1 - z.1.1)))) *
        ENNReal.ofReal p =
      ∑ j ∈ range (lam + mu + 1),
        (if samplerCost x y lam mu z.1 = j then ENNReal.ofReal (Real.exp (j * z.1.1)) else 0) *
          (ENNReal.ofReal (Real.exp (-(j * w.1.1))) * ENNReal.ofReal p) := by
  rw [Finset.sum_eq_single (samplerCost x y lam mu z.1)]
  · rw [ite_eq_left rfl, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · intro j _ hj
    rw [ite_eq_right_iff.2 fun h => absurd h.symm hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (samplerCost_le x y lam mu _))) h

theorem lintegral_samplerDiscount_mul_samplerPsi (R : ℝ) (hR : 0 ≤ R) (qx qy : GenomicProbe)
    (hxy : qx < qy) (hρ : 0 ≤ R * ((qy.val : ℝ) - (qx.val : ℝ))) (N lam mu : ℕ) (n : ℕ) :
    ∫⁻ ω, samplerDiscount (qx.val : ℝ) (qy.val : ℝ) lam mu ω n *
        ENNReal.ofReal (samplerPsi _ hρ N (qx.val : ℝ) (qy.val : ℝ) lam mu (ω n).1)
        ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (samplerPsi _ hρ N (qx.val : ℝ) (qy.val : ℝ) lam mu (initialState N)) := by
  classical
  have hxy' : (qx.val : ℝ) < (qy.val : ℝ) := Rat.cast_lt.mpr hxy
  set ψ := samplerPsi _ hρ N (qx.val : ℝ) (qy.val : ℝ) lam mu with hψ
  have hψm : Measurable fun s => ENNReal.ofReal (ψ s) :=
    ENNReal.measurable_ofReal.comp (samplerPsi_measurable _ hρ N _ _ lam mu)
  have hbound : ∀ q : GenomicProbe, ∀ᵐ ω ∂(eventProcess false R).pathLaw
      (initialState N, (0, .inl ())), ∀ k, carrierCount (q.val : ℝ) (ω k).1 ≤ N := by
    intro q
    filter_upwards [eventProcess_chronologicalAncestryPath N false R,
      eventProcess_twoSampleTransition R (initialState N, (0, .inl ())) q] with ω h hq k
    induction k with
    | zero =>
      rw [h.1]
      exact (carrierCount_initialState N _ (by exact_mod_cast q.property.1)
        (by exact_mod_cast q.property.2)).le
    | succ k ih => exact (hq k).2.1.trans ih
  set a : ℕ → AugmentedState → ℝ≥0∞ := fun j z =>
    if samplerCost (qx.val : ℝ) (qy.val : ℝ) lam mu z.1 = j then
      ENNReal.ofReal (Real.exp (j * z.1.1)) else 0 with ha_def
  set b : ℕ → AugmentedState → ℝ≥0∞ := fun j w =>
    ENNReal.ofReal (Real.exp (-(j * w.1.1))) * ENNReal.ofReal (ψ w.1) with hb_def
  have ha : ∀ j, Measurable (a j) := fun j =>
    Measurable.ite ((samplerCost_measurable _ _ lam mu).comp measurable_fst
      (measurableSet_singleton j))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_fst.fst.const_mul _))) measurable_const
  have hb : ∀ j, Measurable (b j) := fun j =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_fst.fst.const_mul _).neg)).mul (hψm.comp measurable_fst)
  have hinner : ∀ z : AugmentedState,
      ∑ j ∈ range (lam + mu + 1), a j z * ∫⁻ v, b j v ∂eventKernel false R z =
        ∫⁻ v, ENNReal.ofReal (Real.exp
          (-((samplerCost (qx.val : ℝ) (qy.val : ℝ) lam mu z.1 : ℝ) * (v.1.1 - z.1.1)))) *
            ENNReal.ofReal (ψ v.1) ∂eventKernel false R z := by
    intro z
    calc ∑ j ∈ range (lam + mu + 1), a j z * ∫⁻ v, b j v ∂eventKernel false R z
        = ∑ j ∈ range (lam + mu + 1), ∫⁻ v, a j z * b j v ∂eventKernel false R z :=
          Finset.sum_congr rfl fun j _ => (lintegral_const_mul _ (hb j)).symm
      _ = ∫⁻ v, ∑ j ∈ range (lam + mu + 1), a j z * b j v ∂eventKernel false R z :=
          (lintegral_finsetSum _ fun j _ => measurable_const.mul (hb j)).symm
      _ = _ := lintegral_congr fun v => (discountFactor_eq_sum _ _ lam mu z v (ψ v.1)).symm
  induction n with
  | zero =>
    simp only [samplerDiscount, Finset.range_zero, Finset.prod_empty, one_mul]
    have e := lintegral_map (μ := (eventProcess false R).pathLaw (initialState N, (0, .inl ())))
      (hψm.comp measurable_fst) (measurable_pi_apply 0)
    rw [(eventProcess false R).map_eval_zero, lintegral_dirac] at e
    exact e.symm
  | succ n ih =>
    have hsplit : ∀ ω : EventPath,
        samplerDiscount (qx.val : ℝ) (qy.val : ℝ) lam mu ω (n + 1) *
            ENNReal.ofReal (ψ (ω (n + 1)).1) =
          samplerDiscount (qx.val : ℝ) (qy.val : ℝ) lam mu ω n *
            ∑ j ∈ range (lam + mu + 1), a j (ω n) * b j (ω (n + 1)) := fun ω => by
      simp only [samplerDiscount, Finset.prod_range_succ]
      rw [mul_assoc]
      exact congrArg _ (discountFactor_eq_sum _ _ lam mu (ω n) (ω (n + 1)) _)
    rw [lintegral_congr hsplit, pathLaw_lintegral_mul_sum_eval_succ _ _ n _ ha hb
      (samplerDiscount_measurable _ _ lam mu n)]
    refine (lintegral_congr_ae ?_).trans ih
    filter_upwards [hbound qx, hbound qy] with ω h1 h2
    exact congrArg (samplerDiscount (qx.val : ℝ) (qy.val : ℝ) lam mu ω n * ·)
      ((hinner (ω n)).trans (eventKernel_discount_samplerPsi R hR hxy' hρ N lam mu (ω n)
        (h1 n) (h2 n)))

theorem sum_ite_lt_mul_sub (t : ℕ → ℝ) (c : ℝ) {K n : ℕ} (hK : K ≤ n) :
    ∑ k ∈ range n, (if k < K then c else 0) * (t (k + 1) - t k) = c * (t K - t 0) := by
  have h1 : ∑ k ∈ range K, (if k < K then c else 0) * (t (k + 1) - t k) =
      ∑ k ∈ range K, c * (t (k + 1) - t k) :=
    Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
  have h2 : ∑ k ∈ Ico K n, (if k < K then c else 0) * (t (k + 1) - t k) = 0 :=
    Finset.sum_eq_zero fun k hk => by simp [not_lt.2 (Finset.mem_Ico.1 hk).1]
  rw [← Finset.sum_range_add_sum_Ico _ hK, h1, h2, add_zero, ← Finset.mul_sum,
    Finset.sum_range_sub]

theorem samplerDiscount_eq_of_le (x y : ℝ) (lam mu : ℕ) (ω : EventPath) {Kx Ky n : ℕ}
    (hx : ∀ k, 2 ≤ carrierCount x (ω k).1 ↔ k < Kx)
    (hy : ∀ k, 2 ≤ carrierCount y (ω k).1 ↔ k < Ky) (hnx : Kx ≤ n) (hny : Ky ≤ n) :
    samplerDiscount x y lam mu ω n = ENNReal.ofReal (Real.exp (-((lam : ℝ) *
      ((ω Kx).1.1 - (ω 0).1.1) + (mu : ℝ) * ((ω Ky).1.1 - (ω 0).1.1)))) := by
  have hc : ∀ k, (samplerCost x y lam mu (ω k).1 : ℝ) =
      (if k < Kx then (lam : ℝ) else 0) + (if k < Ky then (mu : ℝ) else 0) := by
    intro k
    unfold samplerCost
    simp only [hx k, hy k]
    split_ifs <;> simp
  unfold samplerDiscount
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le, ← Real.exp_sum,
    Finset.sum_neg_distrib]
  simp_rw [hc, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_lt_mul_sub (fun k => (ω k).1.1) _ hnx, sum_ite_lt_mul_sub (fun k => (ω k).1.1) _ hny]

theorem lintegral_expNeg_mrca (R : ℝ) (hR : 0 ≤ R) (qx qy : GenomicProbe) (hxy : qx < qy)
    (hρ : 0 ≤ R * ((qy.val : ℝ) - (qx.val : ℝ))) (N lam mu : ℕ) :
    ∫⁻ ω, expNeg (⨆ i, ⨆ j, genealogyObservation N ω qx i j) ^ lam *
        expNeg (⨆ i, ⨆ j, genealogyObservation N ω qy i j) ^ mu
        ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (boxExt (countPsi _ hρ N lam mu) (0, 0, N)) := by
  classical
  have hx0 : (0 : ℝ) ≤ (qx.val : ℝ) := by exact_mod_cast qx.property.1
  have hx1 : (qx.val : ℝ) < 1 := by exact_mod_cast qx.property.2
  have hy0 : (0 : ℝ) ≤ (qy.val : ℝ) := by exact_mod_cast qy.property.1
  have hy1 : (qy.val : ℝ) < 1 := by exact_mod_cast qy.property.2
  set x : ℝ := (qx.val : ℝ) with hx
  set y : ℝ := (qy.val : ℝ) with hy
  set ψ := samplerPsi _ hρ N x y lam mu with hψ
  have hψ0 : ψ (initialState N) = boxExt (countPsi _ hρ N lam mu) (0, 0, N) := by
    rw [hψ, samplerPsi, typeCounts_initialState N x y hx0 hx1 hy0 hy1]
  rw [← hψ0]
  set F : ℕ → EventPath → ℝ≥0∞ := fun n ω =>
    samplerDiscount x y lam mu ω n * ENNReal.ofReal (ψ (ω n).1) with hF
  have hmart : ∀ n, ∫⁻ ω, F n ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (ψ (initialState N)) := fun n =>
    lintegral_samplerDiscount_mul_samplerPsi R hR qx qy hxy hρ N lam mu n
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ((samplerDiscount_measurable x y lam mu n).mono
      ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).le n) le_rfl).mul
      ((ENNReal.measurable_ofReal.comp (samplerPsi_measurable _ hρ N x y lam mu)).comp
        (measurable_fst.comp (measurable_pi_apply n)))
  have hgood := (eventProcess_chronologicalAncestryPath N false R).and
    ((eventProcess_twoSampleTransition R (initialState N, (0, .inl ())) qx).and
    ((eventProcess_twoSampleTransition R (initialState N, (0, .inl ())) qy).and
    ((eventProcess_labelMergeTransition R (initialState N, (0, .inl ())) qx).and
    ((eventProcess_labelMergeTransition R (initialState N, (0, .inl ())) qy).and
      (eventProcess_liveCount_reaches_one N R hR)))))
  have hmono : ∀ ω : EventPath, ChronologicalAncestryPath N ω → Monotone fun k => (ω k).1.1 :=
    fun ω h => monotone_nat_of_le_succ fun k => (h.2 k).1
  have htime0 : ∀ ω : EventPath, ChronologicalAncestryPath N ω → (ω 0).1.1 = 0 := by
    intro ω h
    rw [h.1]
    rfl
  have hccN : ∀ ω : EventPath, ChronologicalAncestryPath N ω → ∀ q : GenomicProbe,
      (∀ k, twoSampleTransition q (ω k, ω (k + 1))) →
        ∀ k, carrierCount (q.val : ℝ) (ω k).1 ≤ N := by
    intro ω h q hq k
    induction k with
    | zero =>
      rw [h.1]
      exact (carrierCount_initialState N _ (by exact_mod_cast q.property.1)
        (by exact_mod_cast q.property.2)).le
    | succ k ih => exact (hq k).2.1.trans ih
  have hbound : ∀ n, ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      F n ω ≤ 1 := by
    intro n
    filter_upwards [hgood] with ω hω
    have h := hω.1
    refine mul_le_one' (Finset.prod_le_one fun k _ => ?_) (ENNReal.ofReal_le_one.2
      (boxExt_countPsi_mem_Icc _ hρ N _ _ _).2)
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg
      (Nat.cast_nonneg _) (sub_nonneg.2 ((h.2 k).1)))))
  have hlim : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      Tendsto (fun n => F n ω) atTop (𝓝 (expNeg (⨆ i, ⨆ j, genealogyObservation N ω qx i j) ^ lam *
        expNeg (⨆ i, ⨆ j, genealogyObservation N ω qy i j) ^ mu)) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨h, hqx, hqy, hlx, hly, hterm⟩ := hω
    obtain ⟨Kx, hbx, hKx, hMx⟩ := iSup_genealogyObservation_eq_time h qx hqx hlx hterm
    obtain ⟨Ky, hby, hKy, hMy⟩ := iSup_genealogyObservation_eq_time h qy hqy hly hterm
    have hanti : ∀ q : GenomicProbe, (∀ k, twoSampleTransition q (ω k, ω (k + 1))) →
        Antitone fun k => carrierCount (q.val : ℝ) (ω k).1 :=
      fun q hq => antitone_nat_of_succ_le fun k => (hq k).2.1
    have hiffx : ∀ k, 2 ≤ carrierCount x (ω k).1 ↔ k < Kx := fun k =>
      ⟨fun h2 => not_le.1 fun hk => by
        have : carrierCount x (ω k).1 ≤ 1 := (hanti qx hqx hk).trans hKx
        omega,
        fun hk => hbx k hk⟩
    have hiffy : ∀ k, 2 ≤ carrierCount y (ω k).1 ↔ k < Ky := fun k =>
      ⟨fun h2 => not_le.1 fun hk => by
        have : carrierCount y (ω k).1 ≤ 1 := (hanti qy hqy hk).trans hKy
        omega,
        fun hk => hby k hk⟩
    have ht0 := htime0 ω h
    have htx : 0 ≤ (ω Kx).1.1 := ht0 ▸ hmono ω h (Nat.zero_le Kx)
    have hty : 0 ≤ (ω Ky).1.1 := ht0 ▸ hmono ω h (Nat.zero_le Ky)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨max Kx Ky, fun n hn => ?_⟩)
    have hnx : Kx ≤ n := (le_max_left _ _).trans hn
    have hny : Ky ≤ n := (le_max_right _ _).trans hn
    change _ = samplerDiscount x y lam mu ω n * ENNReal.ofReal (ψ (ω n).1)
    rw [samplerDiscount_eq_of_le x y lam mu ω hiffx hiffy hnx hny, hψ,
      samplerPsi_eq_one _ hρ lam mu (hccN ω h qx hqx n) (hccN ω h qy hqy n)
        ((hanti qx hqx hnx).trans hKx) ((hanti qy hqy hny).trans hKy),
      ENNReal.ofReal_one, mul_one, hMx, hMy, expNeg_ofReal htx, expNeg_ofReal hty, ht0,
      sub_zero, sub_zero, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (pow_nonneg (Real.exp_pos _).le _), ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    ring
  have hT := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hFm hbound
    (by simp) hlim
  simp only [hmart] at hT
  exact (tendsto_nhds_unique hT tendsto_const_nhds)

end Rhone.Coalescent.IntervalCounts
