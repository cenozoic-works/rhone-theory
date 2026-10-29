/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.MartingaleProblem
public import Rhone.Probability.ContinuousPathMoments
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Data.Finset.Max

/-!
# Uniqueness of the law of the Wright–Fisher diffusion

Source: ethier_kurtz1986, ch. 4. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Polynomial Filter Topology Set Probability
open scoped NNReal BoundedContinuousFunction

noncomputable def wfMomentRate (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / 2

theorem wfGenerator_monomial (n : ℕ) (y : ℝ) :
    wfGenerator (fun y => (X ^ n : ℝ[X]).eval y) y = wfMomentRate n * (y ^ (n - 1) - y ^ n) := by
  rw [wfGenerator_eval]
  rcases n with _ | _ | n
  · simp [wfMomentRate]
  · simp [wfMomentRate]
  · simp only [derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul,
      eval_C, eval_pow, eval_X, wfMomentRate]
    push_cast
    ring

theorem prod_clampUnit_pow_mem {ι : Type*} (s : Finset ι) (f : ι → ℝ) (m : ι → ℕ) :
    ∏ i ∈ s, clampUnit (f i) ^ m i ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => pow_nonneg (clampUnit_mem _).1 _,
    Finset.prod_le_one₀ (fun _ _ => pow_nonneg (clampUnit_mem _).1 _)
      fun _ _ => pow_le_one₀ (clampUnit_mem _).1 (clampUnit_mem _).2⟩

theorem abs_prod_clampUnit_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (m : ι → ℕ) :
    |∏ i ∈ s, clampUnit (f i) ^ m i| ≤ 1 := by
  have h := prod_clampUnit_pow_mem s f m
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

noncomputable def clampProd {k : ℕ} (m : Fin k → ℕ) : (Fin k → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => ∏ j, clampUnit (y j) ^ m j,
      continuous_finsetProd _ fun j _ => (continuous_clampUnit.comp (continuous_apply j)).pow _⟩
    2 (fun y z => by
      have h1 := abs_prod_clampUnit_pow_le Finset.univ y m
      have h2 := abs_prod_clampUnit_pow_le Finset.univ z m
      rw [abs_le] at h1 h2
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

noncomputable def wfHistMoment (P : Measure C(ℝ≥0, ℝ)) (S : Finset ℝ≥0) (e : ℝ≥0 → ℕ) (n : ℕ)
    (u : ℝ) : ℝ :=
  ∫ w, clampUnit (w u.toNNReal) ^ n * ∏ t ∈ S, clampUnit (w t) ^ e t ∂P

theorem continuous_clampPath (n : ℕ) :
    Continuous fun p : C(ℝ≥0, ℝ) × ℝ => clampUnit (p.1 p.2.toNNReal) ^ n :=
  ((continuous_clampUnit.comp (continuous_eval.comp
    (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))).pow n

theorem continuous_histProd (S : Finset ℝ≥0) (e : ℝ≥0 → ℕ) :
    Continuous fun w : C(ℝ≥0, ℝ) => ∏ t ∈ S, clampUnit (w t) ^ e t :=
  continuous_finsetProd _ fun t _ =>
    (continuous_clampUnit.comp (continuous_eval_const t)).pow _

theorem continuous_wfHistMoment (P : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure P] (S : Finset ℝ≥0)
    (e : ℝ≥0 → ℕ) (n : ℕ) : Continuous (wfHistMoment P S e n) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun u => ?_) (fun u => ?_)
    (integrable_const _) (Eventually.of_forall fun w => ?_)
  · exact (((continuous_clampPath n).comp (continuous_id.prodMk continuous_const)).mul
      (continuous_histProd S e)).aestronglyMeasurable
  · refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |clampUnit (w u.toNNReal) ^ n| ≤ 1 := by
      simpa using abs_prod_clampUnit_pow_le {()} (fun _ => w u.toNNReal) (fun _ => n)
    have h2 := abs_prod_clampUnit_pow_le S (fun t => w t) e
    calc |clampUnit (w u.toNNReal) ^ n| * |∏ t ∈ S, clampUnit (w t) ^ e t| ≤ 1 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · exact ((continuous_clampPath n).comp (continuous_const.prodMk continuous_id)).mul
      continuous_const

theorem wfHistMoment_integral_eq {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (S : Finset ℝ≥0) (e : ℝ≥0 → ℕ) {s : ℝ≥0}
    (hS : ∀ t ∈ S, t ≤ s) (n : ℕ) {t : ℝ} (hst : (s : ℝ) ≤ t) :
    wfHistMoment P S e n t = wfHistMoment P S e n s +
      ∫ u in (s : ℝ)..t,
        wfMomentRate n * (wfHistMoment P S e (n - 1) u - wfHistMoment P S e n u) := by
  have := hP.isProbabilityMeasure
  have ht0 : 0 ≤ t := le_trans s.2 hst
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht't : (t' : ℝ) = t := Real.coe_toNNReal _ ht0
  have hst' : s ≤ t' := by rw [← NNReal.coe_le_coe, ht't]; exact hst
  set k := S.card
  let r : Fin k → ℝ≥0 := fun j => (S.equivFin.symm j : ℝ≥0)
  have hr : ∀ j, r j ≤ s := fun j => hS _ (S.equivFin.symm j).2
  set H : C(ℝ≥0, ℝ) → ℝ := fun w => ∏ t ∈ S, clampUnit (w t) ^ e t with hHdef
  have hH : ∀ w : C(ℝ≥0, ℝ), clampProd (fun j => e (r j)) (fun j => w (r j)) = H w := by
    intro w
    simp only [clampProd, BoundedContinuousFunction.mkOfBound, BoundedContinuousFunction.coe_mk,
      hHdef, r]
    rw [← Finset.prod_coe_sort S]
    exact Equiv.prod_comp S.equivFin.symm (fun i : S => clampUnit (w i) ^ e i)
  have hm := hP.martingale _ ⟨X ^ n, rfl⟩ s t' hst' k r hr (clampProd fun j => e (r j))
  let F : C(ℝ≥0, ℝ) → ℝ → ℝ := fun w u =>
    wfMomentRate n * (clampUnit (w u.toNNReal) ^ (n - 1) - clampUnit (w u.toNNReal) ^ n)
  have hFc : Continuous (Function.uncurry F) :=
    continuous_const.mul ((continuous_clampPath (n - 1)).sub (continuous_clampPath n))
  have hFb : ∀ w u, |F w u| ≤ |wfMomentRate n| * 2 := by
    intro w u
    have h1 := clampUnit_mem (w u.toNNReal)
    have ha : clampUnit (w u.toNNReal) ^ (n - 1) ∈ Icc (0 : ℝ) 1 :=
      ⟨pow_nonneg h1.1 _, pow_le_one₀ h1.1 h1.2⟩
    have hb : clampUnit (w u.toNNReal) ^ n ∈ Icc (0 : ℝ) 1 :=
      ⟨pow_nonneg h1.1 _, pow_le_one₀ h1.1 h1.2⟩
    simp only [F, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hae : ∀ᵐ w ∂P,
      ((fun y => (X ^ n : ℝ[X]).eval y) (w t') - (fun y => (X ^ n : ℝ[X]).eval y) (w s) -
          ∫ u in (s : ℝ)..t', wfGenerator (fun y => (X ^ n : ℝ[X]).eval y) (w u.toNNReal)) *
          clampProd (fun j => e (r j)) (fun j => w (r j)) =
        clampUnit (w t') ^ n * H w - clampUnit (w s) ^ n * H w -
          (∫ u in (s : ℝ)..t, F w u) * H w := by
    filter_upwards [hP.mem] with w hw
    rw [hH w, ht't]
    have hint : (∫ u in (s : ℝ)..t, wfGenerator (fun y => (X ^ n : ℝ[X]).eval y) (w u.toNNReal)) =
        ∫ u in (s : ℝ)..t, F w u := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [F, wfGenerator_monomial, clampUnit_of_mem (hw _)]
    rw [hint]
    simp only [eval_pow, eval_X, clampUnit_of_mem (hw _)]
    ring
  rw [integral_congr_ae hae] at hm
  have hHb : ∀ w, |H w| ≤ 1 := fun w => abs_prod_clampUnit_pow_le S (fun t => w t) e
  have hHc : Continuous H := continuous_histProd S e
  have hint_pow : ∀ (m : ℕ) (u : ℝ≥0),
      Integrable (fun w : C(ℝ≥0, ℝ) => clampUnit (w u) ^ m * H w) P := by
    intro m u
    refine Integrable.of_bound (C := 1)
      (((continuous_clampUnit.comp (continuous_eval_const u)).pow m).mul
        hHc).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |clampUnit (w u) ^ m| ≤ 1 := by
      simpa using abs_prod_clampUnit_pow_le {()} (fun _ => w u) (fun _ => m)
    calc |clampUnit (w u) ^ m| * |H w| ≤ 1 * 1 := mul_le_mul h1 (hHb w) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hIc : Continuous fun w => ∫ u in (s : ℝ)..t, F w u :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc _ _
  have hint_drift : Integrable (fun w => (∫ u in (s : ℝ)..t, F w u) * H w) P := by
    refine Integrable.of_bound (C := |wfMomentRate n| * 2 * |t - s| * 1)
      (hIc.mul hHc).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (hHb w) (abs_nonneg _) (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := t)
      (f := F w) (C := |wfMomentRate n| * 2) (fun u _ => by rw [Real.norm_eq_abs]; exact hFb w u)
    simpa [Real.norm_eq_abs] using this
  rw [integral_sub (f := fun w => clampUnit (w t') ^ n * H w - clampUnit (w s) ^ n * H w)
      ((hint_pow n t').sub (hint_pow n s)) hint_drift,
    integral_sub (hint_pow n t') (hint_pow n s)] at hm
  have hswap : ∫ w, (∫ u in (s : ℝ)..t, F w u) * H w ∂P =
      ∫ u in (s : ℝ)..t, wfMomentRate n *
        (wfHistMoment P S e (n - 1) u - wfHistMoment P S e n u) := by
    simp_rw [← intervalIntegral.integral_mul_const]
    simp_rw [intervalIntegral.integral_of_le hst]
    rw [integral_integral_swap]
    · refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      have h1 := integral_sub (hint_pow (n - 1) u.toNNReal) (hint_pow n u.toNNReal)
      have h2 := integral_const_mul (μ := P) (wfMomentRate n)
        (fun w => clampUnit (w u.toNNReal) ^ (n - 1) * H w - clampUnit (w u.toNNReal) ^ n * H w)
      change _ = wfMomentRate n * ((∫ w, clampUnit (w u.toNNReal) ^ (n - 1) * H w ∂P) -
        ∫ w, clampUnit (w u.toNNReal) ^ n * H w ∂P)
      rw [← h1, ← h2]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [F]
      ring
    · refine Integrable.of_bound (C := |wfMomentRate n| * 2 * 1)
        ((hFc.mul (hHc.comp continuous_fst)).aestronglyMeasurable) (Eventually.of_forall ?_)
      rintro ⟨w, u⟩
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb w u) (hHb w) (abs_nonneg _) (by positivity)
  rw [hswap] at hm
  have hts : t.toNNReal = t' := rfl
  have hss : ((s : ℝ)).toNNReal = s := Real.toNNReal_coe
  have e1 : wfHistMoment P S e n t = ∫ w, clampUnit (w t') ^ n * H w ∂P := rfl
  have e2 : wfHistMoment P S e n s = ∫ w, clampUnit (w s) ^ n * H w ∂P := by
    unfold wfHistMoment; rw [hss]
  rw [e1, e2]
  linarith

theorem eq_zero_of_eq_integral {d : ℝ → ℝ} {a s : ℝ} (hd : Continuous d)
    (h : ∀ t, s ≤ t → d t = ∫ u in s..t, a * d u) : ∀ t, s ≤ t → d t = 0 := by
  intro T hT
  have hc : Continuous fun u => a * d u := continuous_const.mul hd
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := d) (f' := fun u => a * d u)
    (δ := 0) (K := |a|) (ε := 0) (a := s) (b := T) hd.continuousOn
    (fun y hy => by
      have hG := ((hc.integral_hasStrictDerivAt s y).hasDerivAt).hasDerivWithinAt (s := Ici y)
      refine hG.congr_of_mem (fun z hz => h z (le_trans hy.1 hz)) Set.self_mem_Ici)
    (by rw [h s le_rfl, intervalIntegral.integral_same, norm_zero])
    (fun y _ => by rw [norm_mul, Real.norm_eq_abs, add_zero])
    T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at key
  exact norm_le_zero_iff.mp key

theorem IsWrightFisherDiffusionLaw.pathMoment_eq {x : ℝ} {P Q : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (hQ : IsWrightFisherDiffusionLaw x Q)
    (I : Finset ℝ≥0) (e : ℝ≥0 → ℕ) : pathMoment P I e = pathMoment Q I e := by
  have := hP.isProbabilityMeasure
  have := hQ.isProbabilityMeasure
  classical
  induction I using Finset.induction_on_max generalizing e with
  | empty => simp [pathMoment]
  | insert a S hlt ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    let s0 : ℝ≥0 := if hS : S.Nonempty then S.max' hS else 0
    have hS0 : ∀ t ∈ S, t ≤ s0 := by
      intro t ht
      have hne : S.Nonempty := ⟨t, ht⟩
      simp only [s0, hne, ↓reduceDIte]
      exact S.le_max' t ht
    have hs0a : s0 ≤ a := by
      by_cases hne : S.Nonempty
      · simp only [s0, hne, ↓reduceDIte]; exact (hlt _ (S.max'_mem hne)).le
      · simp only [s0, hne, ↓reduceDIte]; exact zero_le
    have hbase : ∀ m : ℕ, wfHistMoment P S e m s0 = wfHistMoment Q S e m s0 := by
      intro m
      by_cases hne : S.Nonempty
      · have hs0S : s0 ∈ S := by simp only [s0, hne, ↓reduceDIte]; exact S.max'_mem hne
        have hrw : ∀ (M : Measure C(ℝ≥0, ℝ)), wfHistMoment M S e m s0 =
            pathMoment M S (e + Pi.single s0 m) := by
          intro M
          simp only [wfHistMoment, pathMoment, Real.toNNReal_coe]
          refine integral_congr_ae (Eventually.of_forall fun w => ?_)
          have hsingle : ∏ t ∈ S, clampUnit (w t) ^ (Pi.single s0 m : ℝ≥0 → ℕ) t =
              clampUnit (w s0) ^ m := by
            rw [Finset.prod_eq_single_of_mem s0 hs0S]
            · simp
            · intro b _ hb; simp [hb]
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, hsingle]
          ring
        rw [hrw, hrw, ih]
      · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hs00 : s0 = 0 := by simp only [s0, hne, ↓reduceDIte]
        have hrw : ∀ (M : Measure C(ℝ≥0, ℝ)), IsWrightFisherDiffusionLaw x M →
            wfHistMoment M S e m s0 = clampUnit x ^ m := by
          intro M hM
          have := hM.isProbabilityMeasure
          simp only [wfHistMoment, hSe, Finset.prod_empty, mul_one, hs00, NNReal.coe_zero,
            Real.toNNReal_zero]
          rw [integral_congr_ae (g := fun _ => clampUnit x ^ m)
            (hM.start.mono fun w hw => by simp only [hw])]
          simp
        rw [hrw P hP, hrw Q hQ]
    have hall : ∀ m : ℕ, ∀ t : ℝ, (s0 : ℝ) ≤ t →
        wfHistMoment P S e m t = wfHistMoment Q S e m t := by
      intro m
      induction m with
      | zero =>
        intro t _
        have h0 : ∀ (M : Measure C(ℝ≥0, ℝ)) (u : ℝ), wfHistMoment M S e 0 u = pathMoment M S e := by
          intro M u; simp [wfHistMoment, pathMoment]
        rw [h0, h0, ih]
      | succ m ihm =>
        let d : ℝ → ℝ := fun u => wfHistMoment P S e (m + 1) u - wfHistMoment Q S e (m + 1) u
        have hdc : Continuous d :=
          (continuous_wfHistMoment P S e _).sub (continuous_wfHistMoment Q S e _)
        have heq : ∀ t, (s0 : ℝ) ≤ t → d t = ∫ u in (s0 : ℝ)..t, (-wfMomentRate (m + 1)) * d u := by
          intro t ht
          simp only [d]
          rw [wfHistMoment_integral_eq hP S e hS0 (m + 1) ht,
            wfHistMoment_integral_eq hQ S e hS0 (m + 1) ht, hbase (m + 1)]
          rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub]
          · refine intervalIntegral.integral_congr fun u hu => ?_
            rw [uIcc_of_le ht] at hu
            simp only [Nat.add_sub_cancel]
            rw [ihm u hu.1]
            ring
          · exact (continuous_const.mul ((continuous_wfHistMoment P S e _).sub
              (continuous_wfHistMoment P S e _))).intervalIntegrable _ _
          · exact (continuous_const.mul ((continuous_wfHistMoment Q S e _).sub
              (continuous_wfHistMoment Q S e _))).intervalIntegrable _ _
        intro t ht
        exact sub_eq_zero.mp (eq_zero_of_eq_integral hdc heq t ht)
    have hrw : ∀ (M : Measure C(ℝ≥0, ℝ)),
        pathMoment M (insert a S) e = wfHistMoment M S e (e a) a := by
      intro M
      simp only [pathMoment, wfHistMoment, Finset.prod_insert haS, Real.toNNReal_coe]
    rw [hrw, hrw]
    exact hall (e a) a (NNReal.coe_le_coe.mpr hs0a)

/-- Source: ethier_kurtz1986, ch. 4. -/
theorem IsWrightFisherDiffusionLaw.unique {x : ℝ} {P Q : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (hQ : IsWrightFisherDiffusionLaw x Q) : P = Q := by
  have := hP.isProbabilityMeasure
  have := hQ.isProbabilityMeasure
  exact eq_of_pathMoment_eq hP.mem hQ.mem (hP.pathMoment_eq hQ)

end Rhone.Diffusion
