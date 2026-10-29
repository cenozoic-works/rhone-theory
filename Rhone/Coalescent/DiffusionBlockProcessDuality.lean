/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FiniteDimLaw
public import Rhone.Diffusion.WrightFisherUniqueness
public import Rhone.Coalescent.DiffusionBlockDuality
public import Rhone.Diffusion.WrightFisherPathLimit

/-!
# Moment duality of the Wright–Fisher diffusion and Kingman's block-counting chain

Source: mohle1999, Thm 2; etheridge2011, sec. 3.2; ethier_kurtz1986, ch. 4, sec. 4. -/

@[expose] public section

noncomputable section

namespace Rhone.Coalescent

open MeasureTheory Finset Set Diffusion MarkovChain Analysis Rhone.Combinatorics Probability
open scoped NNReal

def blockMoment (n : ℕ) (x : ℝ) (k : Fin (n + 1)) (t : ℝ) : ℝ :=
  ∑ j, (blockChain n).semigroup t k j * x ^ (j : ℕ)

theorem coalRate_cast_eq_wfMomentRate (k : ℕ) : ((coalRate k : ℚ) : ℝ) = wfMomentRate k := by
  simp only [coalRate, wfMomentRate]
  push_cast
  ring

theorem hasDerivAt_blockMoment (n : ℕ) (x : ℝ) (k k' : Fin (n + 1))
    (hk' : (k' : ℕ) = (k : ℕ) - 1) (t : ℝ) :
    HasDerivAt (blockMoment n x k)
      (wfMomentRate k * (blockMoment n x k' t - blockMoment n x k t)) t := by
  have h : HasDerivAt (blockMoment n x k)
      (∑ j, ((blockChain n).Q * (blockChain n).semigroup t) k j * x ^ (j : ℕ)) t := by
    unfold blockMoment
    exact HasDerivAt.fun_sum fun j _ =>
      ((blockChain n).hasDerivAt_semigroup' t k j).mul_const (x ^ (j : ℕ))
  convert h using 1
  have hswap : ∑ j, ((blockChain n).Q * (blockChain n).semigroup t) k j * x ^ (j : ℕ) =
      ∑ i, blockQ n k i * blockMoment n x i t := by
    simp only [Matrix.mul_apply, blockChain_Q, blockMoment, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hswap]
  by_cases hk : 1 ≤ (k : ℕ)
  · rw [sum_blockQ_mul n k hk (fun i => blockMoment n x i t), coalRate_cast_eq_wfMomentRate]
    have : (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)) = k' := Fin.ext hk'.symm
    rw [this]
  · have h0 : coalRate (k : ℕ) = 0 := coalRate_eq_zero (by omega)
    have h0' : wfMomentRate (k : ℕ) = 0 := by rw [← coalRate_cast_eq_wfMomentRate, h0]; simp
    simp [blockQ, h0, h0']

theorem continuous_blockMoment (n : ℕ) (x : ℝ) (k : Fin (n + 1)) :
    Continuous (blockMoment n x k) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_blockMoment n x k ⟨(k : ℕ) - 1, by omega⟩ rfl t).continuousAt

theorem blockMoment_integral_eq (n : ℕ) (x : ℝ) (k k' : Fin (n + 1))
    (hk' : (k' : ℕ) = (k : ℕ) - 1) (s t : ℝ) :
    blockMoment n x k t = blockMoment n x k s +
      ∫ u in s..t, wfMomentRate k * (blockMoment n x k' u - blockMoment n x k u) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_blockMoment n x k k' hk' u)
    ((continuous_const.mul ((continuous_blockMoment n x k').sub
      (continuous_blockMoment n x k))).intervalIntegrable _ _)]
  ring

theorem wfHistMoment_empty_zero {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (e : ℝ≥0 → ℕ) (m : ℕ) :
    wfHistMoment P ∅ e m 0 = x ^ m := by
  have := hP.isProbabilityMeasure
  have hx : x ∈ Icc (0 : ℝ) 1 := hP.start_mem
  simp only [wfHistMoment, Finset.prod_empty, mul_one, Real.toNNReal_zero]
  rw [integral_congr_ae (g := fun _ => clampUnit x ^ m)
    (hP.start.mono fun w hw => by simp only [hw])]
  simp [clampUnit_of_mem hx]

theorem wfHistMoment_eq_blockMoment_step {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (n : ℕ) (k k' : Fin (n + 1))
    (hk' : (k' : ℕ) = (k : ℕ) - 1)
    (hprev : ∀ u : ℝ, 0 ≤ u → wfMomentRate k *
      (wfHistMoment P ∅ (fun _ => 0) ((k : ℕ) - 1) u - blockMoment n x k' u) = 0) :
    ∀ t : ℝ, 0 ≤ t → wfHistMoment P ∅ (fun _ => 0) k t = blockMoment n x k t := by
  have := hP.isProbabilityMeasure
  let d : ℝ → ℝ := fun u => wfHistMoment P ∅ (fun _ => 0) k u - blockMoment n x k u
  have hdc : Continuous d :=
    (continuous_wfHistMoment P ∅ _ _).sub (continuous_blockMoment n x k)
  have h0 : wfHistMoment P ∅ (fun _ => 0) k 0 = blockMoment n x k 0 := by
    rw [wfHistMoment_empty_zero hP, blockMoment, blockChain_moment_zero]
  have heq : ∀ t, (0 : ℝ) ≤ t → d t = ∫ u in (0 : ℝ)..t, (-wfMomentRate k) * d u := by
    intro t ht
    have h1 := wfHistMoment_integral_eq hP ∅ (fun _ => 0) (s := 0) (by simp) (k : ℕ)
      (t := t) (by simpa using ht)
    simp only [NNReal.coe_zero] at h1
    have h2 := blockMoment_integral_eq n x k k' hk' 0 t
    simp only [d]
    rw [h1, h2, h0, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le ht] at hu
      have := hprev u hu.1
      linear_combination this
    · exact (continuous_const.mul ((continuous_wfHistMoment P ∅ _ _).sub
        (continuous_wfHistMoment P ∅ _ _))).intervalIntegrable _ _
    · exact (continuous_const.mul ((continuous_blockMoment n x k').sub
        (continuous_blockMoment n x k))).intervalIntegrable _ _
  intro t ht
  exact sub_eq_zero.mp (eq_zero_of_eq_integral hdc heq t ht)

theorem wfHistMoment_eq_blockMoment {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (n : ℕ) :
    ∀ (m : ℕ) (hm : m < n + 1) (t : ℝ), 0 ≤ t →
      wfHistMoment P ∅ (fun _ => 0) m t = blockMoment n x ⟨m, hm⟩ t := by
  intro m
  induction m with
  | zero =>
    intro hm
    exact wfHistMoment_eq_blockMoment_step hP n ⟨0, hm⟩ ⟨0, hm⟩ rfl
      fun u _ => by simp [wfMomentRate]
  | succ m ih =>
    intro hm
    refine wfHistMoment_eq_blockMoment_step hP n ⟨m + 1, hm⟩ ⟨m, by omega⟩ (by simp) ?_
    intro u hu
    simp only [Nat.add_sub_cancel]
    rw [ih (by omega) u hu, sub_self, mul_zero]

/-- Source: mohle1999, Thm 2; etheridge2011, sec. 3.2. -/
theorem integral_pow_eq_blockChain_semigroup {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (n : ℕ) (k : Fin (n + 1)) (t : ℝ≥0) :
    ∫ w, w t ^ (k : ℕ) ∂P = ∑ j, (blockChain n).semigroup t k j * x ^ (j : ℕ) := by
  have h := wfHistMoment_eq_blockMoment hP n k k.isLt t t.coe_nonneg
  simp only [Fin.eta, blockMoment] at h
  rw [← h]
  simp only [wfHistMoment, Finset.prod_empty, mul_one, Real.toNNReal_coe]
  refine integral_congr_ae ?_
  filter_upwards [hP.mem] with w hw
  rw [clampUnit_of_mem (hw t)]

theorem integral_comp_eq_of_hasFDD {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {R : RateChain S} {k : S} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {N : ℝ≥0 → Ω → S} (hN : R.HasFDD k μ N) (F : S → ℝ) (t : ℝ≥0) :
    ∫ ω, F (N t ω) ∂μ = ∑ j, R.semigroup t k j * F j := by
  have hmono : Monotone (fun _ : Fin 1 => t) := fun _ _ _ => le_rfl
  have hmap := hN.map_fdd 1 (fun _ => t) hmono
  beta_reduce at hmap
  have hNm : Measurable (fun ω (_ : Fin 1) => N t ω) :=
    measurable_pi_iff.2 fun _ => hN.measurable t
  have hFm : Measurable (fun y : Fin 1 → S => F (y 0)) :=
    (Measurable.of_discrete (f := F)).comp (measurable_pi_apply 0)
  have := R.isProbabilityMeasure_fdd k (t := fun _ : Fin 1 => (t : ℝ)) (fun _ _ _ => le_rfl)
    (fun _ => t.coe_nonneg)
  calc ∫ ω, F (N t ω) ∂μ
      = ∫ y, F (y 0) ∂(μ.map fun ω (_ : Fin 1) => N t ω) := by
        rw [integral_map hNm.aemeasurable hFm.aestronglyMeasurable]
    _ = ∫ y, F (y 0) ∂(R.fdd k fun _ : Fin 1 => (t : ℝ)) := by rw [hmap]
    _ = ∑ y : Fin 1 → S, (R.fdd k fun _ : Fin 1 => (t : ℝ)).real {y} • F (y 0) :=
        integral_fintype Integrable.of_finite
    _ = ∑ y : Fin 1 → S, R.semigroup t k (y 0) * F (y 0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [measureReal_def, RateChain.fdd_apply_singleton, ENNReal.toReal_ofReal
          (R.fddMass_nonneg k (fun _ _ _ => le_rfl) (fun _ => t.coe_nonneg) y),
          RateChain.fddMass_one, smul_eq_mul]
    _ = ∑ j, R.semigroup t k j * F j :=
        (Equiv.funUnique (Fin 1) S).sum_comp (fun j => R.semigroup t k j * F j)

/-- Source: mohle1999, Thm 2; etheridge2011, sec. 3.2. -/
theorem wf_blockChain_process_duality {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) {n : ℕ} (k : Fin (n + 1)) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {N : ℝ≥0 → Ω → Fin (n + 1)}
    (hN : (blockChain n).HasFDD k μ N) (t : ℝ≥0) :
    ∫ w, w t ^ (k : ℕ) ∂P = ∫ ω, x ^ (N t ω : ℕ) ∂μ := by
  rw [integral_pow_eq_blockChain_semigroup hP n k t,
    integral_comp_eq_of_hasFDD hN (fun j => x ^ (j : ℕ)) t]

theorem existsUnique_wfLaw_moment_duality {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃! P : Measure C(ℝ≥0, ℝ), IsWrightFisherDiffusionLaw x P ∧
      ∀ (n : ℕ) (k : Fin (n + 1)) (t : ℝ≥0),
        ∫ w, w t ^ (k : ℕ) ∂P = ∑ j, (blockChain n).semigroup t k j * x ^ (j : ℕ) := by
  obtain ⟨P, hP⟩ := Rhone.Diffusion.wrightFisherDiffusionLaw_exists hx
  exact ⟨P, ⟨hP, integral_pow_eq_blockChain_semigroup hP⟩, fun Q hQ => hQ.1.unique hP⟩

def blockMomentC (n : ℕ) (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (t : ℝ) : ℝ :=
  ∑ j, (blockChain n).semigroup t k j * c j

theorem hasDerivAt_blockMomentC (n : ℕ) (c : Fin (n + 1) → ℝ) (k k' : Fin (n + 1))
    (hk' : (k' : ℕ) = (k : ℕ) - 1) (t : ℝ) :
    HasDerivAt (blockMomentC n c k)
      (wfMomentRate k * (blockMomentC n c k' t - blockMomentC n c k t)) t := by
  have h : HasDerivAt (blockMomentC n c k)
      (∑ j, ((blockChain n).Q * (blockChain n).semigroup t) k j * c j) t := by
    unfold blockMomentC
    exact HasDerivAt.fun_sum fun j _ =>
      ((blockChain n).hasDerivAt_semigroup' t k j).mul_const (c j)
  convert h using 1
  have hswap : ∑ j, ((blockChain n).Q * (blockChain n).semigroup t) k j * c j =
      ∑ i, blockQ n k i * blockMomentC n c i t := by
    simp only [Matrix.mul_apply, blockChain_Q, blockMomentC, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hswap]
  by_cases hk : 1 ≤ (k : ℕ)
  · rw [sum_blockQ_mul n k hk (fun i => blockMomentC n c i t), coalRate_cast_eq_wfMomentRate]
    have : (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)) = k' := Fin.ext hk'.symm
    rw [this]
  · have h0 : coalRate (k : ℕ) = 0 := coalRate_eq_zero (by omega)
    have h0' : wfMomentRate (k : ℕ) = 0 := by rw [← coalRate_cast_eq_wfMomentRate, h0]; simp
    simp [blockQ, h0, h0']

theorem continuous_blockMomentC (n : ℕ) (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    Continuous (blockMomentC n c k) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_blockMomentC n c k ⟨(k : ℕ) - 1, by omega⟩ rfl t).continuousAt

theorem blockMomentC_shift_integral_eq (n : ℕ) (c : Fin (n + 1) → ℝ) (k k' : Fin (n + 1))
    (hk' : (k' : ℕ) = (k : ℕ) - 1) (s t : ℝ) :
    blockMomentC n c k (t - s) = c k +
      ∫ u in s..t, wfMomentRate k *
        (blockMomentC n c k' (u - s) - blockMomentC n c k (u - s)) := by
  have hd : ∀ u, HasDerivAt (fun u => blockMomentC n c k (u - s))
      (wfMomentRate k * (blockMomentC n c k' (u - s) - blockMomentC n c k (u - s))) u :=
    fun u => (hasDerivAt_blockMomentC n c k k' hk' (u - s)).comp_sub_const u s
  have hc : Continuous fun u => wfMomentRate k *
      (blockMomentC n c k' (u - s) - blockMomentC n c k (u - s)) :=
    continuous_const.mul (((continuous_blockMomentC n c k').comp (continuous_sub_right s)).sub
      ((continuous_blockMomentC n c k).comp (continuous_sub_right s)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable _ _)]
  have h0 : blockMomentC n c k (s - s) = c k := by
    simp [blockMomentC, RateChain.semigroup_zero, Matrix.one_apply]
  rw [h0]
  ring

theorem wfHistMoment_eq_blockChain_hist {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (S : Finset ℝ≥0) (e : ℝ≥0 → ℕ) {s : ℝ≥0}
    (hS : ∀ r ∈ S, r ≤ s) (n : ℕ) (m : ℕ) (hm : m < n + 1) {t : ℝ} (hst : (s : ℝ) ≤ t) :
    wfHistMoment P S e m t = ∑ j : Fin (n + 1),
      (blockChain n).semigroup (t - s) ⟨m, hm⟩ j * wfHistMoment P S e j s := by
  have := hP.isProbabilityMeasure
  obtain ⟨c, hc⟩ : ∃ c : Fin (n + 1) → ℝ,
      c = fun j : Fin (n + 1) => wfHistMoment P S e (j : ℕ) s := ⟨_, rfl⟩
  have hck : ∀ j, c j = wfHistMoment P S e j s := fun j => by rw [hc]
  have step : ∀ (k k' : Fin (n + 1)), (k' : ℕ) = (k : ℕ) - 1 →
      (∀ u : ℝ, (s : ℝ) ≤ u → wfMomentRate k *
        (wfHistMoment P S e ((k : ℕ) - 1) u - blockMomentC n c k' (u - s)) = 0) →
      ∀ t : ℝ, (s : ℝ) ≤ t → wfHistMoment P S e k t = blockMomentC n c k (t - s) := by
    intro k k' hk' hprev
    let d : ℝ → ℝ := fun u => wfHistMoment P S e k u - blockMomentC n c k (u - s)
    have hdc : Continuous d := (continuous_wfHistMoment P S e _).sub
      ((continuous_blockMomentC n c k).comp (continuous_sub_right _))
    have heq : ∀ t, (s : ℝ) ≤ t → d t = ∫ u in (s : ℝ)..t, (-wfMomentRate k) * d u := by
      intro t ht
      have h1 := wfHistMoment_integral_eq hP S e hS (k : ℕ) ht
      have h2 := blockMomentC_shift_integral_eq n c k k' hk' s t
      simp only [d]
      rw [h1, h2, hck, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun u hu => ?_
        rw [uIcc_of_le ht] at hu
        have := hprev u hu.1
        linear_combination this
      · exact (continuous_const.mul ((continuous_wfHistMoment P S e _).sub
          (continuous_wfHistMoment P S e _))).intervalIntegrable _ _
      · exact (continuous_const.mul
          (((continuous_blockMomentC n c k').comp (continuous_sub_right _)).sub
          ((continuous_blockMomentC n c k).comp (continuous_sub_right _)))).intervalIntegrable _ _
    intro t ht
    exact sub_eq_zero.mp (eq_zero_of_eq_integral hdc heq t ht)
  have hall : ∀ (m : ℕ) (hm : m < n + 1) (t : ℝ), (s : ℝ) ≤ t →
      wfHistMoment P S e m t = blockMomentC n c ⟨m, hm⟩ (t - s) := by
    intro m
    induction m with
    | zero =>
      intro hm
      exact step ⟨0, hm⟩ ⟨0, hm⟩ rfl fun u _ => by simp [wfMomentRate]
    | succ m ih =>
      intro hm
      refine step ⟨m + 1, hm⟩ ⟨m, by omega⟩ (by simp) ?_
      intro u hu
      simp only [Nat.add_sub_cancel]
      rw [ih (by omega) u hu, sub_self, mul_zero]
  rw [hall m hm t hst, blockMomentC]
  simp only [hck]

end Rhone.Coalescent

end
