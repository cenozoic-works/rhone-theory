/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.WeakSelectionResponse
public import Rhone.Diffusion.TwoLocusMoran
public import Rhone.Diffusion.VectorChainLimit
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The two-locus diffusion with selection as a process

Source: ethier_kurtz1986, ch. 4, sec. 3, sec. 9. -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory MvPolynomial Set LinearAlgebra.Recursion
open scoped NNReal BoundedContinuousFunction

variable {KA KB : ℕ}

/-- Source: ethier_kurtz1986, ch. 4, sec. 3. -/
structure IsTwoLocusProcessLaw (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (i₀ : Fin KA) (σ : ℝ) (ν : Measure (Diffusion.gameteSimplex KA KB))
    (P : Measure C(ℝ≥0, Fin KA × Fin KB → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  initial : P.map (fun w => w 0) = ν.map Subtype.val
  mem : ∀ᵐ w ∂P, ∀ t, w t ∈ Diffusion.gameteSimplex KA KB
  martingale : ∀ f : MvPolynomial (Fin KA × Fin KB) ℝ, ∀ s t : ℝ≥0, s ≤ t →
    ∀ (k : ℕ) (r : Fin k → ℝ≥0), (∀ j, r j ≤ s) →
    ∀ h : (Fin k → Fin KA × Fin KB → ℝ) →ᵇ ℝ,
      ∫ w, (eval (w t) f - eval (w s) f -
          ∫ u in (s : ℝ)..t, eval (w u.toNNReal)
              (Diffusion.twoLocusGenerator θA θB ρ πA πB i₀ σ f)) *
        h (fun j => w (r j)) ∂P = 0

def IsProcessStationary (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (i₀ : Fin KA)
    (σ : ℝ) (ν : Measure (Diffusion.gameteSimplex KA KB))
        (P : Measure C(ℝ≥0, Fin KA × Fin KB → ℝ)) :
    Prop :=
  IsTwoLocusProcessLaw θA θB ρ πA πB i₀ σ ν P ∧
    ∀ t : ℝ≥0, P.map (fun w => w t) = ν.map Subtype.val

section Easy

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} {i₀ : Fin KA} {σ : ℝ}
  {ν : Measure (Diffusion.gameteSimplex KA KB)} {P : Measure C(ℝ≥0, Fin KA × Fin KB → ℝ)}

theorem exists_bound_eval_gameteSimplex (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ B, ∀ x ∈ Diffusion.gameteSimplex KA KB, |eval x f| ≤ B := by
  obtain ⟨B, hB⟩ := Diffusion.isCompact_gameteSimplex.exists_bound_of_continuousOn
    (MvPolynomial.continuous_eval f).continuousOn
  exact ⟨B, fun x hx => by rw [← Real.norm_eq_abs]; exact hB x hx⟩

/-- Source: ethier_kurtz1986, ch. 4, sec. 9. -/
theorem IsProcessStationary.isStationaryLaw (h : IsProcessStationary θA θB ρ πA πB i₀ σ ν P) :
    Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ ν := by
  obtain ⟨hP, hst⟩ := h
  have := hP.isProbabilityMeasure
  have hmarg : ∀ (t : ℝ≥0) (F : (Fin KA × Fin KB → ℝ) → ℝ), Continuous F →
      ∫ w, F (w t) ∂P = ∫ x, F (x : Fin KA × Fin KB → ℝ) ∂ν := by
    intro t F hF
    rw [← integral_map (continuous_eval_const t).aemeasurable hF.aestronglyMeasurable, hst t,
      integral_map measurable_subtype_coe.aemeasurable hF.aestronglyMeasurable]
  have hνp : IsProbabilityMeasure ν := by
    constructor
    have h1 : (P.map fun w => w 0) univ = 1 := by
      rw [Measure.map_apply (continuous_eval_const 0).measurable MeasurableSet.univ]
      simp
    rw [hP.initial, Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at h1
    simpa using h1
  refine ⟨hνp, fun f => ?_⟩
  set g := Diffusion.twoLocusGenerator θA θB ρ πA πB i₀ σ f with hg
  obtain ⟨Bf, hBf⟩ := exists_bound_eval_gameteSimplex f
  obtain ⟨Bg, hBg⟩ := exists_bound_eval_gameteSimplex g
  have hm := hP.martingale f 0 1 zero_le_one 0 Fin.elim0 (fun j => j.elim0)
    (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, mul_one] at hm
  have hcf : ∀ t : ℝ≥0, Continuous fun w : C(ℝ≥0, Fin KA × Fin KB → ℝ) => eval (w t) f :=
    fun t => (MvPolynomial.continuous_eval f).comp (continuous_eval_const t)
  have hif : ∀ t : ℝ≥0, Integrable (fun w : C(ℝ≥0, Fin KA × Fin KB → ℝ) => eval (w t) f) P := by
    intro t
    refine Integrable.mono' (integrable_const Bf) (hcf t).aestronglyMeasurable ?_
    filter_upwards [hP.mem] with w hw
    rw [Real.norm_eq_abs]
    exact hBf _ (hw t)
  have hjoint : Continuous fun p : C(ℝ≥0, Fin KA × Fin KB → ℝ) × ℝ =>
      eval (p.1 p.2.toNNReal) g :=
    (MvPolynomial.continuous_eval g).comp (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd)))
  have hci : Continuous fun w : C(ℝ≥0, Fin KA × Fin KB → ℝ) =>
      ∫ u in (0 : ℝ)..1, eval (w u.toNNReal) g :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (w : C(ℝ≥0, Fin KA × Fin KB → ℝ)) (u : ℝ) => eval (w u.toNNReal) g) hjoint _ _
  have hii : Integrable (fun w : C(ℝ≥0, Fin KA × Fin KB → ℝ) =>
      ∫ u in (0 : ℝ)..1, eval (w u.toNNReal) g) P := by
    refine Integrable.mono' (integrable_const (Bg * |(1 : ℝ) - 0|)) hci.aestronglyMeasurable ?_
    filter_upwards [hP.mem] with w hw
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]; exact hBg _ (hw _)
  simp only [NNReal.coe_zero, NNReal.coe_one] at hm
  rw [← hg] at hm
  have e1 := integral_sub ((hif 1).sub (hif 0)) hii
  have e2 := integral_sub (hif 1) (hif 0)
  simp only [Pi.sub_apply] at e1
  rw [e1, e2,
    hmarg 1 _ (MvPolynomial.continuous_eval f), hmarg 0 _ (MvPolynomial.continuous_eval f),
    sub_self, zero_sub, neg_eq_zero] at hm
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hprod : Integrable (Function.uncurry fun (w : C(ℝ≥0, Fin KA × Fin KB → ℝ)) (u : ℝ) =>
      eval (w u.toNNReal) g) (P.prod μ) := by
    refine Integrable.mono' (integrable_const Bg) hjoint.aestronglyMeasurable ?_
    have hae : ∀ᵐ p ∂(P.prod μ), ∀ t, p.1 t ∈ Diffusion.gameteSimplex KA KB :=
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := μ)).ae hP.mem
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact hBg _ (hp _)
  have hswap := integral_integral_swap hprod
  have hin : ∀ w : C(ℝ≥0, Fin KA × Fin KB → ℝ), ∫ u in (0 : ℝ)..1, eval (w u.toNNReal) g =
      ∫ u, eval (w u.toNNReal) g ∂μ := fun w =>
    intervalIntegral.integral_of_le zero_le_one
  simp_rw [hin] at hm
  rw [hswap] at hm
  simp_rw [hmarg _ _ (MvPolynomial.continuous_eval g)] at hm
  rw [integral_const, hμ] at hm
  simpa using hm

theorem hasDerivAt_samplingMoment_of_processStationary (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    {ν : ℝ → Measure (Diffusion.gameteSimplex KA KB)}
    (hν : ∀ σ, ∃ P, IsProcessStationary θA θB ρ πA πB i₀ σ (ν σ) P) (ξ : Config KA KB) :
    HasDerivAt (fun σ => samplingMoment (ν σ) ξ)
      (selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ) 0 :=
  hasDerivAt_samplingMoment hθA hθB hρ hπA hπB
    (fun σ => (hν σ).elim fun _ hP => hP.isStationaryLaw) ξ

end Easy

section Existence

open Filter Topology Analysis Diffusion MarkovChain

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem convex_gameteSimplex : Convex ℝ (gameteSimplex KA KB) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun g => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 g)) (mul_nonneg hb (hy.1 g))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

theorem gameteSimplex_subset_cube : gameteSimplex KA KB ⊆ cube (Fin KA × Fin KB) := by
  intro x hx g _
  refine ⟨hx.1 g, ?_⟩
  rw [← hx.2]
  exact Finset.single_le_sum (fun g _ => hx.1 g) (Finset.mem_univ g)

/-- Source: ethier_kurtz1986, ch. 4, sec. 9. -/
theorem exists_isProcessStationary (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j) (hπA : ∑ i, πA i = 1)
    (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ) :
    ∃ (ν : Measure (Diffusion.gameteSimplex KA KB)) (P : Measure C(ℝ≥0, Fin KA × Fin KB → ℝ)),
      IsProcessStationary θA θB ρ πA πB i₀ σ ν P := by
  have hKB : Nonempty (Fin KB) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hπB
  have hKA : Nonempty (Fin KA) := ⟨i₀⟩
  have hNr : ∀ n : ℕ, (0 : ℝ) < ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) :=
    fun n => Nat.cast_pos.2 (moranOffset_pos θA θB ρ σ n)
  have hNt : Tendsto (fun n : ℕ => ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat _)
  have hτ : Tendsto (fun n : ℕ => ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hNt
  have hδ : Tendsto (fun n : ℕ => 1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat _)
  have he : Tendsto (fun n : ℕ => (((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    hτ.inv_tendsto_atTop
  obtain ⟨c0, hc0⟩ := exists_moranChain_drift_le hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ
  have hstep : ∀ n (z z' : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB),
      (moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).P z z' ≠ 0 → ∀ g,
        |moranFreq _ z' g - moranFreq _ z g| ≤ 1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) :=
    fun n z z' h g => moranChain_step hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n h g
  have hmom : ∀ n (z : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB) g (p : ℕ),
      (moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect
        (fun w => (moranFreq _ w g - moranFreq _ z g) ^ p) z ≤
        (1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) ^ p :=
    fun n z g p => expect_pow_le_of_step _ (fun w => moranFreq _ w g) z
      (fun w h => hstep n z w h g) p
  have hτ2 : ∀ n : ℕ, (1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) ^ 2 ≤
      max c0 1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 := fun n => by
    rw [div_pow, one_pow]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨Q, hQ1, hQK, hQm, hQs⟩ := exists_stationary_martingale_limit
    (fun n => moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n)
    (fun n ω => moranFreq (n + moranOffset θA θB ρ σ) ω)
    (fun n => ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2)
    isCompact_gameteSimplex.isClosed convex_gameteSimplex gameteSimplex_subset_cube
    (fun n ω => moranFreq_mem_gameteSimplex (moranOffset_pos θA θB ρ σ n) ω) hτ
    (fun n => 1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) hδ
    (Eventually.of_forall fun n z z' h =>
      (dist_pi_le_iff (by positivity)).2 fun g => by
        rw [Real.dist_eq]; exact hstep n z z' h g)
    (max c0 1) (fun n => (((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2)⁻¹)
    (fun g => Eventually.of_forall fun n z => (hc0 n z g).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
    (fun g => Eventually.of_forall fun n z => (hmom n z g 2).trans (hτ2 n))
    (fun g => Eventually.of_forall fun n z => (hmom n z g 4).trans (le_of_eq (by ring)))
    he (fun p x => eval x p) (fun p x => eval x (twoLocusGenerator θA θB ρ πA πB i₀ σ p))
    (fun p => MvPolynomial.continuous_eval p)
    (fun p => MvPolynomial.continuous_eval _)
    (fun p ε hε => by
      obtain ⟨c, hc⟩ := exists_moranChain_generator_le hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ p
      have hl : Tendsto (fun n : ℕ => c / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).div_atTop hNt
      filter_upwards [hl.eventually (ge_mem_nhds hε)] with n hn z
      exact (hc n z).trans hn)
  have hKm : MeasurableSet (gameteSimplex KA KB) :=
    isCompact_gameteSimplex.isClosed.measurableSet
  set ν : Measure (gameteSimplex KA KB) := (Q.map fun w => w 0).comap Subtype.val with hν
  refine ⟨ν, Q, ?_⟩
  have hinit : ν.map Subtype.val = Q.map fun w => w 0 := by
    rw [hν]
    rw [(MeasurableEmbedding.subtype_coe hKm).map_comap, Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    exact (ae_map_iff (continuous_eval_const 0).measurable.aemeasurable hKm).2
      (hQK.mono fun w hw => hw 0)
  exact ⟨⟨hQ1, hinit.symm, hQK, fun f s t hst k r hr h => hQm f s t hst k r hr h⟩,
    fun t => (hQs t).trans hinit.symm⟩

theorem exists_processStationary_hasDerivAt_samplingMoment (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j) (hπA : ∑ i, πA i = 1)
    (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) :
    ∃ (ν : ℝ → Measure (gameteSimplex KA KB)) (P : ℝ → Measure C(ℝ≥0, Fin KA × Fin KB → ℝ)),
      (∀ σ, IsProcessStationary θA θB ρ πA πB i₀ σ (ν σ) (P σ)) ∧
      ∀ ξ : Config KA KB, HasDerivAt (fun σ => samplingMoment (ν σ) ξ)
        (selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ) 0 := by
  choose ν P hP using fun σ =>
    exists_isProcessStationary hθA.le hθB.le hρ hπA0 hπB0 hπA hπB i₀ σ
  exact ⟨ν, P, hP, fun ξ => hasDerivAt_samplingMoment_of_processStationary hθA hθB hρ hπA hπB
    (fun σ => ⟨P σ, hP σ⟩) ξ⟩

end Existence

end Rhone.Coalescent
