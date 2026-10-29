/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.WeakSelectionResponse
public import Rhone.Probability.ContinuousPathMoments
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Uniqueness of the neutral stationary law of the two-locus diffusion -/

@[expose] public section

namespace Rhone

open MeasureTheory MvPolynomial Set LinearAlgebra.Recursion
open scoped NNReal BoundedContinuousFunction

variable {KA KB : ℕ}

def Coalescent.configC (α : Fin KA → Fin KB → ℕ) : Config KA KB := ⟨fun _ => 0, fun _ => 0, α⟩

theorem Coalescent.sampleMonomial_configC (α : Fin KA → Fin KB → ℕ) :
    Diffusion.sampleMonomial (Coalescent.configC α) =
      ∏ i, ∏ j, (X (i, j) : MvPolynomial (Fin KA × Fin KB) ℝ) ^ α i j := by
  simp [Diffusion.sampleMonomial, Diffusion.partA, Diffusion.partB, Diffusion.partC,
      Coalescent.configC]

theorem Coalescent.exists_eq_sum_sampleMonomial (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ (D : Finset (Config KA KB)) (c : Config KA KB → ℝ),
      f = ∑ η ∈ D, C (c η) * Diffusion.sampleMonomial η := by
  classical
  have he : Function.Injective (fun m : (Fin KA × Fin KB) →₀ ℕ =>
      Coalescent.configC (KA := KA) (KB := KB) fun i j => m (i, j)) := by
    intro m m' h
    ext ⟨i, j⟩
    exact congrFun (congrFun (congrArg Config.c h) i) j
  refine ⟨f.support.image (fun m : (Fin KA × Fin KB) →₀ ℕ =>
      Coalescent.configC (KA := KA) (KB := KB) fun i j => m (i, j)),
    fun η => f.coeff (Finsupp.equivFunOnFinite.symm fun g => η.c g.1 g.2), ?_⟩
  rw [Finset.sum_image (Set.injOn_of_injective he)]
  conv_lhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (Finsupp.equivFunOnFinite.symm fun g : Fin KA × Fin KB =>
      (Coalescent.configC (KA := KA) (KB := KB) fun i j => m (i, j)).c g.1 g.2) = m := by
    ext g
    simp [Coalescent.configC]
  simp only [Coalescent.sampleMonomial_configC]
  rw [hm, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]

theorem Coalescent.downSet_subset_of_mem {ξ η : Config KA KB} (h : η ∈ Coalescent.downSet ξ) :
    Coalescent.downSet η ⊆ Coalescent.downSet ξ := by
  intro ζ hζ
  simp only [Coalescent.downSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h hζ ⊢
  omega

theorem Coalescent.sum_mul_pderiv_margA_eq_selDrift (i₀ : Fin KA)
    (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∑ g, ∑ h, X g * (C (if g = h then 1 else 0) - X h) * pderiv g (Diffusion.margA i₀) * pderiv h
        f =
      Diffusion.selDrift i₀ f := by
  classical
  have hsum : (∑ g : Fin KA × Fin KB,
      X g * (if g.1 = i₀ then (1 : MvPolynomial (Fin KA × Fin KB) ℝ) else 0)) = Diffusion.margA
          i₀ := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [Diffusion.margA]
  rw [Diffusion.selDrift_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp_rw [Diffusion.pderiv_margA]
  rw [← Finset.sum_mul]
  congr 1
  calc ∑ g : Fin KA × Fin KB, X g * (C (if g = h then 1 else 0) - X h) *
        (if g.1 = i₀ then (1 : MvPolynomial (Fin KA × Fin KB) ℝ) else 0)
      = (∑ g : Fin KA × Fin KB, if g = h then
            X g * (if g.1 = i₀ then (1 : MvPolynomial (Fin KA × Fin KB) ℝ) else 0) else 0) -
          X h * ∑ g : Fin KA × Fin KB,
            X g * (if g.1 = i₀ then (1 : MvPolynomial (Fin KA × Fin KB) ℝ) else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero, sub_zero,
          zero_sub] <;> ring
    _ = X h * (C (if h.1 = i₀ then 1 else 0) - Diffusion.margA i₀) := by
        rw [hsum, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ↓reduceIte]
        split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero] <;> ring

set_option linter.unusedFintypeInType false in
theorem Coalescent.ext_of_map_restrict_vec {G : Type*} [Fintype G] {P Q : Measure C(ℝ≥0, G → ℝ)}
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ I : Finset ℝ≥0, P.map (fun w => I.restrict (fun t => w t)) =
      Q.map (fun w => I.restrict (fun t => w t))) : P = Q := by
  have hmeas : Measurable (fun (w : C(ℝ≥0, G → ℝ)) (t : ℝ≥0) => w t) :=
    Measurable.of_eval fun t => ContinuousMap.measurable_eval t
  have hσ : (inferInstance : MeasurableSpace C(ℝ≥0, G → ℝ)) =
      MeasurableSpace.comap (fun (w : C(ℝ≥0, G → ℝ)) (t : ℝ≥0) => w t) MeasurableSpace.pi := by
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    simp_rw [MeasurableSpace.comap_comp]
    exact ContinuousMap.measurableSpace_eq_iSup_comap_eval
  have hcoe : P.map (fun w (t : ℝ≥0) => w t) = Q.map (fun w (t : ℝ≥0) => w t) := by
    have hP := ProbabilityTheory.isProjectiveLimit_map
      (X := fun (t : ℝ≥0) (w : C(ℝ≥0, G → ℝ)) => w t) (P := P) hmeas.aemeasurable
    have hQ := ProbabilityTheory.isProjectiveLimit_map
      (X := fun (t : ℝ≥0) (w : C(ℝ≥0, G → ℝ)) => w t) (P := Q) hmeas.aemeasurable
    have hfam : (fun I : Finset ℝ≥0 => P.map (fun w => I.restrict (fun t => w t))) =
        fun I => Q.map (fun w => I.restrict (fun t => w t)) := funext h
    rw [hfam] at hP
    exact hP.unique hQ
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap (fun (w : C(ℝ≥0, G → ℝ)) (t : ℝ≥0) => w t)
      MeasurableSpace.pi] A := by
    rw [← hσ]; exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply hmeas hB, hcoe, Measure.map_apply hmeas hB]

noncomputable def Coalescent.simplexCoord (g : Fin KA × Fin KB) : Diffusion.gameteSimplex KA KB →ᵇ
    ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (x : Fin KA × Fin KB → ℝ) g, (continuous_apply g).comp continuous_subtype_val⟩

noncomputable def Coalescent.simplexPolynomials : StarSubalgebra ℝ
    (Diffusion.gameteSimplex KA KB →ᵇ ℝ) :=
  { Algebra.adjoin ℝ (Set.range (Coalescent.simplexCoord (KA := KA) (KB := KB))) with
    star_mem' := fun {a} ha => by
      have : star a = a := by ext z; simp
      rw [this]; exact ha }

theorem Coalescent.simplexPolynomials_separatesPoints :
    ((Coalescent.simplexPolynomials (KA := KA) (KB := KB)).map
      (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have hne : (x : Fin KA × Fin KB → ℝ) ≠ y := fun h => hxy (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  refine ⟨_, ⟨BoundedContinuousFunction.toContinuousMapStarₐ ℝ (Coalescent.simplexCoord g),
    ⟨Coalescent.simplexCoord g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  intro heq
  exact hg (by simpa [Coalescent.simplexCoord] using heq)

theorem Coalescent.exists_monomial_of_mem_closure_simplex {f : Diffusion.gameteSimplex KA KB →ᵇ ℝ}
    (hf : f ∈ Submonoid.closure (Set.range (Coalescent.simplexCoord (KA := KA) (KB := KB)))) :
    ∃ e : Fin KA × Fin KB → ℕ, ∀ z : Diffusion.gameteSimplex KA KB,
      f z = ∏ g, (z : Fin KA × Fin KB → ℝ) g ^ e g := by
  classical
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    refine ⟨Pi.single g 1, fun z => ?_⟩
    rw [Finset.prod_eq_single g]
    · simp [Coalescent.simplexCoord]
    · intro h _ hh; simp [hh]
    · simp
  | one => exact ⟨0, fun z => by simp⟩
  | mul f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, fun z => ?_⟩
    simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, he₁, he₂, Pi.add_apply,
      pow_add, Finset.prod_mul_distrib]

theorem Coalescent.ext_of_samplingMoment_eq {ν ν' : Measure (Diffusion.gameteSimplex KA KB)}
    [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] (h : Coalescent.samplingMoment ν = Coalescent.samplingMoment ν') : ν =
        ν' := by
  have hmono : ∀ e : Fin KA × Fin KB → ℕ,
      ∫ z, ∏ g, (z : Fin KA × Fin KB → ℝ) g ^ e g ∂ν =
        ∫ z, ∏ g, (z : Fin KA × Fin KB → ℝ) g ^ e g ∂ν' := by
    intro e
    have h1 := congrFun h (Coalescent.configC fun i j => e (i, j))
    simp only [Coalescent.samplingMoment, Coalescent.sampleMonomial_configC, map_prod, map_pow,
        eval_X] at h1
    simpa [Fintype.prod_prod_type] using h1
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (𝕜 := ℝ) Coalescent.simplexPolynomials_separatesPoints ?_
  have key : ∀ f ∈ Submodule.span ℝ (Submonoid.closure
      (Set.range (Coalescent.simplexCoord (KA := KA) (KB := KB))) : Set
          (Diffusion.gameteSimplex KA KB →ᵇ ℝ)),
      ∫ z, f z ∂ν = ∫ z, f z ∂ν' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, he⟩ := Coalescent.exists_monomial_of_mem_closure_simplex hf
      simp_rw [he]
      exact hmono e
    | zero => simp
    | add f₁ f₂ _ _ h₁ h₂ =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (f₁.integrable ν) (f₂.integrable ν),
        integral_add (f₁.integrable ν') (f₂.integrable ν'), h₁, h₂]
    | smul c f _ hf =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hf]
  intro f hf
  have hf' : f ∈ Subalgebra.toSubmodule
      (Algebra.adjoin ℝ (Set.range (Coalescent.simplexCoord (KA := KA) (KB := KB)))) := hf
  rw [Algebra.adjoin_eq_span] at hf'
  exact key f hf'

theorem Diffusion.IsStationaryLaw.eq_of_zero {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    {i₀ : Fin KA} {ν ν' : Measure (Diffusion.gameteSimplex KA KB)} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hν : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ 0 ν)
        (hν' : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ 0 ν') :
    ν = ν' := by
  have := hν.1
  have := hν'.1
  exact Coalescent.ext_of_samplingMoment_eq ((hν.samplingMoment_eq_q hθA hθB hρ hπA hπB).trans
    (hν'.samplingMoment_eq_q hθA hθB hρ hπA hπB).symm)

theorem Coalescent.eq_of_doeblin {S : Type*} [TopologicalSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    [CompactSpace S] [MeasurableSpace S]
    [BorelSpace S] (A : C(S, ℝ) →L[ℝ] C(S, ℝ)) (_hpos : ∀ g, 0 ≤ g → 0 ≤ A g) (hone : A 1 = 1)
    {κ : ℝ} (hκ : 0 < κ) {μ₀ : Measure S} [IsProbabilityMeasure μ₀]
    (hmin : ∀ g : C(S, ℝ), 0 ≤ g → ∀ x, κ * ∫ y, g y ∂μ₀ ≤ A g x)
    {ν ν' : Measure S} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ∀ g, ∫ x, A g x ∂ν = ∫ x, g x ∂ν) (hν' : ∀ g, ∫ x, A g x ∂ν' = ∫ x, g x ∂ν') :
    ν = ν' := by
  have hint : ∀ (m : Measure S) [IsFiniteMeasure m] (g : C(S, ℝ)),
      Integrable (fun x => g x) m := fun m _ g =>
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hκ1 : κ ≤ 1 := by
    have h := hmin 1 (ContinuousMap.le_def.2 fun _ => by simp) x₀
    simpa [hone] using h
  have hbd : ∀ (m : Measure S) [IsProbabilityMeasure m] (g : C(S, ℝ)) (M : ℝ),
      (∀ x, |g x| ≤ M) → |∫ x, g x ∂m| ≤ M := by
    intro m _ g M hM
    have h1 : ∫ x, g x ∂m ≤ ∫ _x, M ∂m :=
      integral_mono (hint m g) (integrable_const M) fun x => (abs_le.1 (hM x)).2
    have h2 : ∫ _x, -M ∂m ≤ ∫ x, g x ∂m :=
      integral_mono (integrable_const (-M)) (hint m g) fun x => (abs_le.1 (hM x)).1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1 h2
    exact abs_le.2 ⟨h2, h1⟩
  have hstep : ∀ (g : C(S, ℝ)) (M : ℝ), (∀ x, |g x| ≤ M) →
      (∫ x, g x ∂ν - ∫ x, g x ∂ν' =
        ∫ x, (A g - (κ * ∫ y, g y ∂μ₀) • (1 : C(S, ℝ))) x ∂ν -
          ∫ x, (A g - (κ * ∫ y, g y ∂μ₀) • (1 : C(S, ℝ))) x ∂ν') ∧
      ∀ x, |(A g - (κ * ∫ y, g y ∂μ₀) • (1 : C(S, ℝ))) x| ≤ (1 - κ) * M := by
    intro g M hM
    refine ⟨?_, fun x => ?_⟩
    · simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
      rw [integral_sub (hint ν (A g)) (integrable_const _),
        integral_sub (hint ν' (A g)) (integrable_const _), hν, hν']
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    · have hup := hmin (M • 1 - g) (ContinuousMap.le_def.2 fun y => by
        simp only [ContinuousMap.zero_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one, sub_nonneg]
        exact (abs_le.1 (hM y)).2) x
      have hlo := hmin (M • 1 + g) (ContinuousMap.le_def.2 fun y => by
        simp only [ContinuousMap.zero_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
          ContinuousMap.one_apply, smul_eq_mul, mul_one]
        linarith [(abs_le.1 (hM y)).1]) x
      simp only [map_sub, map_add, map_smul, hone, ContinuousMap.sub_apply,
        ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
        mul_one] at hup hlo
      rw [integral_sub (integrable_const M) (hint μ₀ g)] at hup
      rw [integral_add (integrable_const M) (hint μ₀ g)] at hlo
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hup hlo
      simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one]
      rw [abs_le]
      constructor <;> linarith
  have key : ∀ (n : ℕ) (g : C(S, ℝ)) (M : ℝ), (∀ x, |g x| ≤ M) →
      |∫ x, g x ∂ν - ∫ x, g x ∂ν'| ≤ 2 * M * (1 - κ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro g M hM
      have h1 := hbd ν g M hM
      have h2 := hbd ν' g M hM
      rw [pow_zero, mul_one]
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    | succ n ih =>
      intro g M hM
      obtain ⟨heq, hb⟩ := hstep g M hM
      rw [heq]
      calc _ ≤ 2 * ((1 - κ) * M) * (1 - κ) ^ n := ih _ _ hb
        _ = 2 * M * (1 - κ) ^ (n + 1) := by ring
  have hzero : ∀ g : C(S, ℝ), ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
    intro g
    have hM : ∀ x, |g x| ≤ ‖g‖ := fun x => by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x
    have hlim : Filter.Tendsto (fun n : ℕ => 2 * ‖g‖ * (1 - κ) ^ n) Filter.atTop
        (nhds (2 * ‖g‖ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).const_mul _
    have h := ge_of_tendsto' hlim fun n => key n g ‖g‖ hM
    rw [mul_zero] at h
    have := abs_nonpos_iff.1 h
    linarith
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => hzero f.toContinuousMap

end Rhone
