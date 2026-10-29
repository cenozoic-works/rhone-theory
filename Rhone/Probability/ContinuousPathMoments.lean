/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Laws on continuous paths in `[0, 1]` are determined by their joint moments -/

@[expose] public section

namespace Rhone.Probability

open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped NNReal

noncomputable def clampUnit (y : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one y : ℝ)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_subtype_val.comp continuous_projIcc

theorem clampUnit_of_mem {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : clampUnit y = y := by
  simp [clampUnit, Set.projIcc_of_mem _ hy]

theorem clampUnit_mem (y : ℝ) : clampUnit y ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one y).2

noncomputable def pathMoment (P : Measure C(ℝ≥0, ℝ)) (I : Finset ℝ≥0) (e : ℝ≥0 → ℕ) : ℝ :=
  ∫ w, ∏ t ∈ I, clampUnit (w t) ^ e t ∂P

theorem measurable_coeFn : Measurable (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) :=
  Measurable.of_eval fun t => ContinuousMap.measurable_eval t

theorem measurableSpace_eq_comap_coeFn :
    (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t) MeasurableSpace.pi := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  change borel C(ℝ≥0, ℝ) = _
  rw [ContinuousMap.borel_eq_iSup_comap_eval]
  rfl

theorem ext_of_map_coeFn {P Q : Measure C(ℝ≥0, ℝ)}
    (h : P.map (fun w (t : ℝ≥0) => w t) = Q.map (fun w (t : ℝ≥0) => w t)) : P = Q := by
  ext A hA
  have hA' : MeasurableSet[MeasurableSpace.comap (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t)
      MeasurableSpace.pi] A := by
    rw [← measurableSpace_eq_comap_coeFn]; exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply measurable_coeFn hB, h, Measure.map_apply measurable_coeFn hB]

theorem ext_of_map_restrict {P Q : Measure C(ℝ≥0, ℝ)} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ I : Finset ℝ≥0, P.map (fun w => I.restrict (fun t => w t)) =
      Q.map (fun w => I.restrict (fun t => w t))) : P = Q := by
  apply ext_of_map_coeFn
  have hP := isProjectiveLimit_map (X := fun (t : ℝ≥0) (w : C(ℝ≥0, ℝ)) => w t) (P := P)
    measurable_coeFn.aemeasurable
  have hQ := isProjectiveLimit_map (X := fun (t : ℝ≥0) (w : C(ℝ≥0, ℝ)) => w t) (P := Q)
    measurable_coeFn.aemeasurable
  have hfam : (fun I : Finset ℝ≥0 => P.map (fun w => I.restrict (fun t => w t))) =
      fun I => Q.map (fun w => I.restrict (fun t => w t)) := funext h
  rw [hfam] at hP
  exact hP.unique hQ

section Cube

variable (I : Finset ℝ≥0)

noncomputable def cubeCoord (i : I) : (I → Set.Icc (0 : ℝ) 1) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (z i : ℝ), continuous_subtype_val.comp (continuous_apply i)⟩

noncomputable def cubePolynomials : StarSubalgebra ℝ ((I → Set.Icc (0 : ℝ) 1) →ᵇ ℝ) :=
  { Algebra.adjoin ℝ (Set.range (cubeCoord I)) with
    star_mem' := fun {a} ha => by
      have : star a = a := by ext z; simp
      rw [this]; exact ha }

theorem cubePolynomials_separatesPoints :
    ((cubePolynomials I).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra hcon
    push Not at hcon
    exact hxy (funext hcon)
  refine ⟨_, ⟨toContinuousMapStarₐ ℝ (cubeCoord I i),
    ⟨cubeCoord I i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hi
  exact Subtype.ext (by simpa [cubeCoord] using heq)

theorem exists_monomial_of_mem_closure {g : (I → Set.Icc (0 : ℝ) 1) →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (Set.range (cubeCoord I))) :
    ∃ e : I → ℕ, ∀ z, g z = ∏ i, (z i : ℝ) ^ e i := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    refine ⟨Pi.single i 1, fun z => ?_⟩
    rw [Finset.prod_eq_single i]
    · simp [cubeCoord]
    · intro j _ hj; simp [hj]
    · simp
  | one => exact ⟨0, fun z => by simp⟩
  | mul g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, fun z => ?_⟩
    simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, he₁, he₂, Pi.add_apply,
      pow_add, Finset.prod_mul_distrib]

theorem cube_ext_of_monomial {μ ν : Measure (I → Set.Icc (0 : ℝ) 1)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ e : I → ℕ, ∫ z, ∏ i, (z i : ℝ) ^ e i ∂μ = ∫ z, ∏ i, (z i : ℝ) ^ e i ∂ν) :
    μ = ν := by
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (𝕜 := ℝ) (cubePolynomials_separatesPoints I) ?_
  have key : ∀ g ∈ Submodule.span ℝ (Submonoid.closure (Set.range (cubeCoord I)) :
      Set ((I → Set.Icc (0 : ℝ) 1) →ᵇ ℝ)), ∫ z, g z ∂μ = ∫ z, g z ∂ν := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, he⟩ := exists_monomial_of_mem_closure I hg
      simp_rw [he]
      exact h e
    | zero => simp
    | add g₁ g₂ _ _ h₁ h₂ =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (g₁.integrable μ) (g₂.integrable μ),
        integral_add (g₁.integrable ν) (g₂.integrable ν), h₁, h₂]
    | smul c g _ hg =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hg]
  intro g hg
  have hg' : g ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (Set.range (cubeCoord I))) := hg
  rw [Algebra.adjoin_eq_span] at hg'
  exact key g hg'

end Cube

theorem eq_of_pathMoment_eq {P Q : Measure C(ℝ≥0, ℝ)} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hP : ∀ᵐ w ∂P, ∀ t, w t ∈ Set.Icc (0 : ℝ) 1) (hQ : ∀ᵐ w ∂Q, ∀ t, w t ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ (I : Finset ℝ≥0) (e : ℝ≥0 → ℕ), pathMoment P I e = pathMoment Q I e) : P = Q := by
  apply ext_of_map_restrict
  intro I
  set R : C(ℝ≥0, ℝ) → (I → ℝ) := fun w => I.restrict (fun t => w t) with hR
  let c : (I → ℝ) → (I → Set.Icc (0 : ℝ) 1) := fun y i => Set.projIcc (0 : ℝ) 1 zero_le_one (y i)
  let v : (I → Set.Icc (0 : ℝ) 1) → (I → ℝ) := fun z i => (z i : ℝ)
  have hRm : Measurable R := (Finset.measurable_restrict _).comp measurable_coeFn
  have hcm : Measurable c :=
    Measurable.of_eval fun i => (continuous_projIcc.measurable).comp (measurable_pi_apply i)
  have hvm : Measurable v :=
    Measurable.of_eval fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  have hvc : ∀ (M : Measure C(ℝ≥0, ℝ)), (∀ᵐ w ∂M, ∀ t, w t ∈ Set.Icc (0 : ℝ) 1) →
      M.map R = (M.map (c ∘ R)).map v := by
    intro M hM
    rw [Measure.map_map hvm (hcm.comp hRm)]
    refine Measure.map_congr ?_
    filter_upwards [hM] with w hw
    funext i
    change w i = ((Set.projIcc (0 : ℝ) 1 zero_le_one (w i)) : ℝ)
    rw [Set.projIcc_of_mem _ (hw i)]
  rw [hvc P hP, hvc Q hQ]
  congr 1
  apply cube_ext_of_monomial
  intro e
  have hmc : Continuous fun z : (I → Set.Icc (0 : ℝ) 1) => ∏ i, (z i : ℝ) ^ e i :=
    continuous_finsetProd _ fun i _ => (continuous_subtype_val.comp (continuous_apply i)).pow _
  rw [integral_map (hcm.comp hRm).aemeasurable hmc.aestronglyMeasurable,
    integral_map (hcm.comp hRm).aemeasurable hmc.aestronglyMeasurable]
  let e' : ℝ≥0 → ℕ := fun t => if ht : t ∈ I then e ⟨t, ht⟩ else 0
  have hmon : ∀ w : C(ℝ≥0, ℝ), (∏ i, ((c ∘ R) w i : ℝ) ^ e i) =
      ∏ t ∈ I, clampUnit (w t) ^ e' t := by
    intro w
    rw [← Finset.prod_coe_sort I]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [e', c, R, clampUnit, i.2]
  simp_rw [hmon]
  exact h I e'

end Rhone.Probability
