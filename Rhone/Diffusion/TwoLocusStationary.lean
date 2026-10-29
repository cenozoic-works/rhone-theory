/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.TwoLocusMaximumPrinciple
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Stationary laws of the two-locus diffusion with selection

Source: ethier_kurtz1986, ch. 4, sec. 9. -/

@[expose] public section

namespace Rhone.Diffusion

open MvPolynomial Finset Set MeasureTheory

variable {KA KB : ℕ}

noncomputable def simplexDiffusionOpLin {G : Type*} [Fintype G] [DecidableEq G]
    (b : G → MvPolynomial G ℝ) : MvPolynomial G ℝ →ₗ[ℝ] MvPolynomial G ℝ where
  toFun := simplexDiffusionOp b
  map_add' f g := by
    simp only [simplexDiffusionOp, map_add, mul_add, sum_add_distrib]
    abel
  map_smul' c f := by
    simp only [simplexDiffusionOp, Derivation.map_smul, RingHom.id_apply, smul_add, smul_sum,
      mul_smul_comm]

instance instCompactSpaceGameteSimplex : CompactSpace (gameteSimplex KA KB) :=
  isCompact_iff_compactSpace.mp isCompact_gameteSimplex

noncomputable def polyOnSimplex (KA KB : ℕ) :
    MvPolynomial (Fin KA × Fin KB) ℝ →ₗ[ℝ] C(gameteSimplex KA KB, ℝ) where
  toFun f := ⟨fun x => eval (x : Fin KA × Fin KB → ℝ) f,
    (MvPolynomial.continuous_eval f).comp continuous_subtype_val⟩
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

def IsStationaryLaw (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (i₀ : Fin KA) (σ : ℝ)
    (ν : Measure (gameteSimplex KA KB)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ f : MvPolynomial (Fin KA × Fin KB) ℝ,
    ∫ x, eval (x : Fin KA × Fin KB → ℝ) (twoLocusGenerator θA θB ρ πA πB i₀ σ f) ∂ν = 0

theorem nonneg_of_neg_on_neg {S : Type*} [TopologicalSpace S] (Λ : StrongDual ℝ C(S, ℝ))
    (hneg : ∀ g : C(S, ℝ), (∀ x, g x < 0) → Λ g < 0) {g : C(S, ℝ)} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ Λ g := by
  have h1 : Λ (-1) < 0 := hneg _ fun x => by simp
  have h1' : 0 < Λ 1 := by
    rw [map_neg] at h1
    linarith
  by_contra hlt
  push Not at hlt
  set ε : ℝ := -Λ g / (2 * Λ 1) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have h2 := hneg (-g - ε • 1) fun x => by
    simp only [ContinuousMap.sub_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    linarith [hg x]
  rw [map_sub, map_neg, map_smul, smul_eq_mul] at h2
  have h3 : ε * Λ 1 = -Λ g / 2 := by
    rw [hε]
    field_simp
  linarith

theorem exists_isStationaryLaw {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ) :
    ∃ ν : Measure (gameteSimplex KA KB), IsStationaryLaw θA θB ρ πA πB i₀ σ ν := by
  set S := gameteSimplex KA KB
  set Gen := (polyOnSimplex KA KB).comp (simplexDiffusionOpLin (twoLocusDrift θA θB ρ πA πB i₀ σ))
    with hGen
  have hGen_apply : ∀ f x, Gen f x =
      eval (x : Fin KA × Fin KB → ℝ) (twoLocusGenerator θA θB ρ πA πB i₀ σ f) := by
    intro f x
    rw [twoLocusGenerator_eq_simplexDiffusionOp]
    rfl
  set M : Set C(S, ℝ) := (LinearMap.range Gen : Set C(S, ℝ)) with hM
  set s : Set C(S, ℝ) := {g | MapsTo (⇑g) univ (Iio 0)} with hs
  have hs_open : IsOpen s := ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ isOpen_Iio
  have hs_mem : ∀ g : C(S, ℝ), g ∈ s ↔ ∀ x, g x < 0 := fun g => by
    simp [hs, MapsTo]
  have hs_conv : Convex ℝ s := by
    intro g hg h hh a b ha hb hab
    rw [hs_mem] at hg hh ⊢
    intro x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    have := hg x
    have := hh x
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      linarith
    · nlinarith [mul_neg_of_pos_of_neg ha' (hg x), mul_nonpos_of_nonneg_of_nonpos hb (hh x).le]
  have hdisj : Disjoint s M := by
    rw [Set.disjoint_left]
    rintro g hgs ⟨f, rfl⟩
    obtain ⟨x, hx, hx0⟩ :=
      exists_nonneg_eval_twoLocusGenerator hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ f
    have := (hs_mem _).1 hgs ⟨x, hx⟩
    rw [hGen_apply] at this
    exact absurd hx0 (not_le.2 this)
  obtain ⟨Λ, u, hΛs, hΛM⟩ :=
    geometric_hahn_banach_open hs_conv hs_open (LinearMap.range Gen).convex hdisj
  have hu0 : u ≤ 0 := by simpa using hΛM 0 (LinearMap.range Gen).zero_mem
  have hΛM0 : ∀ f, Λ (Gen f) = 0 := by
    intro f
    by_contra hne
    have := hΛM (((u - 1) / Λ (Gen f)) • Gen f) ⟨((u - 1) / Λ (Gen f)) • f, by rw [map_smul]⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  have hneg : ∀ g : C(S, ℝ), (∀ x, g x < 0) → Λ g < 0 := fun g hg =>
    (hΛs g ((hs_mem g).2 hg)).trans_le hu0
  have hpos : ∀ g : C(S, ℝ), (∀ x, 0 ≤ g x) → 0 ≤ Λ g := fun g hg =>
    nonneg_of_neg_on_neg Λ hneg hg
  have hΛ1 : 0 < Λ 1 := by
    have h := hneg (-1) fun x => by simp
    rw [map_neg] at h
    linarith
  set c : ℝ := (Λ 1)⁻¹ with hc
  let L : CompactlySupportedContinuousMap S ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun h => c * Λ h.toContinuousMap
      map_add' := fun h₁ h₂ => by
        have : (h₁ + h₂).toContinuousMap = h₁.toContinuousMap + h₂.toContinuousMap := by
          ext x
          simp
        rw [this, map_add, mul_add]
      map_smul' := fun a h => by
        have : (a • h).toContinuousMap = a • h.toContinuousMap := by
          ext x
          simp
        rw [this, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
        ring }
  let Lp := PositiveLinearMap.mk₀ L fun h hh => mul_nonneg (inv_nonneg.2 hΛ1.le)
    (hpos _ fun x => by simpa using (CompactlySupportedContinuousMap.le_def.1 hh x))
  set μ := RealRMK.rieszMeasure Lp with hμ
  have hint : ∀ g : C(S, ℝ), ∫ x, g x ∂μ = c * Λ g := by
    intro g
    have := RealRMK.integral_rieszMeasure Lp
      (CompactlySupportedContinuousMap.continuousMapEquiv g)
    exact this
  have hprob : IsProbabilityMeasure μ := by
    have h1 := hint 1
    simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h1
    rw [hc, inv_mul_cancel₀ hΛ1.ne'] at h1
    refine ⟨?_⟩
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h1
    exact h1
  refine ⟨μ, hprob, fun f => ?_⟩
  have := hint (Gen f)
  rw [hΛM0 f, mul_zero] at this
  rw [← this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hGen_apply f x).symm)

end Rhone.Diffusion
