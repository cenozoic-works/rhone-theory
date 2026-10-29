/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Compact sets of continuous paths with values in `[0, 1]` -/

@[expose] public section

namespace Rhone.Analysis

open Set Filter Topology Metric
open scoped NNReal

def ModulusAt (j : ℕ) (d : ℝ) (f : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, (s : ℝ) ≤ j + 1 → (t : ℝ) ≤ j + 1 → dist s t ≤ d → dist (f s) (f t) ≤ 1 / (j + 1)

theorem ModulusAt.mono {j : ℕ} {d d' : ℝ} {f : ℝ≥0 → ℝ} (h : ModulusAt j d f) (hd : d' ≤ d) :
    ModulusAt j d' f :=
  fun s t hs ht hst => h s t hs ht (hst.trans hd)

def UnitModulus (δ : ℕ → ℝ) (f : ℝ≥0 → ℝ) : Prop :=
  (∀ t, f t ∈ Icc (0 : ℝ) 1) ∧ ∀ j : ℕ, ModulusAt j (δ j) f

theorem exists_nhds_unitModulus {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) (x₀ : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ U ∈ 𝓝 x₀, ∀ f, UnitModulus δ f → ∀ x ∈ U, dist (f x₀) (f x) < ε := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (x₀ : ℝ) + 1 / ε ≤ j := exists_nat_ge _
  refine ⟨ball x₀ (min (δ j) 1), ball_mem_nhds _ (lt_min (hδ j) one_pos), fun f hf x hx => ?_⟩
  rw [mem_ball] at hx
  have hx1 : dist x x₀ < 1 := hx.trans_le (min_le_right _ _)
  have hxδ : dist x₀ x ≤ δ j := by
    rw [dist_comm]
    exact hx.le.trans (min_le_left _ _)
  have h1ε : 0 ≤ 1 / ε := by positivity
  have hx0 : (0 : ℝ) ≤ x₀ := NNReal.coe_nonneg x₀
  have hx0j : (x₀ : ℝ) ≤ j + 1 := by linarith
  have hxj : (x : ℝ) ≤ j + 1 := by
    have h : |(x : ℝ) - x₀| < 1 := by rwa [NNReal.dist_eq] at hx1
    linarith [(abs_lt.1 h).2]
  refine (hf.2 j x₀ x hx0j hxj hxδ).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  have hεj : 1 ≤ ε * j := by
    have h := mul_le_mul_of_nonneg_left (show 1 / ε ≤ j by linarith) hε.le
    rwa [mul_one_div_cancel hε.ne'] at h
  have e : ε * ((j : ℝ) + 1) = ε * j + ε := by ring
  linarith

theorem UnitModulus.continuous {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) {f : ℝ≥0 → ℝ}
    (hf : UnitModulus δ f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨U, hU, h⟩ := exists_nhds_unitModulus hδ x₀ hε
  filter_upwards [hU] with x hx
  rw [dist_comm]
  exact h f hf x hx

def unitModulusSet (δ : ℕ → ℝ) : Set C(ℝ≥0, ℝ) := {w | UnitModulus δ w}

theorem isClosed_setOf_unitModulus (δ : ℕ → ℝ) :
    IsClosed {f : ℝ≥0 → ℝ | UnitModulus δ f} := by
  simp only [UnitModulus, ModulusAt, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun t => isClosed_Icc.preimage (continuous_apply t)) ?_
  exact isClosed_iInter fun j => isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le ((continuous_apply s).dist (continuous_apply t)) continuous_const

theorem isCompact_unitModulusSet {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j) :
    IsCompact (unitModulusSet δ) := by
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · have himg : ContinuousMap.toFun '' unitModulusSet δ = {f : ℝ≥0 → ℝ | UnitModulus δ f} := by
      ext f
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hf
        exact ⟨⟨f, hf.continuous hδ⟩, hf, rfl⟩
    rw [himg]
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      (isClosed_setOf_unitModulus δ) ?_
    intro f hf t _
    exact hf.1 t
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨U, hU, h⟩ := exists_nhds_unitModulus hδ x₀ hε
    filter_upwards [hU] with x hx
    intro i
    exact h _ i.2 x hx

end Rhone.Analysis
