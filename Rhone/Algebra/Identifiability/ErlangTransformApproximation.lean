/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.FinitePanelGeometry.StablePolytope
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Exact finite interpolation by rational powers, the Erlang-transform algebraic step -/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Rhone.Algebra.Identifiability.ErlangApproximation

abbrev PositiveTime := {t : ℝ // 0 < t}

def atomFeature {d : ℕ} (s : Fin d → ℝ) (t : PositiveTime) : Fin d → ℝ :=
  fun i => Real.exp (-s i * t)

def powerFeature {d : ℕ} (s : Fin d → ℝ) (n : ℕ) (t : PositiveTime) : Fin d → ℝ :=
  fun i => (1 + s i * t / (n+2 : ℕ))⁻¹ ^ (n+2)

lemma powerFeature_tendsto {d : ℕ} (s : Fin d → ℝ) (t : PositiveTime) :
    Tendsto (fun n => powerFeature s n t) atTop (𝓝 (atomFeature s t)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := (Real.tendsto_one_add_div_pow_exp (s i * t)).inv₀ (Real.exp_ne_zero _)
  have hn : Tendsto (fun n : ℕ => n+2) atTop atTop := tendsto_add_atTop_nat 2
  have hh := h.comp hn
  simpa only [powerFeature, atomFeature, Function.comp_def, inv_pow, Real.exp_neg,
    neg_mul] using hh

lemma powerFeature_as_rate {d : ℕ} (s : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i)
    (n : ℕ) (t : PositiveTime) (i : Fin d) :
    powerFeature s n t i =
      (((n+2 : ℕ) : ℝ) / t / (((n+2 : ℕ) : ℝ) / t + s i)) ^ (n+2) := by
  have hn : (0 : ℝ) < (n+2 : ℕ) := by positivity
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have hr : (0 : ℝ) < (n+2 : ℕ) / t := div_pos hn t.property
  have hd : ((n+2 : ℕ) : ℝ) / t + s i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hr (hs i))
  unfold powerFeature
  congr 1
  field_simp

theorem eventually_positive_power_match {d : ℕ} (s : Fin d → ℝ) {m : Fin d → ℝ}
    (hm : m ∈ interior (convexHull ℝ (range (atomFeature s)))) :
    ∀ᶠ n in atTop, ∃ (t : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ),
      (↑t : Set (Fin d → ℝ)) ⊆ range (powerFeature s n) ∧
      t.Nonempty ∧ t.card ≤ d+1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = m := by
  have h := FinitePanelGeometry.curve_eventually_exists_positive_exact_match
    (atomFeature s) (powerFeature s) hm (powerFeature_tendsto s)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

theorem eventually_positive_rate_power_match {d : ℕ} (s : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i) {m : Fin d → ℝ}
    (hm : m ∈ interior (convexHull ℝ (range (atomFeature s)))) :
    ∀ᶠ n in atTop, ∃ (t : Finset (Fin d → ℝ)) (w r : (Fin d → ℝ) → ℝ),
      t.Nonempty ∧ t.card ≤ d+1 ∧ (∀ y ∈ t, 0 < w y) ∧ (∀ y ∈ t, 0 < r y) ∧
      ∑ y ∈ t, w y = 1 ∧
      ∀ i, ∑ y ∈ t, w y * (r y / (r y + s i)) ^ (n+2) = m i := by
  classical
  filter_upwards [eventually_positive_power_match s hm] with n hn
  obtain ⟨t,w,htr,hne,hcard,hpos,hws,heq⟩ := hn
  have hrep : ∀ y : t, ∃ x : PositiveTime, powerFeature s n x = (y : Fin d → ℝ) :=
    fun y => htr y.property
  choose x hx using hrep
  let r : (Fin d → ℝ) → ℝ := fun y =>
    if hy : y ∈ t then (n+2 : ℕ) / (x ⟨y,hy⟩ : ℝ) else 1
  refine ⟨t,w,r,hne,hcard,hpos,?_,hws,?_⟩
  · intro y hy
    simp only [r, dite_eq_left hy]
    exact div_pos (by positivity) (x ⟨y,hy⟩).property
  · intro i
    have hcomponent := congrArg (fun z : Fin d → ℝ => z i) heq
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcomponent
    rw [← hcomponent]
    apply Finset.sum_congr rfl
    intro y hy
    congr 1
    simp only [r, dite_eq_left hy]
    rw [← powerFeature_as_rate s hs n (x ⟨y,hy⟩) i, hx]

end Rhone.Algebra.Identifiability.ErlangApproximation
