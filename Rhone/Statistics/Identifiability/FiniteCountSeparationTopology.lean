/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-! # Uniform finite boxes from exclusion of pointwise closure -/

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace FiniteCountSeparation

def UniformBoxSeparation (target : ℕ × ℕ → ℝ)
    (competitors : Set (ℕ × ℕ → ℝ)) : Prop :=
  ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ competitors,
    ∃ i ≤ K, ∃ j ≤ K, ε ≤ |p (i, j) - target (i, j)|

theorem exists_pointwise_approximation_of_no_uniform_box
    (target : ℕ × ℕ → ℝ) (competitors : Set (ℕ × ℕ → ℝ))
    (h : ¬ UniformBoxSeparation target competitors) :
    ∃ p : ℕ → ℕ × ℕ → ℝ, (∀ n, p n ∈ competitors) ∧
      ∀ k, Tendsto (fun n => p n k) atTop (𝓝 (target k)) := by
  classical
  have happrox (n : ℕ) : ∃ p ∈ competitors,
      ∀ i ≤ n, ∀ j ≤ n, |p (i, j) - target (i, j)| < 1 / ((n : ℝ) + 1) := by
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hn
    apply h
    refine ⟨n, 1 / ((n : ℝ) + 1), hpos, ?_⟩
    intro p hp
    by_contra hsep
    apply hn
    refine ⟨p, hp, ?_⟩
    intro i hi j hj
    by_contra hbad
    exact hsep ⟨i, hi, j, hj, le_of_not_gt hbad⟩
  choose p hp hclose using happrox
  refine ⟨p, hp, fun k => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hε)
  filter_upwards [eventually_ge_atTop (max k.1 k.2), hsmall] with n hn hsmall
  rw [Real.dist_eq]
  exact (hclose n k.1 ((le_max_left _ _).trans hn)
    k.2 ((le_max_right _ _).trans hn)).trans hsmall

theorem uniform_box_of_not_mem_closure
    (target : ℕ × ℕ → ℝ) (competitors : Set (ℕ × ℕ → ℝ))
    (h : target ∉ closure competitors) : UniformBoxSeparation target competitors := by
  by_contra hsep
  obtain ⟨p, hp, hlim⟩ :=
    exists_pointwise_approximation_of_no_uniform_box target competitors hsep
  exact h (mem_closure_of_tendsto (tendsto_pi_nhds.mpr hlim)
    (Filter.Eventually.of_forall hp))

theorem uniform_box_of_no_pointwise_approximation
    (target : ℕ × ℕ → ℝ) (competitors : Set (ℕ × ℕ → ℝ))
    (h : ∀ p : ℕ → ℕ × ℕ → ℝ, (∀ n, p n ∈ competitors) →
      (∀ k, Tendsto (fun n => p n k) atTop (𝓝 (target k))) → False) :
    UniformBoxSeparation target competitors := by
  by_contra hsep
  obtain ⟨p, hp, hlim⟩ :=
    exists_pointwise_approximation_of_no_uniform_box target competitors hsep
  exact h p hp hlim

end FiniteCountSeparation
end Rhone.Statistics.Identifiability
