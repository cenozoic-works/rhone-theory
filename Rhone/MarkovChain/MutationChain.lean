/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MutationModels
public import Rhone.MarkovChain.Trajectory
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Trajectories of the explicitly specified parent independent allele mutation chain

Source: ewens2004, eq. (12.14), p. 376, eq. (12.5)–(12.6), pp. 373–374. -/
@[expose] public section
namespace Rhone.MarkovChain.MutationModels
open Finset

/-- Source: ewens2004, eq. (12.14), p. 376. -/
noncomputable def pimChain {A : Type*} [Fintype A] [DecidableEq A]
    (u : ℝ) (π : A → ℝ) (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : Rhone.MarkovChain.FinChain A :=
  ⟨Dynamics.MutationModels.pimTransition u π,
      (Dynamics.MutationModels.pim_markov u π hπ0 hπ hu0 hu1).1,
    (Dynamics.MutationModels.pim_markov u π hπ0 hπ hu0 hu1).2⟩

/-- Source: ewens2004, eq. (12.5)–(12.6), pp. 373–374, eq. (12.14), p. 376. -/
theorem pim_stepN_formula
    {A : Type*} [Fintype A] [DecidableEq A]
    (u : ℝ) (π : A → ℝ) (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℕ) (i j : A) :
    (pimChain u π hπ0 hπ hu0 hu1).stepN t i j =
      (1-u)^t*(if i=j then 1 else 0) + (1-(1-u)^t)*π j := by
  induction t generalizing i j with
  | zero =>
    rw [Rhone.MarkovChain.FinChain.stepN_zero, Matrix.one_apply]
    simp
  | succ t ih =>
    rw [Rhone.MarkovChain.FinChain.stepN_succ', Matrix.mul_apply]
    change (∑ k, (pimChain u π hπ0 hπ hu0 hu1).stepN t i k * Dynamics.MutationModels.pimTransition u
        π k j) = _
    simp only [ih, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
    have hdiag : (∑ k, (if i=k then (1:ℝ) else 0) * Dynamics.MutationModels.pimTransition u π k j) =
        Dynamics.MutationModels.pimTransition u π i j := by simp [ite_mul]
    rw [hdiag, Dynamics.MutationModels.pim_stationary u π hπ j]
    simp only [Dynamics.MutationModels.pimTransition, pow_succ]
    ring

/-- Source: ewens2004, eq. (12.5)–(12.6), pp. 373–374, eq. (2.137), p. 87. -/
theorem pim_trajectory_allele_probability
    {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (u : ℝ) (π : A → ℝ) (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℕ) (i j : A) :
    ((pimChain u π hπ0 hπ hu0 hu1).pathLaw i).real {ω | ω t=j} =
      (1-u)^t*(if i=j then 1 else 0) + (1-(1-u)^t)*π j := by
  rw [Rhone.MarkovChain.FinChain.pathLaw_real_eval]
  exact pim_stepN_formula u π hπ0 hπ hu0 hu1 t i j

/-- Source: ewens2004, sec. 2.12, eq. (2.156)–(2.157), p. 90, eq. (12.14), p. 376. -/
theorem pim_trajectory_converges
    {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (u : ℝ) (π : A → ℝ) (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (i j : A) :
    Filter.Tendsto (fun t =>
      ((pimChain u π hπ0 hπ (le_of_lt hu0) hu1).pathLaw i).real {ω | ω t=j})
      Filter.atTop (nhds (π j)) := by
  have hpow : Filter.Tendsto (fun t : ℕ => (1-u)^t) Filter.atTop (nhds (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hu1) (by linarith)
  simp only [pim_trajectory_allele_probability]
  have h := (hpow.mul_const (if i=j then (1:ℝ) else 0)).add
    ((hpow.const_sub (1 : ℝ)).mul_const (π j))
  simpa using h

end Rhone.MarkovChain.MutationModels
