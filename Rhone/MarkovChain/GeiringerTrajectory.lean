/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerDuality

/-!
# Nonlinear recombination iterates as expectations of the fragmentation trajectory

Source: geiringer1944, eq. (41), p. 43, eq. (44‴), p. 45. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset MeasureTheory

/-- Source: geiringer1944, eq. (41), p. 43, eq. (44‴), p. 45. -/
theorem recombination_iterate_distribution
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) (t : ℕ) :
    (∀ h, 0 ≤ ((recombination ρ)^[t] p) h) ∧
      ∑ h, ((recombination ρ)^[t] p) h = 1 := by
  induction t with
  | zero => simpa using And.intro hp0 hp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact recombination_preserves_distribution ρ _ hρ0 hρ ih.1 ih.2

/-- Source: geiringer1944, eq. (41), p. 43, eq. (44‴), p. 45. -/
theorem recombination_partition_iterate
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (t : ℕ) (π : Finpartition (Finset.univ : Finset κ)) (h : κ → Ω) :
    partitionProduct ((recombination ρ)^[t] p) π h =
      (fragmentationChain ρ hρ0 hρ).expectN t (fun σ => partitionProduct p σ h) π := by
  induction t generalizing π with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', recombination_partition_identity_general ρ _
      (recombination_iterate_distribution ρ p hρ0 hρ hp0 hp t).2]
    rw [Rhone.MarkovChain.FinChain.expectN_succ, Rhone.MarkovChain.FinChain.expect_apply]
    apply sum_congr rfl
    intro σ _
    rw [ih σ]
    rfl

theorem marginal_univ {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (p : (κ → Ω) → ℝ) (h : κ → Ω) :
    marginal p Finset.univ h = p h := by
  classical
  simp [marginal, ← funext_iff]

theorem partition_product_initial {κ Ω : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (p : (κ → Ω) → ℝ) (h : κ → Ω) : partitionProduct p initialPartition h = p h := by
  simp [partitionProduct, initialPartition, marginal_univ]

/-- Source: geiringer1944, eq. (41), p. 43, eq. (44‴), p. 45. -/
theorem recombination_partition_trajectory
    {κ Ω : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (t : ℕ) (h : κ → Ω) :
    ((recombination ρ)^[t] p) h =
      ∫ ω, partitionProduct p (ω t) h
        ∂(fragmentationChain ρ hρ0 hρ).pathLaw initialPartition := by
  rw [(fragmentationChain ρ hρ0 hρ).integral_eval t
    (fun σ => partitionProduct p σ h) initialPartition,
    ← recombination_partition_iterate ρ p hρ0 hρ hp0 hp]
  exact (partition_product_initial _ h).symm

end Rhone.MarkovChain.Geiringer
