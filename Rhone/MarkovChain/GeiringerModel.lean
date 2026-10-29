/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Trajectory
public import Rhone.MarkovChain.Ancestral
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-mask two-parent recombination and its partition fragmentation chain

Source: geiringer1944, eq. (26)–(31), pp. 38–39. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset
/-- Source: geiringer1944, eq. (31), p. 39. -/
noncomputable def assemble {κ Ω : Type*} [DecidableEq κ]
    (mask : Finset κ) (p q : κ → Ω) (l : κ) : Ω :=
  if l ∈ mask then p l else q l

/-- Source: geiringer1944, eq. (31), p. 39. -/
noncomputable def recombination {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ) (h : κ → Ω) : ℝ :=
  ∑ mask, ρ mask * ∑ parent, ∑ other,
    p parent * p other * (if assemble mask parent other = h then 1 else 0)

/-- Source: geiringer1944, p. 38. -/
noncomputable def marginal {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (p : (κ → Ω) → ℝ) (B : Finset κ) (h : κ → Ω) : ℝ :=
  ∑ other, p other * (if ∀ l ∈ B, other l = h l then 1 else 0)

noncomputable def partitionProduct {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (p : (κ → Ω) → ℝ) (π : Finpartition (Finset.univ : Finset κ))
    (h : κ → Ω) : ℝ := ∏ B ∈ π.parts, marginal p B h

noncomputable def splitPartition {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : Finpartition (Finset.univ : Finset κ)) (masks : π.parts → Finset κ) :
    Finpartition (Finset.univ : Finset κ) :=
  π.bind (fun B hB => Finpartition.atomise B {masks ⟨B, hB⟩})

noncomputable def fragmentationMatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (π σ : Finpartition (Finset.univ : Finset κ)) : ℝ :=
  ∑ masks : π.parts → Finset κ,
    (∏ B, ρ (masks B)) * (if splitPartition π masks = σ then 1 else 0)

noncomputable def initialPartition {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ] :
    Finpartition (Finset.univ : Finset κ) :=
  Finpartition.indiscrete Finset.univ_nonempty.ne_empty

noncomputable def separationProbability {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (i j : κ) : ℝ :=
  ∑ mask, ρ mask * (if (i ∈ mask ∧ j ∉ mask) ∨ (i ∉ mask ∧ j ∈ mask) then 1 else 0)

theorem fragmentation_matrix_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask)
    (π σ : Finpartition (Finset.univ : Finset κ)) :
    0 ≤ fragmentationMatrix ρ π σ := by
  classical
  apply sum_nonneg
  intro masks _
  exact mul_nonneg (prod_nonneg fun B _ => hρ0 (masks B)) (by positivity)

theorem fragmentation_matrix_row_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ : ∑ mask, ρ mask = 1)
    (π : Finpartition (Finset.univ : Finset κ)) :
    ∑ σ, fragmentationMatrix ρ π σ = 1 := by
  classical
  unfold fragmentationMatrix
  rw [sum_comm]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [sum_ite_eq, mem_univ, ite_true]
  have h := Fintype.prod_sum (fun (_ : π.parts) (mask : Finset κ) => ρ mask)
  simpa only [hρ, prod_const_one] using h.symm

noncomputable def fragmentationChain {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1) :
    Rhone.MarkovChain.FinChain (Finpartition (Finset.univ : Finset κ)) :=
  ⟨fragmentationMatrix ρ, fragmentation_matrix_nonneg ρ hρ0,
    fragmentation_matrix_row_sum ρ hρ⟩

theorem recombination_preserves_distribution
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) :
    (∀ h, 0 ≤ recombination ρ p h) ∧ ∑ h, recombination ρ p h = 1 := by
  classical
  constructor
  · intro h
    apply sum_nonneg
    intro mask _
    apply mul_nonneg (hρ0 mask)
    apply sum_nonneg
    intro parent _
    apply sum_nonneg
    intro other _
    exact mul_nonneg (mul_nonneg (hp0 parent) (hp0 other)) (by positivity)
  · have hm (mask : Finset κ) :
        (∑ h, ∑ parent, ∑ other,
          p parent*p other*(if assemble mask parent other=h then 1 else 0)) = 1 := by
      calc
        _ = ∑ parent, ∑ other, ∑ h,
            p parent*p other*(if assemble mask parent other=h then 1 else 0) := by
          rw [sum_comm]
          apply sum_congr rfl
          intro parent _
          rw [sum_comm]
        _ = 1 := by
          simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
          simp only [← mul_sum, hp, mul_one]
    unfold recombination
    rw [sum_comm]
    simp_rw [← mul_sum, hm]
    simpa only [mul_one] using hρ

end Rhone.MarkovChain.Geiringer
