/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerMarginal
public import Rhone.MarkovChain.GeiringerPartition

/-!
# Exact nonlinear duality for finite-mask two-parent recombination

Source: geiringer1944, eq. (41), p. 43, eq. (42)–(44), pp. 44–45. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset

/-- Source: geiringer1944, eq. (41), p. 43, eq. (42)–(44), pp. 44–45. -/
theorem recombination_partition_identity_general
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ) (hp : ∑ h, p h = 1)
    (π : Finpartition (Finset.univ : Finset κ)) (h : κ → Ω) :
    partitionProduct (recombination ρ p) π h =
      ∑ σ, fragmentationMatrix ρ π σ*partitionProduct p σ h := by
  classical
  have hrhs : (∑ σ, fragmentationMatrix ρ π σ*partitionProduct p σ h) =
      ∑ masks : π.parts → Finset κ,
        (∏ B, ρ (masks B))*partitionProduct p (splitPartition π masks) h := by
    unfold fragmentationMatrix
    simp only [sum_mul, mul_assoc]
    rw [sum_comm]
    apply sum_congr rfl
    intro masks _
    rw [← mul_sum]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  rw [hrhs]
  unfold partitionProduct
  simp_rw [marginal_recombination_split]
  rw [← prod_coe_sort]
  have hsum := Fintype.prod_sum (fun B : π.parts => fun mask : Finset κ =>
    ρ mask*marginal p (B.val ∩ mask) h*marginal p (B.val \ mask) h)
  rw [hsum]
  apply sum_congr rfl
  intro masks _
  rw [← partitionProduct, partition_product_split p π masks h hp]
  simp only [prod_mul_distrib]
  ring

/-- Source: geiringer1944, eq. (41), p. 43, eq. (42)–(44), pp. 44–45. -/
theorem recombination_partition_identity
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (π : Finpartition (Finset.univ : Finset κ)) (h : κ → Ω) :
    partitionProduct (recombination ρ p) π h =
      ∑ σ, fragmentationMatrix ρ π σ*partitionProduct p σ h := by
  have _ := hρ0
  have _ := hρ
  have _ := hp0
  exact recombination_partition_identity_general ρ p hp π h

end Rhone.MarkovChain.Geiringer
