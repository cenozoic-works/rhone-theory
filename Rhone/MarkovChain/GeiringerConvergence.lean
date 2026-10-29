/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerAbsorption

/-!
# Geiringer's convergence of recombination iterates to the product of marginals

Source: geiringer1944, Thm. II, p. 42, eq. (37), p. 41. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset Filter
open scoped Topology

theorem partition_product_bottom {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (p : (κ → Ω) → ℝ) (h : κ → Ω) :
    partitionProduct p ⊥ h = ∏ l, marginal p {l} h := by
  simp only [partitionProduct, Finpartition.parts_bot, prod_map, Function.Embedding.coeFn_mk]

theorem fragmentation_partition_expectation_converges
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j)
    (π : Finpartition (Finset.univ : Finset κ)) (h : κ → Ω) :
    Filter.Tendsto (fun t : ℕ =>
      (fragmentationChain ρ hρ0 hρ).expectN t (fun σ => partitionProduct p σ h) π)
      Filter.atTop (nhds (partitionProduct p ⊥ h)) := by
  classical
  let C := fragmentationChain ρ hρ0 hρ
  let g := fun σ => partitionProduct p σ h-partitionProduct p ⊥ h
  let M := ∑ σ, |g σ|
  have hA : C.IsAbsorbingSet {⊥} := by
    intro σ hσ
    obtain rfl := mem_singleton.mp hσ
    exact fragmentation_bottom_absorbing ρ hρ0 hρ
  have hR : C.Reaches {⊥} := fragmentation_reaches_bottom ρ hρ0 hρ hsep
  have hg0 : ∀ σ ∈ ({⊥} : Finset (Finpartition (Finset.univ : Finset κ))), g σ = 0 := by
    intro σ hσ
    obtain rfl := mem_singleton.mp hσ
    exact sub_self _
  have hgM : ∀ σ, |g σ| ≤ M := fun σ =>
    single_le_sum (fun σ _ => abs_nonneg (g σ)) (mem_univ σ)
  have hbound (t : ℕ) : |C.expectN t g π| ≤ M*C.survival {⊥} t π :=
    C.abs_expectN_le_survival hg0 hgM t π
  have hlim : Tendsto (fun t => M*C.survival {⊥} t π) atTop (nhds 0) := by
    simpa only [mul_zero] using (C.tendsto_survival hA hR π).const_mul M
  have habs : Tendsto (fun t => |C.expectN t g π|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound hlim
  have hzero : Tendsto (fun t => C.expectN t g π) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using habs
  have heq (t : ℕ) : C.expectN t g π =
      C.expectN t (fun σ => partitionProduct p σ h) π-partitionProduct p ⊥ h := by
    rw [Rhone.MarkovChain.FinChain.expectN_apply, Rhone.MarkovChain.FinChain.expectN_apply]
    simp only [g, mul_sub, sum_sub_distrib, ← sum_mul, C.stepN_row_sum, one_mul]
  simpa only [heq, sub_add_cancel, zero_add] using hzero.add_const (partitionProduct p ⊥ h)

/-- Source: geiringer1944, Thm. II, p. 42, eq. (37), p. 41. -/
theorem geiringer_recombination_converges
    {κ Ω : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j) :
    Filter.Tendsto (fun t : ℕ => (recombination ρ)^[t] p) Filter.atTop
      (nhds (fun h => ∏ l, marginal p {l} h)) := by
  apply tendsto_pi_nhds.mpr
  intro h
  have hl := fragmentation_partition_expectation_converges ρ p hρ0 hρ hsep initialPartition h
  simpa only [← recombination_partition_iterate ρ p hρ0 hρ hp0 hp,
    partition_product_initial, partition_product_bottom] using hl

end Rhone.MarkovChain.Geiringer
