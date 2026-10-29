/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Marginal

/-! # The ESF-pair decomposition assembled, and the IBD covariance kernel -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n : ℕ} {θA θB ρ : ℝ}

theorem sum_esfKernel_eq_one' (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    (∑ ζB : Blocks n, ∑ ζA : Blocks n, esfKernel θA θB ρ ζA ζB) = 1 := by
  rw [← sum_esfKernel_eq_one (n := n) hθA hθB hρ, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_esfPart_eq_one {θ : ℝ} (hθ : 0 < θ) : (∑ ζ : Blocks n, esfPart n θ ζ) = 1 := by
  have h : ∀ ζB : Blocks n, esfPart n θ ζB = margB θ θ 0 ζB :=
    fun ζB => (margB_eq_esfPart hθ hθ le_rfl ζB).symm
  rw [Finset.sum_congr rfl fun ζB _ => h ζB]
  exact sum_esfKernel_eq_one' hθ hθ le_rfl

theorem exists_esf_pair_law_with_esf_marginals (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (n : ℕ) :
    ∃ P : Blocks n → Blocks n → ℝ,
      (∀ ζA ζB, 0 ≤ P ζA ζB) ∧
      (∑ x : Blocks n × Blocks n, P x.1 x.2) = 1 ∧
      (∀ ζA, (∑ ζB, P ζA ζB) = esfPart n θA ζA) ∧
      (∀ ζB, (∑ ζA, P ζA ζB) = esfPart n θB ζB) ∧
      ∀ (KA KB : ℕ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (_ : ∀ i, 0 ≤ πA i)
        (_ : ∑ i, πA i = 1) (_ : ∀ j, 0 ≤ πB j) (_ : ∑ j, πB j = 1)
        (σA : Fin n → Fin KA) (σB : Fin n → Fin KB),
        LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
          = ∑ ζA : Blocks n, ∑ ζB : Blocks n, P ζA ζB * wA σA πA ζA * wB σB πB ζB :=
  ⟨esfKernel θA θB ρ, esfKernel_nonneg hθA hθB hρ, sum_esfKernel_eq_one hθA hθB hρ,
    margA_eq_esfPart hθA hθB hρ, margB_eq_esfPart hθA hθB hρ,
    fun _ _ _ _ hπA hsA hπB hsB σA σB => esf_pair_decomposition hθA hθB hρ hπA hsA hπB hsB σA σB⟩

noncomputable def covKernel (n : ℕ) (θA θB ρ : ℝ) (ζA ζB : Blocks n) : ℝ :=
  esfKernel θA θB ρ ζA ζB - esfPart n θA ζA * esfPart n θB ζB

theorem sum_covKernel_row (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζA : Blocks n) :
    (∑ ζB : Blocks n, covKernel n θA θB ρ ζA ζB) = 0 := by
  simp only [covKernel, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [margA_eq_esfPart hθA hθB hρ ζA, sum_esfPart_eq_one hθB, mul_one, sub_self]

theorem sum_covKernel_col (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζB : Blocks n) :
    (∑ ζA : Blocks n, covKernel n θA θB ρ ζA ζB) = 0 := by
  have h : ∀ ζA : Blocks n, covKernel n θA θB ρ ζA ζB
      = esfKernel θA θB ρ ζA ζB - esfPart n θB ζB * esfPart n θA ζA := by
    intro ζA
    rw [covKernel]
    ring
  simp only [Finset.sum_congr rfl fun ζA _ => h ζA, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← margB, margB_eq_esfPart hθA hθB hρ ζB, sum_esfPart_eq_one hθA, mul_one, sub_self]

def meet (ζA ζB : Blocks n) : Blocks n := (((ζA ×ˢ ζB).image fun x => x.1 ∩ x.2)).erase ∅

theorem mem_meet {ζA ζB : Blocks n} {δ : Finset (Fin n)} :
    δ ∈ meet ζA ζB ↔ δ ≠ ∅ ∧ ∃ β ∈ ζA, ∃ γ ∈ ζB, β ∩ γ = δ := by
  simp only [meet, Finset.mem_erase, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨hne, ⟨β, γ⟩, ⟨hβ, hγ⟩, hd⟩
    exact ⟨hne, β, hβ, γ, hγ, hd⟩
  · rintro ⟨hne, β, hβ, γ, hγ, hd⟩
    exact ⟨hne, ⟨β, γ⟩, ⟨hβ, hγ⟩, hd⟩

theorem meet_isPartOf {S : Finset (Fin n)} {ζA ζB : Blocks n} (hA : IsPartOf S ζA)
    (hB : IsPartOf S ζB) : IsPartOf S (meet ζA ζB) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    exact Finset.nonempty_iff_ne_empty.2 (mem_meet.1 hδ).1
  · rintro δ hδ δ' hδ' hne
    obtain ⟨-, β, hβ, γ, hγ, rfl⟩ := mem_meet.1 hδ
    obtain ⟨-, β', hβ', γ', hγ', rfl⟩ := mem_meet.1 hδ'
    by_cases hb : β = β'
    · subst hb
      have hg : γ ≠ γ' := fun hc => hne (by rw [hc])
      exact ((hB.pd γ hγ γ' hγ' hg).mono Finset.inter_subset_right Finset.inter_subset_right)
    · exact ((hA.pd β hβ β' hβ' hb).mono Finset.inter_subset_left Finset.inter_subset_left)
  · ext k
    constructor
    · intro hk
      obtain ⟨δ, hδ, hkδ⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨-, β, hβ, γ, hγ, hbg⟩ := mem_meet.1 hδ
      have hkβ : k ∈ β := by
        have : k ∈ β ∩ γ := by rw [hbg]; exact hkδ
        exact (Finset.mem_inter.1 this).1
      exact hA.block_subset hβ hkβ
    · intro hk
      obtain ⟨β, hβ, hkβ⟩ := hA.exists_block hk
      obtain ⟨γ, hγ, hkγ⟩ := hB.exists_block hk
      have hkm : k ∈ β ∩ γ := Finset.mem_inter.2 ⟨hkβ, hkγ⟩
      refine Finset.mem_biUnion.2 ⟨β ∩ γ, mem_meet.2 ⟨?_, β, hβ, γ, hγ, rfl⟩, hkm⟩
      exact Finset.nonempty_iff_ne_empty.1 ⟨k, hkm⟩

noncomputable def meetLaw (n : ℕ) (θA θB ρ : ℝ) (ζ : Blocks n) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset (Blocks n × Blocks n)).filter fun x => meet x.1 x.2 = ζ,
    esfKernel θA θB ρ x.1 x.2

theorem sum_meetLaw_eq_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    (∑ ζ : Blocks n, meetLaw n θA θB ρ ζ) = 1 := by
  rw [← sum_esfKernel_eq_one (n := n) hθA hθB hρ]
  exact Finset.sum_fiberwise (Finset.univ : Finset (Blocks n × Blocks n))
    (fun x => meet x.1 x.2) (fun x => esfKernel θA θB ρ x.1 x.2)

theorem meetLaw_eq_zero {ζ : Blocks n} (h : ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    meetLaw n θA θB ρ ζ = 0 := by
  refine Finset.sum_eq_zero fun x hx => ?_
  refine esfKernel_eq_zero_of_not_part fun hc => h ?_
  rw [← (Finset.mem_filter.1 hx).2]
  exact meet_isPartOf hc.1 hc.2

end Rhone.Coalescent.EsfPair
