/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.InfiniteAllelesLimit.Window

/-! # Decomposition of the Ewens sampling formula pair kernel over refining partitions -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset TwoLocusGenealogy EsfPair LinearAlgebra.Recursion

variable {n K KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def classOf (σ : Fin n → Fin K) : Blocks n :=
  ((Finset.univ : Finset (Fin K)).image fun i => Finset.univ.filter fun k => σ k = i).erase ∅

theorem mem_classOf {σ : Fin n → Fin K} {β : Finset (Fin n)} :
    β ∈ classOf σ ↔ β ≠ ∅ ∧ ∃ i, (Finset.univ.filter fun k => σ k = i) = β := by
  simp [classOf, Finset.mem_erase, Finset.mem_image]

theorem fibre_mem_classOf (σ : Fin n → Fin K) (k : Fin n) :
    (Finset.univ.filter fun l => σ l = σ k) ∈ classOf σ := by
  refine mem_classOf.2 ⟨?_, σ k, rfl⟩
  intro hc
  have : k ∈ Finset.univ.filter fun l => σ l = σ k :=
    Finset.mem_filter.2 ⟨Finset.mem_univ k, rfl⟩
  rw [hc] at this
  exact absurd this (Finset.notMem_empty k)

theorem isPartOf_classOf (σ : Fin n → Fin K) :
    IsPartOf (Finset.univ : Finset (Fin n)) (classOf σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    exact Finset.nonempty_iff_ne_empty.2 (mem_classOf.1 hβ).1
  · rintro β hβ β' hβ' hne
    obtain ⟨-, i, rfl⟩ := mem_classOf.1 hβ
    obtain ⟨-, i', rfl⟩ := mem_classOf.1 hβ'
    refine Finset.disjoint_left.2 fun k hk hk' => hne ?_
    have h1 := (Finset.mem_filter.1 hk).2
    have h2 := (Finset.mem_filter.1 hk').2
    rw [← h1, ← h2]
  · ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, id]
    exact ⟨_, fibre_mem_classOf σ k, Finset.mem_filter.2 ⟨Finset.mem_univ k, rfl⟩⟩

theorem refines_classOf_iff {σ : Fin n → Fin K} {η : Blocks n}
    (hη : ∀ β ∈ η, β.Nonempty) :
    Refines η (classOf σ) ↔ ∀ β ∈ η, ∀ k ∈ β, ∀ l ∈ β, σ k = σ l := by
  constructor
  · intro h β hβ k hk l hl
    obtain ⟨γ, hγ, hsub⟩ := h β hβ
    obtain ⟨-, i, rfl⟩ := mem_classOf.1 hγ
    rw [(Finset.mem_filter.1 (hsub hk)).2, (Finset.mem_filter.1 (hsub hl)).2]
  · intro h β hβ
    obtain ⟨k₀, hk₀⟩ := hη β hβ
    refine ⟨Finset.univ.filter fun l => σ l = σ k₀, fibre_mem_classOf σ k₀, fun l hl => ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ l, h β hβ l hl k₀ hk₀⟩

theorem wA_eq_zero_of_not_refines {σ : Fin n → Fin K} {π : Fin K → ℝ} {η : Blocks n}
    (hη : ∀ β ∈ η, β.Nonempty) (h : ¬ Refines η (classOf σ)) : wA σ π η = 0 := by
  rw [refines_classOf_iff hη] at h
  push Not at h
  obtain ⟨β, hβ, k, hk, l, hl, hkl⟩ := h
  refine Finset.prod_eq_zero hβ (matchA_eq_zero fun hmono => hkl ?_)
  exact hmono k hk l hl

theorem esf_pair_decomposition_refines (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
      = ∑ ηA ∈ refSet (classOf σA), ∑ ηB ∈ refSet (classOf σB),
          esfKernel θA θB ρ ηA ηB * wA σA πA ηA * wB σB πB ηB := by
  have hzA : ∀ ηA : Blocks n, ηA ∉ refSet (classOf σA) → ∀ ηB : Blocks n,
      esfKernel θA θB ρ ηA ηB * wA σA πA ηA * wB σB πB ηB = 0 := by
    intro ηA hηA ηB
    by_cases hp : IsPartOf (Finset.univ : Finset (Fin n)) ηA
    · have hnr : ¬ Refines ηA (classOf σA) := fun hc => hηA (mem_refSet.2 ⟨hp, hc⟩)
      rw [wA_eq_zero_of_not_refines hp.ne hnr, mul_zero, zero_mul]
    · rw [esfKernel_eq_zero_of_not_part fun hc => hp hc.1, zero_mul, zero_mul]
  have hzB : ∀ ηA ηB : Blocks n, ηB ∉ refSet (classOf σB) →
      esfKernel θA θB ρ ηA ηB * wA σA πA ηA * wB σB πB ηB = 0 := by
    intro ηA ηB hηB
    by_cases hp : IsPartOf (Finset.univ : Finset (Fin n)) ηB
    · have hnr : ¬ Refines ηB (classOf σB) := fun hc => hηB (mem_refSet.2 ⟨hp, hc⟩)
      rw [show wB σB πB ηB = wA σB πB ηB from rfl, wA_eq_zero_of_not_refines hp.ne hnr, mul_zero]
    · rw [esfKernel_eq_zero_of_not_part fun hc => hp hc.2, zero_mul, zero_mul]
  rw [esf_pair_decomposition hθA hθB hρ hπA hsA hπB hsB σA σB,
    ← Finset.sum_subset (Finset.subset_univ (refSet (classOf σA)))
      (fun ηA _ h => Finset.sum_eq_zero fun ηB _ => hzA ηA h ηB)]
  refine Finset.sum_congr rfl fun ηA _ => ?_
  exact (Finset.sum_subset (Finset.subset_univ (refSet (classOf σB)))
    (fun ηB _ h => hzB ηA ηB h)).symm

end Rhone.Coalescent.InfiniteAllelesLimit
