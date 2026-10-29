/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Decomp

/-! # `P` is supported on pairs of set partitions -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset Filter Topology TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ} {θA θB ρ : ℝ} {ζA ζB : Blocks n}

theorem hitNP_eq_zero_of_not_part (N : ℕ) {s : PSt n} (hs : WFP s)
    (h : ¬ (IsPartOf (spanA s) ζA ∧ IsPartOf (spanB s) ζB)) :
    hitNP ζA ζB θA θB ρ N s = 0 := by
  induction N generalizing s with
  | zero =>
    rw [hitNP_zero]
    split_ifs with he
    · rw [hitAt, ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact h (isPartOf_of_absorbed hs he)
    · rfl
  | succ N ih =>
    by_cases he : s.1 = ∅
    · rw [hitNP_of_empty _ he, hitAt, ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact h (isPartOf_of_absorbed hs he)
    · rw [hitNP_succ_of_ne N he]
      have hzero : stepP θA θB ρ (hitNP ζA ζB θA θB ρ N) s = 0 := by
        have h1 : (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, hitNP ζA ζB θA θB ρ N (coalP s p q)) = 0 := by
          refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
          refine ih (hs.coal hp hq) ?_
          rwa [spanA_coal hp hq, spanB_coal hp hq]
        have h2 : (∑ p ∈ carA s.1, hitNP ζA ζB θA θB ρ N (mutAP s p)) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hpL : p ∈ s.1 := carA_subset _ hp
          refine ih (hs.mutA hp) ?_
          rwa [spanA_mutA hs.wf hpL, spanB_mutA hs.wf hpL]
        have h3 : (∑ p ∈ carB s.1, hitNP ζA ζB θA θB ρ N (mutBP s p)) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have hpL : p ∈ s.1 := carB_subset _ hp
          refine ih (hs.mutB hp) ?_
          rwa [spanA_mutB hs.wf hpL, spanB_mutB hs.wf hpL]
        have h4 : (∑ p ∈ carC s.1, hitNP ζA ζB θA θB ρ N (recP s p)) = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          obtain ⟨hpL, hn1, hn2⟩ := mem_carC.1 hp
          refine ih (hs.recomb hpL hn1 hn2) ?_
          rwa [spanA_rec hs.wf hpL, spanB_rec hs.wf hpL]
        rw [stepP, h1, h2, h3, h4]
        ring
      rw [hzero, zero_div]

theorem PPst_eq_zero_of_not_part {s : PSt n} (hs : WFP s)
    (h : ¬ (IsPartOf (spanA s) ζA ∧ IsPartOf (spanB s) ζB)) :
    PPst θA θB ρ ζA ζB s = 0 := by
  have hz : (fun N => hitNP ζA ζB θA θB ρ N s) = fun _ : ℕ => (0 : ℝ) :=
    funext fun N => hitNP_eq_zero_of_not_part (θA := θA) (θB := θB) (ρ := ρ) N hs h
  rw [PPst, hz, ciSup_const]

theorem coverA_fullState : coverA (fullState n) = Finset.univ := by
  ext k
  simp only [mem_coverA, Finset.mem_univ, iff_true]
  exact ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, Finset.mem_singleton_self k⟩

theorem coverB_fullState : coverB (fullState n) = Finset.univ := by
  ext k
  simp only [mem_coverB, Finset.mem_univ, iff_true]
  exact ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, Finset.mem_singleton_self k⟩

@[simp] theorem spanA_initP : spanA (initP n) = Finset.univ := by
  rw [spanA]
  change coverA (fullState n) ∪ (∅ : Blocks n).biUnion id = Finset.univ
  rw [coverA_fullState]
  simp

@[simp] theorem spanB_initP : spanB (initP n) = Finset.univ := by
  rw [spanB]
  change coverB (fullState n) ∪ (∅ : Blocks n).biUnion id = Finset.univ
  rw [coverB_fullState]
  simp

theorem esfKernel_eq_zero_of_not_part
    (h : ¬ (IsPartOf (Finset.univ : Finset (Fin n)) ζA ∧
      IsPartOf (Finset.univ : Finset (Fin n)) ζB)) :
    esfKernel θA θB ρ ζA ζB = 0 := by
  refine PPst_eq_zero_of_not_part wfp_initP ?_
  rwa [spanA_initP, spanB_initP]

theorem eq_empty_of_isPartOf_empty {ζ : Blocks n} (h : IsPartOf ∅ ζ) : ζ = ∅ := by
  by_contra hc
  obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.2 hc
  obtain ⟨k, hk⟩ := h.ne β hβ
  have : k ∈ ζ.biUnion id := Finset.mem_biUnion.2 ⟨β, hβ, hk⟩
  rw [h.cover] at this
  exact absurd this (Finset.notMem_empty k)

end Rhone.Coalescent.EsfPair
