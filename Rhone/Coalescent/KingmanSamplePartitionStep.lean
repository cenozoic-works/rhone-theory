/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartition
public import Rhone.Coalescent.KingmanSampleFibreMerge
/-! # Next-event sample-block merger -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset IntervalProcess

theorem samplePartition_succ_eq_mergeBlocks_of_fibres (N : ℕ) (ω : EventPath)
    (k : ℕ) (hvalid : Valid (ω k).1)
    (hcarried : ∀ a : Fin N, ∃ v,
      ((ω k).1.2.2.2 v).1 = ancestorLabel N ω leftBoundaryProbe a k)
    (hsurj : ∀ v, ∃ a : Fin N,
      ancestorLabel N ω leftBoundaryProbe a k = ((ω k).1.2.2.2 v).1)
    (i j : Fin (ω k).1.2.2.1) (hij : i.val < j.val)
    (hmark : (ω (k + 1)).2.2 = .inr (.inl (i.val, j.val))) :
    samplePartition N ω (k + 1) =
      mergeBlocks (samplePartition N ω k)
        {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          ((ω k).1.2.2.2 i).1),
         univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          ((ω k).1.2.2.2 j).1)} := by
  classical
  let a : Fin N → ℕ := fun u => ancestorLabel N ω leftBoundaryProbe u k
  let x := ((ω k).1.2.2.2 i).1
  let y := ((ω k).1.2.2.2 j).1
  let z := (ω k).1.2.1
  let A : Finset (Fin N) := univ.filter (fun u => a u = x)
  let B : Finset (Fin N) := univ.filter (fun u => a u = y)
  have hx : ∃ u, a u = x := hsurj i
  have hy : ∃ u, a u = y := hsurj j
  have hz : ∀ u, a u ≠ z := by
    intro u
    obtain ⟨v, hv⟩ := hcarried u
    have hlt := hvalid.2.2.1 v
    rw [hv] at hlt
    exact ne_of_lt hlt
  have hA : A ∈ (samplePartition N ω k).parts := by
    obtain ⟨u, hu⟩ := hx
    rw [samplePartition_parts]
    exact mem_image.mpr ⟨u, mem_univ u, by simp only [A, a, ← hu]⟩
  have hB : B ∈ (samplePartition N ω k).parts := by
    obtain ⟨u, hu⟩ := hy
    rw [samplePartition_parts]
    exact mem_image.mpr ⟨u, mem_univ u, by simp only [B, a, ← hu]⟩
  have hs : ({A, B} : Finset (Finset (Fin N))) ⊆ (samplePartition N ω k).parts := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hA, hB⟩
  have hli : liveLabelAt (ω k).1 i.val = x := by simp [liveLabelAt, i.isLt, x]
  have hlj : liveLabelAt (ω k).1 j.val = y := by simp [liveLabelAt, j.isLt, y]
  apply Finpartition.ext
  change (samplePartition N ω (k + 1)).parts = (mergeBlocks _ {A, B}).parts
  rw [samplePartition_parts, parts_mergeBlocks hs (by simp)]
  simp only [sup_insert, sup_singleton, id_eq, sup_eq_union, samplePartition_parts]
  have hmerge := image_label_fibres_merge a x y z hx hz
  simpa only [kingmanSampleClades, ancestorLabel, hmark, ancestorStep, hij, j.isLt,
    and_self, ite_eq_left, hli, hlj, a, x, y, z, A, B] using hmerge

theorem samplePartition_succ_eq_mergeBlocks (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1)))
    (k : ℕ) (i j : Fin (ω k).1.2.2.1) (hij : i.val < j.val)
    (hmark : (ω (k + 1)).2.2 = .inr (.inl (i.val, j.val))) :
    samplePartition N ω (k + 1) =
      mergeBlocks (samplePartition N ω k)
        {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          ((ω k).1.2.2.2 i).1),
         univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          ((ω k).1.2.2.2 j).1)} := by
  apply samplePartition_succ_eq_mergeBlocks_of_fibres N ω k (hvalid k)
    (fun a => kingman_sample_present N ω hinit hvalid hstep a k)
    (kingman_path_sample_surjective N ω hinit hvalid hstep k) i j hij hmark
end Rhone.Coalescent.SmcPrime
