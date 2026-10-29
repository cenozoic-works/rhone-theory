/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartitionGeometry
public import Rhone.Coalescent.SmcPrimeKingmanOneStepMarkLaw
/-! # Live-position pairs and partition merges -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset IntervalProcess

theorem bijOn_kingmanPairSet_sampleMerges (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    Set.BijOn
      (fun p : ℕ × ℕ => mergeBlocks (samplePartition N ω k)
        {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          liveLabelAt (ω k).1 p.1),
         univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          liveLabelAt (ω k).1 p.2)})
      (kingmanPairSet (ω k).1.2.2.1)
      (Rhone.Coalescent.merges (samplePartition N ω k)) := by
  classical
  let π := samplePartition N ω k
  let m := (ω k).1.2.2.1
  let cell (i : Fin m) : Finset (Fin N) := univ.filter
    (fun a => ancestorLabel N ω leftBoundaryProbe a k = ((ω k).1.2.2.2 i).1)
  let φ (p : ℕ × ℕ) := mergeBlocks π
    {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k = liveLabelAt (ω k).1 p.1),
     univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k = liveLabelAt (ω k).1 p.2)}
  have hcell : Function.Injective cell := live_sample_fibres_injective N ω hinit hvalid hstep k
  have hparts : univ.image cell = π.parts :=
    image_live_sample_fibres_eq_parts N ω hinit hvalid hstep k
  have hmem (i : Fin m) : cell i ∈ π.parts := by
    rw [← hparts]
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
  have hφ (p : ℕ × ℕ) (hp : p ∈ kingmanPairSet m) :
      φ p = mergeBlocks π {cell ⟨p.1, lt_trans hp.1 hp.2⟩, cell ⟨p.2, hp.2⟩} := by
    have hfirst : p.1 < (ω k).1.2.2.1 := lt_trans hp.1 hp.2
    have hsecond : p.2 < (ω k).1.2.2.1 := hp.2
    simp only [φ, cell, liveLabelAt, dite_eq_left hfirst, dite_eq_left hsecond]
  have hpair (p : ℕ × ℕ) (hp : p ∈ kingmanPairSet m) :
      ({cell ⟨p.1, lt_trans hp.1 hp.2⟩, cell ⟨p.2, hp.2⟩} : Finset (Finset (Fin N))) ⊆
          π.parts ∧
        ({cell ⟨p.1, lt_trans hp.1 hp.2⟩, cell ⟨p.2, hp.2⟩} :
          Finset (Finset (Fin N))).card = 2 := by
    constructor
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hmem _, hmem _⟩
    · have hn : cell ⟨p.1, lt_trans hp.1 hp.2⟩ ≠ cell ⟨p.2, hp.2⟩ := by
        intro he
        have hv := congrArg Fin.val (hcell he)
        exact Nat.ne_of_lt hp.1 hv
      simp [hn]
  change Set.BijOn φ (kingmanPairSet m) (Rhone.Coalescent.merges π)
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro p hp
    rw [hφ p hp]
    apply mem_image.mpr
    exact ⟨_, mem_powersetCard.mpr (hpair p hp), rfl⟩
  · intro p hp q hq heq
    have hp' := hpair p hp
    have hq' := hpair q hq
    have hsets : ({cell ⟨p.1, lt_trans hp.1 hp.2⟩, cell ⟨p.2, hp.2⟩} :
        Finset (Finset (Fin N))) = {cell ⟨q.1, lt_trans hq.1 hq.2⟩, cell ⟨q.2, hq.2⟩} := by
      rw [← parts_sdiff_parts_mergeBlocks hp'.1 hp'.2,
        ← parts_sdiff_parts_mergeBlocks hq'.1 hq'.2, ← hφ p hp, ← hφ q hq, heq]
    have hpositions : ({⟨p.1, lt_trans hp.1 hp.2⟩, ⟨p.2, hp.2⟩} : Finset (Fin m)) =
        {⟨q.1, lt_trans hq.1 hq.2⟩, ⟨q.2, hq.2⟩} := by
      apply image_injective hcell
      simpa only [image_insert, image_singleton] using hsets
    have h1 : p.1 = q.1 ∨ p.1 = q.2 := by
      have hm : (⟨p.1, lt_trans hp.1 hp.2⟩ : Fin m) ∈
          ({⟨p.1, lt_trans hp.1 hp.2⟩, ⟨p.2, hp.2⟩} : Finset (Fin m)) := by simp
      rw [hpositions] at hm
      simpa only [mem_insert, mem_singleton, Fin.ext_iff] using hm
    have h2 : p.2 = q.1 ∨ p.2 = q.2 := by
      have hm : (⟨p.2, hp.2⟩ : Fin m) ∈
          ({⟨p.1, lt_trans hp.1 hp.2⟩, ⟨p.2, hp.2⟩} : Finset (Fin m)) := by simp
      rw [hpositions] at hm
      simpa only [mem_insert, mem_singleton, Fin.ext_iff] using hm
    have hp_lt : p.1 < p.2 := hp.1
    have hq_lt : q.1 < q.2 := hq.1
    apply Prod.ext <;> omega
  · intro σ hσ
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hσ
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
    obtain ⟨A, B, hne, rfl⟩ := card_eq_two.mp hcard
    obtain ⟨i, -, hi⟩ := mem_image.mp (hparts.symm ▸ hsub (by simp : A ∈ ({A, B} : Finset _)))
    obtain ⟨j, -, hj⟩ := mem_image.mp (hparts.symm ▸ hsub (by simp : B ∈ ({A, B} : Finset _)))
    have hn : i.val ≠ j.val := by
      intro hv
      have he : i = j := Fin.ext hv
      exact hne (hi.symm.trans (by rw [he]; exact hj))
    rcases lt_or_gt_of_ne hn with hij | hji
    · refine ⟨(i.val, j.val), ⟨hij, j.isLt⟩, ?_⟩
      rw [hφ (i.val, j.val) ⟨hij, j.isLt⟩]
      change mergeBlocks π {cell i, cell j} = _
      rw [hi, hj]
    · refine ⟨(j.val, i.val), ⟨hji, i.isLt⟩, ?_⟩
      rw [hφ (j.val, i.val) ⟨hji, i.isLt⟩]
      change mergeBlocks π {cell j, cell i} = _
      rw [hi, hj, pair_comm]
end Rhone.Coalescent.SmcPrime
