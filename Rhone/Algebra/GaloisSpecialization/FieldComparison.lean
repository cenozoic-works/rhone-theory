/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.General

/-! # Splitting fields over isomorphic base fields -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {R S L : Type*} [Field R] [Field S] [Field L]
    [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]

theorem isSplittingField_of_surjective_base (h : Function.Surjective (algebraMap R S))
    (p : R[X]) [IsSplittingField S L (p.map (algebraMap R S))] :
    IsSplittingField R L p := by
  have hroots : (p.map (algebraMap R S)).rootSet L = p.rootSet L := by
    simp only [rootSet, aroots, map_map, ← IsScalarTower.algebraMap_eq]
  constructor
  · have hs := IsSplittingField.splits L (p.map (algebraMap R S))
    rwa [map_map, ← IsScalarTower.algebraMap_eq] at hs
  · let B := Algebra.adjoin R (p.rootSet L)
    apply _root_.Algebra.eq_top_iff.mpr
    intro x
    have hx : x ∈ Algebra.adjoin S (p.rootSet L) := by
      rw [← hroots, IsSplittingField.adjoin_rootSet]
      exact Algebra.mem_top
    change x ∈ B
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap s =>
      obtain ⟨r, rfl⟩ := h s
      rw [← IsScalarTower.algebraMap_apply R S L]
      exact B.algebraMap_mem r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy

end Rhone.Algebra.GaloisSpecialization
