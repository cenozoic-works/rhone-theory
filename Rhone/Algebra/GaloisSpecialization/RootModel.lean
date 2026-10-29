/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Action.Invariant

/-! # The integral root-generated model of a monic polynomial -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial _root_.Algebra

variable (A L : Type*) [CommRing A] [Field L] [Algebra A L]

noncomputable def rootModel (p : A[X]) : Subalgebra A L := Algebra.adjoin A (p.rootSet L)

variable {A L}

theorem root_integral_of_monic {p : A[X]} (hp : p.Monic) {x : L}
    (hx : x ∈ p.rootSet L) : IsIntegral A x :=
  ⟨p, hp, (Polynomial.mem_rootSet'.mp hx).2⟩

theorem rootModel_integral {p : A[X]} (hp : p.Monic) :
    Algebra.IsIntegral A (rootModel A L p) :=
  Algebra.IsIntegral.adjoin (fun _ hx => root_integral_of_monic hp hx)

theorem rootModel_finite {p : A[X]} (hp : p.Monic) :
    Module.Finite A (rootModel A L p) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral (p.rootSet_finite L)
    (fun _ hx => root_integral_of_monic hp hx)

theorem rootModel_generated_by_roots (p : A[X]) :
    Algebra.adjoin A {b : rootModel A L p |
      (p.map (algebraMap A (rootModel A L p))).IsRoot b} = ⊤ := by
  let B := rootModel A L p
  let C := Algebra.adjoin A {b : B | (p.map (algebraMap A B)).IsRoot b}
  have hmem : ∀ x (hx : x ∈ Algebra.adjoin A (p.rootSet L)), (⟨x, hx⟩ : B) ∈ C := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      let b : B := ⟨x, Algebra.subset_adjoin hx⟩
      change (p.map (algebraMap A B)).IsRoot b
      rw [IsRoot.def, eval_map_algebraMap]
      apply Subtype.val_injective
      change B.val (aeval b p) = 0
      rw [← aeval_algHom_apply]
      exact (Polynomial.mem_rootSet'.mp hx).2
    | algebraMap a =>
      exact Subalgebra.algebraMap_mem C a
    | add x y _ _ hx hy =>
      exact C.add_mem hx hy
    | mul x y _ _ hx hy =>
      exact C.mul_mem hx hy
  apply _root_.eq_top_iff.mpr
  intro b _
  exact hmem b.val b.property

variable {G : Type*} [Group G] [MulSemiringAction G L] [SMulCommClass G A L]

theorem rootModel_smul_mem (p : A[X]) (g : G) {x : L}
    (hx : x ∈ rootModel A L p) : g • x ∈ rootModel A L p := by
  change x ∈ Algebra.adjoin A (p.rootSet L) at hx
  change g • x ∈ Algebra.adjoin A (p.rootSet L)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    apply Algebra.subset_adjoin
    obtain ⟨hne, hroot⟩ := Polynomial.mem_rootSet'.mp hx
    apply Polynomial.mem_rootSet'.mpr
    exact ⟨hne, by rw [aeval_smul, hroot, smul_zero]⟩
  | algebraMap a =>
    rw [smul_algebraMap]
    exact Subalgebra.algebraMap_mem _ a
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [smul_mul']
    exact mul_mem hx hy

instance rootModel_invariantSubring (p : A[X]) :
    IsInvariantSubring G (rootModel A L p).toSubring where
  smul_mem g _ hx := rootModel_smul_mem p g hx

end Rhone.Algebra.GaloisSpecialization
