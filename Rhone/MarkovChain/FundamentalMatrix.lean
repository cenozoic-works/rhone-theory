/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.AbsorptionProb
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The fundamental matrix of an absorbing finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open Finset Matrix

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S) (A : Finset S)

abbrev Transient (A : Finset S) : Type _ := {x : S // x ∉ A}

def transientBlock : Matrix (Transient A) (Transient A) ℝ := fun x y => C.P x y

def absorbBlock : Matrix (Transient A) {a : S // a ∈ A} ℝ := fun x a => C.P x a

variable {C}

theorem sum_P_mul_eq (A : Finset S) (g : S → ℝ) (x : S) :
    ∑ y, C.P x y * g y = ∑ y : Transient A, C.P x y * g y + ∑ a : {a : S // a ∈ A}, C.P x a * g a :=
  by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y => y ∈ A) fun y => C.P x y * g y, add_comm]
  congr!

variable {A}

def extendZero (v : Transient A → ℝ) : S → ℝ := fun x => if h : x ∈ A then 0 else v ⟨x, h⟩

omit [Fintype S] in
theorem extendZero_of_mem (v : Transient A → ℝ) {a : S} (ha : a ∈ A) : extendZero v a = 0 := by
  simp [extendZero, ha]

omit [Fintype S] in
theorem extendZero_of_not_mem (v : Transient A → ℝ) (x : Transient A) :
    extendZero v x.1 = v x := by
  simp [extendZero, x.2]

theorem sum_P_mul_extendZero (v : Transient A → ℝ) (x : S) :
    ∑ y, C.P x y * extendZero v y = ∑ y : Transient A, C.P x y * v y := by
  rw [sum_P_mul_eq A]
  have h1 : ∑ a : {a : S // a ∈ A}, C.P x a * extendZero v a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [extendZero_of_mem v a.2, mul_zero]
  rw [h1, add_zero]
  exact Finset.sum_congr rfl fun y _ => by rw [extendZero_of_not_mem v y]

theorem one_sub_transientBlock_mulVec_apply (u : Transient A → ℝ) (y : Transient A) :
    ((1 - C.transientBlock A) *ᵥ u) y = u y - ∑ z : Transient A, C.P y z * u z := by
  rw [sub_mulVec, one_mulVec]
  rfl

theorem isUnit_one_sub_transientBlock (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) :
    IsUnit (1 - C.transientBlock A) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv0
  have hharm : C.IsHarmonic (extendZero v) := by
    funext x
    rw [expect_apply]
    by_cases hx : x ∈ A
    · rw [extendZero_of_mem v hx]
      simp [(hA x hx).P_apply, extendZero_of_mem v hx]
    · rw [sum_P_mul_extendZero]
      have : v ⟨x, hx⟩ - ∑ z : Transient A, C.P x z * v z = 0 :=
        (one_sub_transientBlock_mulVec_apply v ⟨x, hx⟩).symm.trans (congrFun hv ⟨x, hx⟩)
      rw [extendZero_of_not_mem v ⟨x, hx⟩]
      linarith
  have hzero := hharm.eq_zero_of_eqOn hA hR fun a ha => extendZero_of_mem v ha
  funext x
  have := congrFun hzero x.1
  rwa [extendZero_of_not_mem v x] at this

theorem eq_fundamental_mulVec (hA : C.IsAbsorbingSet A) (hR : C.Reaches A)
    {u w : Transient A → ℝ} (h : (1 - C.transientBlock A) *ᵥ u = w) :
    u = (1 - C.transientBlock A)⁻¹ *ᵥ w := by
  have hu := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_transientBlock hA hR))
  rw [← h, mulVec_mulVec, hu, one_mulVec]

theorem absorbProb_eq_fundamental_mul (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) :
    (fun (x : Transient A) (a : {a : S // a ∈ A}) => C.absorbProb a x) =
      (1 - C.transientBlock A)⁻¹ * C.absorbBlock A := by
  funext x a
  have hcol : (1 - C.transientBlock A) *ᵥ (fun y : Transient A => C.absorbProb a y) =
      fun y : Transient A => C.P y a := by
    funext y
    have hh := congrFun (absorbProb_isHarmonic (hA a a.2)) y
    rw [expect_apply, sum_P_mul_eq A] at hh
    have h2 : ∑ b : {b : S // b ∈ A}, C.P y b * C.absorbProb a b = C.P y a := by
      rw [Finset.sum_eq_single a]
      · simp [absorbProb_of_isAbsorbing (hA a a.2)]
      · intro b _ hb
        have hba : (b : S) ≠ a := fun h => hb (Subtype.ext h)
        simp [absorbProb_of_isAbsorbing (hA b b.2), hba]
      · exact fun h => absurd (mem_univ a) h
    rw [h2] at hh
    rw [one_sub_transientBlock_mulVec_apply]
    linarith
  have := congrFun (eq_fundamental_mulVec hA hR hcol) x
  rw [this]
  rfl

theorem absorbTime_eq_fundamental_mulVec (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) :
    (fun x : Transient A => C.absorbTime A x) = (1 - C.transientBlock A)⁻¹ *ᵥ fun _ => 1 := by
  apply eq_fundamental_mulVec hA hR
  funext y
  have hs := absorbTime_step hA hR y.2
  rw [sum_P_mul_eq A] at hs
  have h2 : ∑ a : {a : S // a ∈ A}, C.P y a * C.absorbTime A a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [absorbTime_of_mem hA a.2, mul_zero]
  rw [h2, add_zero] at hs
  rw [one_sub_transientBlock_mulVec_apply]
  linarith

end Rhone.MarkovChain.FinChain
