/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FundamentalMatrix
public import Rhone.MarkovChain.ClosedSet

/-! # The fundamental matrix for a closed set of a finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open Finset Matrix

variable {S : Type*} [Fintype S] [DecidableEq S] {C : FinChain S} {A : Finset S}

theorem IsClosedSet.isUnit_one_sub_transientBlock (hA : C.IsClosedSet A) (hR : C.Reaches A) :
    IsUnit (1 - C.transientBlock A) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv0
  have hzero := hA.eq_zero_of_harmonicOff hR (g := extendZero v) (fun x hx => by
      rw [expect_apply, sum_P_mul_extendZero]
      have : v ⟨x, hx⟩ - ∑ z : Transient A, C.P x z * v z = 0 :=
        (one_sub_transientBlock_mulVec_apply v ⟨x, hx⟩).symm.trans (congrFun hv ⟨x, hx⟩)
      rw [extendZero_of_not_mem v ⟨x, hx⟩]
      linarith) fun a ha => extendZero_of_mem v ha
  funext x
  have := congrFun hzero x.1
  rwa [extendZero_of_not_mem v x] at this

theorem IsClosedSet.eq_fundamental_mulVec (hA : C.IsClosedSet A) (hR : C.Reaches A)
    {u w : Transient A → ℝ} (h : (1 - C.transientBlock A) *ᵥ u = w) :
    u = (1 - C.transientBlock A)⁻¹ *ᵥ w := by
  have hu := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 (hA.isUnit_one_sub_transientBlock hR))
  rw [← h, mulVec_mulVec, hu, one_mulVec]

theorem IsClosedSet.potential_eq_fundamental_mulVec (hA : C.IsClosedSet A) (hR : C.Reaches A)
    (c : S → ℝ) :
    (fun x : Transient A => C.potential A c x) =
      (1 - C.transientBlock A)⁻¹ *ᵥ fun x : Transient A => c x := by
  apply hA.eq_fundamental_mulVec hR
  funext y
  have hs := hA.potential_step hR c y.1
  simp only [y.2, ↓reduceIte] at hs
  rw [sum_P_mul_eq A] at hs
  have h2 : ∑ a : {a : S // a ∈ A}, C.P y a * C.potential A c a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hA.potential_of_mem a.2, mul_zero]
  rw [h2, add_zero] at hs
  rw [one_sub_transientBlock_mulVec_apply]
  linarith

theorem IsClosedSet.absorbTime_eq_fundamental_mulVec (hA : C.IsClosedSet A) (hR : C.Reaches A) :
    (fun x : Transient A => C.absorbTime A x) = (1 - C.transientBlock A)⁻¹ *ᵥ fun _ => 1 := by
  rw [absorbTime_eq_potential]
  exact hA.potential_eq_fundamental_mulVec hR fun _ => 1

theorem IsClosedSet.fundamental_apply (hA : C.IsClosedSet A) (hR : C.Reaches A)
    (x y : Transient A) :
    (1 - C.transientBlock A)⁻¹ x y = C.potential A (fun z => if z = y.1 then 1 else 0) x := by
  have h := congrFun (hA.potential_eq_fundamental_mulVec hR
    (fun z => if z = y.1 then (1 : ℝ) else 0)) x
  have hsingle : (fun z : Transient A => if z.1 = y.1 then (1 : ℝ) else 0) = Pi.single y 1 := by
    funext z
    by_cases hz : z = y
    · subst hz
      simp
    · have hz' : z.1 ≠ y.1 := fun h => hz (Subtype.ext h)
      simp [hz, hz']
  rw [h, hsingle, mulVec_single_one]
  rfl

theorem IsClosedSet.fundamental_nonneg (hA : C.IsClosedSet A) (hR : C.Reaches A)
    (x y : Transient A) : 0 ≤ (1 - C.transientBlock A)⁻¹ x y := by
  rw [hA.fundamental_apply hR]
  exact C.potential_nonneg A (fun z => by split_ifs <;> norm_num) x

theorem IsClosedSet.one_le_fundamental_self (hA : C.IsClosedSet A) (hR : C.Reaches A)
    (x : Transient A) : 1 ≤ (1 - C.transientBlock A)⁻¹ x x := by
  rw [hA.fundamental_apply hR, hA.potential_step hR]
  simp only [x.2, ↓reduceIte]
  have hnn : 0 ≤ ∑ y, C.P x.1 y * C.potential A (fun z => if z = x.1 then (1 : ℝ) else 0) y :=
    Finset.sum_nonneg fun y _ => mul_nonneg (C.nonneg _ _)
      (C.potential_nonneg A (fun z => by split_ifs <;> norm_num) y)
  linarith

end Rhone.MarkovChain.FinChain
