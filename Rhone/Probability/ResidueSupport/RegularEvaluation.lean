/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.SimplePole
public import Rhone.Probability.SamplingUniform.ConstructionMap

/-! # Evaluation of regular rational functions at an arbitrary point -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial Matrix
open Analysis.RareAlleleHierarchy RareAlleleHierarchy SamplingUniform

variable {K : Type*} [Field K]

noncomputable def regularAt (r : K) : Subring (RatFunc K) where
  carrier := {f | f.denom.eval r ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg hz
    have h := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id K) r
      (RatFunc.denom_add_dvd f g) hz
    exact (mul_ne_zero hf hg) (by simpa using h)
  mul_mem' := regular_mul_at r
  neg_mem' := by
    intro f hf
    have hneg : (RatFunc.C (-1 : K)).denom.eval r ≠ 0 := by rw [RatFunc.denom_C]; simp
    simpa using regular_mul_at r hneg hf

noncomputable def valueAt (r : K) : regularAt r →+* K where
  toFun f := RatFunc.eval (RingHom.id K) r f.val
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' f g := RatFunc.eval_add (RingHom.id K) r f.property g.property
  map_mul' f g := RatFunc.eval_mul (RingHom.id K) r f.property g.property

noncomputable def regularPolynomial (r : K) : Polynomial K →+* regularAt r where
  toFun p := ⟨algebraMap _ _ p, by
    change (RatFunc.denom (algebraMap _ _ p)).eval r ≠ 0
    rw [RatFunc.denom_algebraMap]
    simp⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp] theorem coe_regularPolynomial (r : K) (p : Polynomial K) :
    (regularPolynomial r p).val = algebraMap _ (RatFunc K) p := rfl

theorem valueAt_polynomial (r : K) (p : Polynomial K) :
    valueAt r (regularPolynomial r p) = p.eval r := by
  change RatFunc.eval (RingHom.id K) r (algebraMap _ _ p) = _
  rw [RatFunc.eval_algebraMap]
  rfl

noncomputable def scaledRegularFamily (r : K) (f : ℕ → ℕ → ℕ → RatFunc K)
    (hf : ∀ i j t, (RatFunc.denom (algebraMap (Polynomial K) (RatFunc K) (X - C r) *
      f i j t)).eval r ≠ 0) (i j t : ℕ) : regularAt r :=
  ⟨algebraMap _ _ (X - C r) * f i j t, hf i j t⟩

theorem regular_matrix_equation {n : Type*} [Fintype n]
    (r : K) (M : Matrix n n (Polynomial K)) (v s : n → regularAt r)
    (h : (M.map (algebraMap (Polynomial K) (RatFunc K))) *ᵥ (fun t => (v t).val) =
      fun t => (s t).val) :
    (M.map (Polynomial.evalRingHom r)) *ᵥ (fun t => valueAt r (v t)) =
      fun t => valueAt r (s t) := by
  have hlift : (M.map (regularPolynomial r)) *ᵥ v = s := by
    funext t
    apply Subtype.ext
    have hm := (regularAt r).subtype.map_mulVec (M.map (regularPolynomial r)) v t
    exact hm.trans (congrFun h t)
  have hout := congrArg (fun v => fun t => valueAt r (v t)) hlift
  funext t
  have hm := (valueAt r).map_mulVec (M.map (regularPolynomial r)) v t
  have ht := congrFun hout t
  rw [hm] at ht
  simpa only [Matrix.map_map, Function.comp_def, valueAt_polynomial,
    Polynomial.coe_evalRingHom] using ht

end Rhone.Probability.ResidueSupport
