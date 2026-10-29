/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

/-! # Rational functions regular at zero: the subring, residue map, and matrix solutions -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Polynomial Matrix

variable {K : Type*} [Field K]

private theorem eval_ne_zero_of_dvd {p q : K[X]} (hpq : p ∣ q)
    (hq : q.eval 0 ≠ 0) : p.eval 0 ≠ 0 := by
  intro hp
  exact hq (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id K) 0 hpq hp)

theorem regular_mul {f g : RatFunc K}
    (hf : f.denom.eval 0 ≠ 0) (hg : g.denom.eval 0 ≠ 0) :
    (f * g).denom.eval 0 ≠ 0 := by
  apply eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd f g)
  simpa only [Polynomial.eval_mul] using mul_ne_zero hf hg

noncomputable def regularAtZero (K : Type*) [Field K] : Subring (RatFunc K) where
  carrier := {f | f.denom.eval 0 ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg
    apply eval_ne_zero_of_dvd (RatFunc.denom_add_dvd f g)
    simpa only [Polynomial.eval_mul] using mul_ne_zero hf hg
  mul_mem' := regular_mul
  neg_mem' := by
    intro f hf
    have hneg : (RatFunc.C (-1 : K)).denom.eval 0 ≠ 0 := by
      rw [RatFunc.denom_C]
      simp
    simpa using regular_mul hneg hf

abbrev RegularAtZero (K : Type*) [Field K] := ↥(regularAtZero K)

noncomputable def residueAtZero : RegularAtZero K →+* K where
  toFun f := RatFunc.eval (RingHom.id K) 0 f.val
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' f g := RatFunc.eval_add (RingHom.id K) 0 f.property g.property
  map_mul' f g := RatFunc.eval_mul (RingHom.id K) 0 f.property g.property

noncomputable def regularC : K →+* RegularAtZero K where
  toFun c := ⟨RatFunc.C c, by simp [regularAtZero]⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

noncomputable def regularZ : RegularAtZero K := ⟨RatFunc.X, by simp [regularAtZero]⟩

@[simp] theorem coe_regularC (c : K) : (regularC c : RatFunc K) = RatFunc.C c := rfl
@[simp] theorem coe_regularZ : (regularZ (K := K) : RatFunc K) = RatFunc.X := rfl
@[simp] theorem residue_regularC (c : K) : residueAtZero (regularC c) = c := by
  simp [residueAtZero, regularC]
@[simp] theorem residue_regularZ : residueAtZero (regularZ : RegularAtZero K) = 0 := by
  simp [residueAtZero, regularZ]

noncomputable def regularInv (f : RegularAtZero K) (hf : residueAtZero f ≠ 0) :
    RegularAtZero K :=
  ⟨f.val⁻¹, by
    have hfn : f.val ≠ 0 := by
      intro h
      apply hf
      simp [residueAtZero, h]
    have hnum : f.val.num.eval 0 ≠ 0 := by
      intro h
      apply hf
      change f.val.num.eval 0 / f.val.denom.eval 0 = 0
      rw [h, zero_div]
    exact eval_ne_zero_of_dvd (RatFunc.denom_inv_dvd hfn) hnum⟩

@[simp] theorem coe_regularInv (f : RegularAtZero K) (hf : residueAtZero f ≠ 0) :
    (regularInv f hf : RatFunc K) = (f : RatFunc K)⁻¹ := rfl

theorem isUnit_regularAtZero_iff (f : RegularAtZero K) :
    IsUnit f ↔ residueAtZero f ≠ 0 := by
  constructor
  · intro hf
    exact (hf.map residueAtZero).ne_zero
  · intro hf
    have hfn : f.val ≠ 0 := by
      intro h
      apply hf
      simp [residueAtZero, h]
    apply isUnit_iff_exists_inv.mpr
    refine ⟨regularInv f hf, ?_⟩
    ext
    exact mul_inv_cancel₀ hfn

@[simp] theorem residue_regularInv (f : RegularAtZero K) (hf : residueAtZero f ≠ 0) :
    residueAtZero (regularInv f hf) = (residueAtZero f)⁻¹ := by
  have hmul : f * regularInv f hf = 1 := by
    ext
    apply mul_inv_cancel₀
    intro h
    apply hf
    simp [residueAtZero, h]
  have hr := congrArg residueAtZero hmul
  rw [map_mul, map_one] at hr
  exact eq_inv_of_mul_eq_one_right hr

@[simp] theorem mem_regularAtZero (f : RatFunc K) :
    f ∈ regularAtZero K ↔ f.denom.eval 0 ≠ 0 := Iff.rfl

@[simp] theorem C_mem_regularAtZero (c : K) : RatFunc.C c ∈ regularAtZero K := by
  change (RatFunc.C c).denom.eval 0 ≠ 0
  rw [RatFunc.denom_C]
  simp

@[simp] theorem X_mem_regularAtZero : (RatFunc.X : RatFunc K) ∈ regularAtZero K := by
  simp [regularAtZero]

theorem inv_mem_regularAtZero {f : RatFunc K} (hf : f ∈ regularAtZero K)
    (hres : RatFunc.eval (RingHom.id K) 0 f ≠ 0) : f⁻¹ ∈ regularAtZero K :=
  (regularInv ⟨f, hf⟩ hres).property

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem map_matrix_inverse_of_unit_det {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Matrix n n R) (hM : IsUnit M.det) :
    M⁻¹.map φ = (M.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  have h := congrArg φ.mapMatrix (Matrix.mul_nonsing_inv M hM)
  simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h

theorem regular_matrix_unit_det (M : Matrix n n (RegularAtZero K))
    (hM : (M.map residueAtZero).det ≠ 0) : IsUnit M.det := by
  apply (isUnit_regularAtZero_iff _).mpr
  rwa [RingHom.map_det]

theorem coe_regular_matrix_inverse (M : Matrix n n (RegularAtZero K))
    (hM : (M.map residueAtZero).det ≠ 0) :
    M⁻¹.map (regularAtZero K).subtype = (M.map (regularAtZero K).subtype)⁻¹ :=
  map_matrix_inverse_of_unit_det _ M (regular_matrix_unit_det M hM)

theorem residue_regular_matrix_inverse (M : Matrix n n (RegularAtZero K))
    (hM : (M.map residueAtZero).det ≠ 0) :
    M⁻¹.map residueAtZero = (M.map residueAtZero)⁻¹ :=
  map_matrix_inverse_of_unit_det _ M (regular_matrix_unit_det M hM)

theorem solution_of_regular_matrix (M : Matrix n n (RegularAtZero K))
    (s : n → RegularAtZero K) (v : n → RatFunc K)
    (hM : (M.map residueAtZero).det ≠ 0)
    (hv : (M.map (regularAtZero K).subtype) *ᵥ v = fun i => (s i : RatFunc K)) :
    v = fun i => ((M⁻¹ *ᵥ s) i : RatFunc K) := by
  have hunit : IsUnit (M.map (regularAtZero K).subtype).det := by
    have h := (regular_matrix_unit_det M hM).map (regularAtZero K).subtype
    rwa [RingHom.map_det] at h
  let := Matrix.invertibleOfIsUnitDet _ hunit
  have h := Matrix.inv_mulVec_eq_vec hv.symm
  rw [← coe_regular_matrix_inverse M hM] at h
  symm
  calc
    (fun i => ((M⁻¹ *ᵥ s) i : RatFunc K)) =
        M⁻¹.map (regularAtZero K).subtype *ᵥ (fun i => (s i : RatFunc K)) := by
          ext i
          exact (regularAtZero K).subtype.map_mulVec _ _ i
    _ = v := h

theorem solution_mem_regularAtZero (M : Matrix n n (RegularAtZero K))
    (s : n → RegularAtZero K) (v : n → RatFunc K)
    (hM : (M.map residueAtZero).det ≠ 0)
    (hv : (M.map (regularAtZero K).subtype) *ᵥ v = fun i => (s i : RatFunc K))
    (i : n) : v i ∈ regularAtZero K := by
  rw [solution_of_regular_matrix M s v hM hv]
  exact ((M⁻¹ *ᵥ s) i).property

theorem residue_regular_matrix_solution (M : Matrix n n (RegularAtZero K))
    (s : n → RegularAtZero K) (hM : (M.map residueAtZero).det ≠ 0) :
    (fun i => residueAtZero ((M⁻¹ *ᵥ s) i)) =
      (M.map residueAtZero)⁻¹ *ᵥ (fun i => residueAtZero (s i)) := by
  rw [← residue_regular_matrix_inverse M hM]
  ext i
  exact residueAtZero.map_mulVec _ _ i

noncomputable def scaledRegularMatrix (c : K) (A : Matrix n n (RegularAtZero K)) :
    Matrix n n (RegularAtZero K) := regularC c • 1 + (regularZ : RegularAtZero K) • A

omit [Fintype n] in
@[simp] theorem residue_scaledRegularMatrix (c : K) (A : Matrix n n (RegularAtZero K)) :
    (scaledRegularMatrix c A).map residueAtZero = c • (1 : Matrix n n K) := by
  ext i j
  by_cases hij : i = j <;>
    simp [scaledRegularMatrix, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, hij]

theorem scaledRegularMatrix_residue_det_ne_zero {c : K} (hc : c ≠ 0)
    (A : Matrix n n (RegularAtZero K)) :
    ((scaledRegularMatrix c A).map residueAtZero).det ≠ 0 := by
  rw [residue_scaledRegularMatrix, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ hc

theorem residue_scaledRegularMatrix_inverse {c : K} (hc : c ≠ 0)
    (A : Matrix n n (RegularAtZero K)) :
    (scaledRegularMatrix c A)⁻¹.map residueAtZero = c⁻¹ • (1 : Matrix n n K) := by
  rw [residue_regular_matrix_inverse _ (scaledRegularMatrix_residue_det_ne_zero hc A),
    residue_scaledRegularMatrix]
  apply Matrix.inv_eq_right_inv
  simp [smul_smul, inv_mul_cancel₀ hc]

noncomputable def poleMatrix (c : K) (A : Matrix n n (RegularAtZero K)) :
    Matrix n n (RatFunc K) :=
  (RatFunc.C c / RatFunc.X) • 1 + A.map (regularAtZero K).subtype

omit [Fintype n] in
theorem poleMatrix_scaled (c : K) (A : Matrix n n (RegularAtZero K)) :
    (RatFunc.X : RatFunc K) • poleMatrix c A =
      (scaledRegularMatrix c A).map (regularAtZero K).subtype := by
  ext i j
  by_cases hij : i = j <;>
    simp [poleMatrix, scaledRegularMatrix, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, hij, mul_add,
      mul_div_cancel₀ (RatFunc.C c) (show (RatFunc.X : RatFunc K) ≠ 0 from RatFunc.X_ne_zero)]

theorem poleMatrix_det_ne_zero {c : K} (hc : c ≠ 0)
    (A : Matrix n n (RegularAtZero K)) : (poleMatrix c A).det ≠ 0 := by
  have hu := regular_matrix_unit_det (scaledRegularMatrix c A)
    (scaledRegularMatrix_residue_det_ne_zero hc A)
  have hmap := (hu.map (regularAtZero K).subtype).ne_zero
  rw [RingHom.map_det] at hmap
  intro hzero
  have hd := congrArg Matrix.det (poleMatrix_scaled c A)
  rw [Matrix.det_smul, hzero, mul_zero] at hd
  exact hmap hd.symm

noncomputable def poleMatrixSolution (c : K) (A : Matrix n n (RegularAtZero K))
    (s : n → RegularAtZero K) : n → RegularAtZero K :=
  (regularZ : RegularAtZero K) • ((scaledRegularMatrix c A)⁻¹ *ᵥ s)

@[simp] theorem residue_poleMatrixSolution (c : K) (A : Matrix n n (RegularAtZero K))
    (s : n → RegularAtZero K) (i : n) :
    residueAtZero (poleMatrixSolution c A s i) = 0 := by
  simp [poleMatrixSolution]

theorem solution_of_poleMatrix {c : K} (hc : c ≠ 0)
    (A : Matrix n n (RegularAtZero K)) (s : n → RegularAtZero K)
    (v : n → RatFunc K)
    (hv : poleMatrix c A *ᵥ v = fun i => (s i : RatFunc K)) :
    v = fun i => (poleMatrixSolution c A s i : RatFunc K) := by
  have hs := congrArg (fun w : n → RatFunc K => (RatFunc.X : RatFunc K) • w) hv
  rw [← Matrix.smul_mulVec, poleMatrix_scaled] at hs
  have hs' : (scaledRegularMatrix c A).map (regularAtZero K).subtype *ᵥ v =
      fun i => ((regularZ * s i : RegularAtZero K) : RatFunc K) := by
    ext i
    simpa only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, coe_regularZ] using congrFun hs i
  rw [solution_of_regular_matrix _ (fun i => regularZ * s i) v
    (scaledRegularMatrix_residue_det_ne_zero hc A) hs']
  change (fun i =>
    (((scaledRegularMatrix c A)⁻¹ *ᵥ ((regularZ : RegularAtZero K) • s)) i : RatFunc K)) = _
  rw [Matrix.mulVec_smul]
  rfl

theorem poleMatrix_solution_regular_zero {c : K} (hc : c ≠ 0)
    (A : Matrix n n (RegularAtZero K)) (s : n → RegularAtZero K)
    (v : n → RatFunc K)
    (hv : poleMatrix c A *ᵥ v = fun i => (s i : RatFunc K)) (i : n) :
    v i ∈ regularAtZero K ∧ RatFunc.eval (RingHom.id K) 0 (v i) = 0 := by
  rw [solution_of_poleMatrix hc A s v hv]
  exact ⟨(poleMatrixSolution c A s i).property, residue_poleMatrixSolution c A s i⟩

omit [Fintype n] [DecidableEq n] in
theorem constant_regular_matrix_residue (A : Matrix n n K) :
    (A.map regularC).map residueAtZero = A := by
  ext i j
  simp

theorem constant_matrix_solution_regular (A : Matrix n n K) (hA : A.det ≠ 0)
    (s : n → RegularAtZero K) (v : n → RatFunc K)
    (hv : (A.map RatFunc.C) *ᵥ v = fun i => (s i : RatFunc K)) (i : n) :
    v i ∈ regularAtZero K := by
  apply solution_mem_regularAtZero (A.map regularC) s v
  · rwa [constant_regular_matrix_residue]
  · change (A.map RatFunc.C) *ᵥ v = fun i => (s i : RatFunc K)
    exact hv

end Matrices

end Rhone.Algebra.SamplingUniform
