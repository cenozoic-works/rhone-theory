/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.RegularEvaluation

/-! # Taking the simple-pole coefficient through the centred recurrence -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial Matrix Analysis.RareAlleleHierarchy RareAlleleHierarchy SamplingUniform

variable {K : Type*} [Field K]

noncomputable def poleCoefficient (r : K) (f : RatFunc K) : K :=
  RatFunc.eval (RingHom.id K) r (algebraMap (Polynomial K) (RatFunc K) (X - C r) * f)

theorem poleCoefficient_matrix (r a b κA γA κB γB : K)
    (f : ℕ → ℕ → ℕ → RatFunc K)
    (hf : ∀ i j t, (RatFunc.denom (algebraMap (Polynomial K) (RatFunc K) (X - C r) *
      f i j t)).eval r ≠ 0) (i j : ℕ)
    (hrec : LinearAlgebra.Tridiag.T (RatFunc K) i j (RatFunc.C a) (RatFunc.C b) RatFunc.X *ᵥ
        (fun t : Fin (min i j + 1) => f i j t) =
      fun t : Fin (min i j + 1) =>
        recursionSource (RatFunc.C κA) (RatFunc.C γA) (RatFunc.C κB) (RatFunc.C γB) f i j t) :
    LinearAlgebra.Tridiag.T K i j a b r *ᵥ
        (fun t : Fin (min i j + 1) => poleCoefficient r (f i j t)) =
      fun t : Fin (min i j + 1) =>
        recursionSource κA γA κB γB (fun x y u => poleCoefficient r (f x y u)) i j t := by
  let g := scaledRegularFamily r f hf
  let Creg := (regularPolynomial r).comp (Polynomial.C : K →+* Polynomial K)
  let M := LinearAlgebra.Tridiag.T (Polynomial K) i j (C a) (C b) X
  have hscaled : M.map (algebraMap (Polynomial K) (RatFunc K)) *ᵥ
      (fun t : Fin (min i j + 1) => (g i j t).val) =
      fun t : Fin (min i j + 1) =>
        (recursionSource (Creg κA) (Creg γA) (Creg κB) (Creg γB) g i j t).val := by
    have hs := congrArg (fun v : Fin (min i j + 1) → RatFunc K =>
      (algebraMap (Polynomial K) (RatFunc K) (X - C r)) • v) hrec
    rw [← Matrix.mulVec_smul] at hs
    funext t
    have ht := congrFun hs t
    simp only [Pi.smul_apply, smul_eq_mul] at ht
    simp only [M, LinearAlgebra.Tridiag.T_map, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    change _ = (regularAt r).subtype
      (recursionSource (Creg κA) (Creg γA) (Creg κB) (Creg γB) g i j t)
    rw [recursionSource_map]
    simp only [Creg, RingHom.comp_apply, Subring.subtype_apply,
      coe_regularPolynomial, RatFunc.algebraMap_C, g, scaledRegularFamily]
    rw [recursionSource_mul]
    exact ht
  have hout := regular_matrix_equation r M (fun t : Fin (min i j + 1) => g i j t)
    (fun t : Fin (min i j + 1) =>
      recursionSource (Creg κA) (Creg γA) (Creg κB) (Creg γB) g i j t) hscaled
  dsimp only [M] at hout
  rw [LinearAlgebra.Tridiag.T_map] at hout
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X,
    recursionSource_map, Creg, RingHom.comp_apply, valueAt_polynomial] at hout
  exact hout

end Rhone.Probability.ResidueSupport
