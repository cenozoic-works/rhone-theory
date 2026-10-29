/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.DiagonalLimit

/-! # The residue of the concrete hierarchy is the diagonal chain -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Matrix Analysis.RareAlleleHierarchy RareAlleleHierarchy DiagonalChain
    LinearAlgebra.SlotDeletion SlotDeletion

variable {K : Type*} [Field K] [CharZero K]

noncomputable def regularTheta (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  ⟨lambdaTheta θ ρ i j t, (lambdaTheta_regular_zero θ ρ hE i j t).1⟩

@[simp] theorem coe_regularTheta (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) : (regularTheta θ ρ hE i j t : RatFunc K) = lambdaTheta θ ρ i j t := rfl

@[simp] theorem residue_regularTheta (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) : Algebra.SamplingUniform.residueAtZero (regularTheta θ ρ hE i j t) =
      RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ i j t) := rfl

noncomputable def regularReducedSource (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  (((i - t) * (i + t - 1) : ℕ) : Algebra.SamplingUniform.RegularAtZero K) * regularTheta θ ρ hE
      (i - 1) j t +
    (((j - t) * (j + t - 1) : ℕ) : Algebra.SamplingUniform.RegularAtZero K) * regularTheta θ ρ hE i
        (j - 1) t +
    ((t * (t - 1) : ℕ) : Algebra.SamplingUniform.RegularAtZero K) * regularTheta θ ρ hE (i - 1)
        (j - 1) (t - 1)

@[simp] theorem coe_regularReducedSource (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    (i j t : ℕ) : (regularReducedSource θ ρ hE i j t : RatFunc K) =
      redSource (alphaSeq Algebra.SamplingUniform.lambdaA)
          (alphaSeq (Algebra.SamplingUniform.lambdaB θ)) (lambdaPhi θ ρ) i j t := rfl

theorem regularTheta_diagonal_system (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    (LinearAlgebra.Tridiag.T K k k θ 0 ρ).map Algebra.SamplingUniform.regularC *ᵥ
        (fun t : Fin (min k k + 1) => regularTheta θ ρ hE k k t) =
      fun t : Fin (min k k + 1) => regularReducedSource θ ρ hE k k t := by
  have hsys := lambdaTheta_system θ ρ hE hk hk
  rw [Algebra.SamplingUniform.lambdaBlock_diagonal] at hsys
  funext t
  apply Subtype.ext
  change (Algebra.SamplingUniform.regularAtZero K).subtype
    (((LinearAlgebra.Tridiag.T K k k θ 0 ρ).map Algebra.SamplingUniform.regularC *ᵥ
      (fun t : Fin (min k k + 1) => regularTheta θ ρ hE k k t)) t) = _
  rw [(Algebra.SamplingUniform.regularAtZero K).subtype.map_mulVec, coe_regularReducedSource]
  exact congrFun hsys t

theorem lambdaTheta_residue_system (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    LinearAlgebra.Tridiag.T K k k θ 0 ρ *ᵥ
        (fun t : Fin (min k k + 1) => RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ k k t)) =
      fun t : Fin (min k k + 1) => ((t * (t - 1) : ℕ) : K) *
        RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ (k - 1) (k - 1) (t - 1)) := by
  funext t
  have hrow := congrArg Algebra.SamplingUniform.residueAtZero
      (congrFun (regularTheta_diagonal_system θ ρ hE hk) t)
  rw [Algebra.SamplingUniform.residueAtZero.map_mulVec,
      Algebra.SamplingUniform.constant_regular_matrix_residue] at hrow
  change (LinearAlgebra.Tridiag.T K k k θ 0 ρ *ᵥ
    (fun s : Fin (min k k + 1) => RatFunc.eval (RingHom.id K) 0
      (lambdaTheta θ ρ k k s))) t = _ at hrow
  have hleft := (lambdaTheta_regular_zero θ ρ hE (k - 1) k t).2 (by omega)
  have hright := (lambdaTheta_regular_zero θ ρ hE k (k - 1) t).2 (by omega)
  simpa only [regularReducedSource, map_add, map_mul, map_natCast, residue_regularTheta,
    hleft, hright, mul_zero, zero_add] using hrow

noncomputable def residueChain (θ ρ : K) (k t : ℕ) : K :=
  if k = 1 then varthetaOne t else RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ k k t)

omit [CharZero K] in
@[simp] theorem residueChain_one (θ ρ : K) (t : ℕ) : residueChain θ ρ 1 t = varthetaOne t := by
  simp [residueChain]

omit [CharZero K] in
theorem residueChain_eq (θ ρ : K) {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    residueChain θ ρ k t = RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ k k t) := by
  simp only [residueChain, ite_eq_right (by omega : k ≠ 1)]

theorem residueChain_source (θ ρ : K) {k t : ℕ} (hk : 2 ≤ k) (ht : t ≤ k) :
    ((t * (t - 1) : ℕ) : K) *
        RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ (k - 1) (k - 1) (t - 1)) =
      diagSource (residueChain θ ρ (k - 1)) t := by
  by_cases hk2 : k = 2
  · subst k
    interval_cases t <;> simp [diagSource, residueChain, varthetaOne, lambdaTheta]
  · rw [diagSource, residueChain_eq θ ρ (by omega : 2 ≤ k - 1)]

theorem residueChain_isDiagChain (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0) :
    IsDiagChain θ ρ (residueChain θ ρ) := by
  refine ⟨residueChain_one θ ρ, ?_⟩
  intro k hk t ht
  have hrow := congrFun (lambdaTheta_residue_system θ ρ hE hk)
    (⟨t, by simpa using Nat.lt_succ_of_le ht⟩ : Fin (min k k + 1))
  rw [T_mulVec_apply k k θ 0 ρ
    (fun s => RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ k k s))] at hrow
  rw [residueChain_source θ ρ hk ht] at hrow
  simp only [residueChain_eq θ ρ hk]
  convert hrow using 1
  simp only [Analysis.DenominatorEquation.dcoefS, LinearAlgebra.Tridiag.dcoef, zero_mul, add_zero]
  ring

theorem lambdaTheta_residue_cleared (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    {k t : ℕ} (hk : 2 ≤ k) (ht : t ≤ k) :
    frakE k θ ρ * RatFunc.eval (RingHom.id K) 0 (lambdaTheta θ ρ k k t) =
      clearedChain θ ρ k t := by
  rw [← residueChain_eq θ ρ hk]
  exact (clearedChain_eq_frakE_mul θ ρ (residueChain_isDiagChain θ ρ hE) k
    (by omega) t ht).symm

theorem lambdaPhi_cf11_residue (θ ρ : K) (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    frakE k θ ρ * RatFunc.eval (RingHom.id K) 0 (cf 1 1 (lambdaPhi θ ρ k k 0)) =
      W k θ ρ := by
  have h := lambdaTheta_residue_cleared θ ρ hE hk (Nat.zero_le k)
  simpa only [lambdaTheta, Theta_eq_cf11 _ _ _ hk hk, W] using h

end Rhone.Probability.SamplingUniform
