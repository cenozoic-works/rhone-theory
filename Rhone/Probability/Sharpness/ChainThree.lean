/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Sharpness.Specialization
public import Rhone.Probability.DiagonalChain.Small
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Unconditional diagonal-chain coprimality at level three -/

@[expose] public section

namespace Rhone.Probability.Sharpness
open Polynomial DiagonalChain LinearAlgebra.Tridiag

theorem ED_three_eq {S : Type*} [CommRing S] (θ ρ : S) :
    ED 3 θ ρ = (18 * θ + 72) * ρ ^ 3
      + (99 * θ ^ 2 + 1062 * θ + 2664) * ρ ^ 2
      + (162 * θ ^ 3 + 2754 * θ ^ 2 + 14436 * θ + 23184) * ρ
      + (81 * θ ^ 4 + 1836 * θ ^ 3 + 14148 * θ ^ 2 + 43200 * θ + 43200) := by
  rw [ED, E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef, LinearAlgebra.Tridiag.bcoef,
      LinearAlgebra.Tridiag.ccoef]
  ring

theorem chain_three_at_zero_isCoprime :
    IsCoprime (W 3 (0 : Polynomial ℚ) X) (ED 3 (0 : Polynomial ℚ) X) := by
  let u : Polynomial ℚ := C (1 / 859963392)
  let p : Polynomial ℚ := 72 * X ^ 2 + 2232 * X + 9792
  have hid : p * W 3 (0 : Polynomial ℚ) X - 55296 * ED 3 (0 : Polynomial ℚ) X
      = 859963392 := by
    rw [W_three_at_zero, ED_three_at_zero]
    dsimp [p]
    ring
  refine ⟨u * p, u * (-55296), ?_⟩
  calc (u * p) * W 3 (0 : Polynomial ℚ) X +
        (u * (-55296)) * ED 3 (0 : Polynomial ℚ) X
      = u * (p * W 3 (0 : Polynomial ℚ) X - 55296 * ED 3 (0 : Polynomial ℚ) X) := by ring
    _ = u * 859963392 := by rw [hid]
    _ = 1 := by
      dsimp [u]
      have h : (C (1 / 859963392) : Polynomial ℚ) * C (859963392 : ℚ) = C (1 : ℚ) := by
        rw [← map_mul]
        norm_num
      simpa only [Polynomial.C_ofNat, Polynomial.C_1] using h

noncomputable def chainWThree : Polynomial (Polynomial ℚ) := W 3 (C X) X

noncomputable def chainEThree : Polynomial (Polynomial ℚ) := ED 3 (C X) X

theorem natDegree_chainWThree : chainWThree.natDegree = 1 := by
  unfold chainWThree
  rw [W_three]
  compute_degree!
  intro h
  have hh := congrArg (eval (0 : ℚ)) h
  norm_num at hh

theorem natDegree_chainEThree : chainEThree.natDegree = 3 := by
  unfold chainEThree
  rw [ED_three_eq]
  compute_degree!
  intro h
  have hh := congrArg (eval (0 : ℚ)) h
  norm_num at hh

theorem chain_three_isCoprime_map {K : Type*} [Field K]
    (ι : Polynomial ℚ →+* K) (hι : Function.Injective ι) :
    IsCoprime (chainWThree.map ι) (chainEThree.map ι) := by
  let s : Polynomial ℚ →+* ℚ := evalRingHom 0
  have hw : chainWThree.map s = W 3 (0 : Polynomial ℚ) X := by
    change (mapRingHom s) (W 3 (C X) X) = _
    rw [W_map]
    simp [s]
  have he : chainEThree.map s = ED 3 (0 : Polynomial ℚ) X := by
    change (mapRingHom s) (ED 3 (C X) X) = _
    rw [ED_map]
    simp [s]
  apply Algebra.Sharpness.isCoprime_map_of_specialization ι s hι chainWThree chainEThree
  · rw [hw, natDegree_chainWThree, W_three_at_zero]
    compute_degree!
  · rw [he, natDegree_chainEThree, ED_three_at_zero]
    compute_degree!
  · rw [hw, he]
    exact chain_three_at_zero_isCoprime

theorem chain_three_isCoprime :
    IsCoprime
      (W 3 (C (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) X)) X)
      (ED 3 (C (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) X)) X) := by
  have h := chain_three_isCoprime_map
    (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
    (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  change IsCoprime
    ((mapRingHom (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
      (W 3 (C X) X))
    ((mapRingHom (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
      (ED 3 (C X) X)) at h
  rw [W_map, ED_map] at h
  simpa using h

end Rhone.Probability.Sharpness
