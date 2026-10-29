/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.MinorSeparation
public import Rhone.Analysis.DenominatorEquation.Criterion

/-! # Rootwise kernel criterion with coprime leading and trailing minors -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial LinearAlgebra.Tridiag Analysis.DenominatorEquation LinearAlgebra.DenominatorEquation

abbrev RatioField := RatFunc (RatFunc ℚ)

def ratioThetaA : RatioField := RatFunc.X

def ratioThetaB : RatioField := RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X

theorem ratio_dcoef_zero_ne_zero (i j t : ℕ) (hi : 1 ≤ i) :
    dcoef RatioField i j ratioThetaA ratioThetaB 0 t ≠ 0 := by
  let S : RatFunc ℚ := (i : RatFunc ℚ) + (j : RatFunc ℚ) * RatFunc.X
  let n : ℕ := (i + j - t) * (i + j - t - 1)
  let P : (RatFunc ℚ)[X] := C (n : RatFunc ℚ) + C S * X
  have he : algebraMap (RatFunc ℚ)[X] RatioField P =
      dcoef RatioField i j ratioThetaA ratioThetaB 0 t := by
    simp only [P, S, n, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_natCast, dcoef, ratioThetaA, ratioThetaB, zero_mul, add_zero]
    ring
  intro hz
  have hp : P = 0 := (RatFunc.algebraMap_injective (RatFunc ℚ)) (by
    rw [he, hz, map_zero])
  have hc := congrArg (fun p : (RatFunc ℚ)[X] => p.coeff 1) hp
  have hs : S = 0 := by simpa [P] using hc
  exact ratio_total_ne_zero i j hi hs

variable {F : Type*} [Field F] (f : RatioField →+* F)

theorem ratio_root_ne_zero (i j : ℕ) (hi : 1 ≤ i) (ρ : F)
    (hE : E F i j (f ratioThetaA) (f ratioThetaB) ρ = 0) : ρ ≠ 0 := by
  apply root_ne_zero i j (f ratioThetaA) (f ratioThetaB) ρ _ hE
  apply Finset.prod_ne_zero_iff.mpr
  intro t _ hz
  apply ratio_dcoef_zero_ne_zero i j t hi
  apply f.injective
  simpa [dcoef] using hz

theorem ratio_Delta_ne_zero (i j : ℕ) (hi : 1 ≤ i) (ρ : F)
    (hE : E F i j (f ratioThetaA) (f ratioThetaB) ρ = 0)
    (t : ℕ) (ht : t ≤ min i j) :
    Delta F i j (f ratioThetaA) (f ratioThetaB) ρ t ≠ 0 := by
  let : CharZero F := charZero_of_injective_ringHom f.injective
  exact Delta_ne_zero i j _ _ ρ (ratio_root_ne_zero f i j hi ρ hE) hE
    (DeltaP_ne_zero_of_Delta_eq_zero_ratio f i j hi ρ) t ht

theorem ratio_DeltaP_ne_zero (i j : ℕ) (hi : 1 ≤ i) (ρ : F)
    (hE : E F i j (f ratioThetaA) (f ratioThetaB) ρ = 0)
    (t : ℕ) (ht : t ≤ min i j) :
    DeltaP F i j (f ratioThetaA) (f ratioThetaB) ρ (t + 1) ≠ 0 := by
  let : CharZero F := charZero_of_injective_ringHom f.injective
  exact DeltaP_ne_zero i j _ _ ρ (ratio_root_ne_zero f i j hi ρ hE) hE
    (DeltaP_ne_zero_of_Delta_eq_zero_ratio f i j hi ρ) ht

theorem ratio_ell_ne_zero (i j : ℕ) (hi : 1 ≤ i) (ρ : F)
    (hE : E F i j (f ratioThetaA) (f ratioThetaB) ρ = 0)
    (t : ℕ) (ht : t ≤ min i j) :
    ell F i j (f ratioThetaA) (f ratioThetaB) ρ t ≠ 0 := by
  let : CharZero F := charZero_of_injective_ringHom f.injective
  exact ell_ne_zero i j _ _ ρ (ratio_root_ne_zero f i j hi ρ hE) hE
    (DeltaP_ne_zero_of_Delta_eq_zero_ratio f i j hi ρ) ht

theorem ratio_residual_criterion (i j : ℕ) (hi : 1 ≤ i) (ρ : F)
    (hE : E F i j (f ratioThetaA) (f ratioThetaB) ρ = 0)
    (Rv : Fin (min i j + 1) → F) (t : Fin (min i j + 1)) :
    (∑ s : Fin (min i j + 1), ell F i j (f ratioThetaA) (f ratioThetaB) ρ s * Rv s) ≠ 0 ↔
      (∑ s, U F i j (f ratioThetaA) (f ratioThetaB) ρ t s * Rv s) ≠ 0 := by
  let : CharZero F := charZero_of_injective_ringHom f.injective
  exact residual_criterion_at_root i j _ _ ρ (ratio_root_ne_zero f i j hi ρ hE) hE
    (DeltaP_ne_zero_of_Delta_eq_zero_ratio f i j hi ρ) Rv t

end Rhone.Probability.ChainDenominator
