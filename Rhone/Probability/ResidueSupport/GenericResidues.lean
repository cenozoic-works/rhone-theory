/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.ResidueRecurrence
public import Rhone.Probability.ResidueSupport.Propagation

/-! # The generic sampling hierarchy in a root field -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial Matrix Analysis.GenericCoordinates LinearAlgebra.SlotDeletion SlotDeletion
open SamplingUniform Analysis.RareAlleleHierarchy RareAlleleHierarchy

variable {L : Type*} [Field L]

noncomputable def toExtension (φ : CanonicalField →+* L) :
    Polynomial CanonicalField →+* RatFunc L :=
  (algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom φ)

@[simp] theorem toExtension_C (φ : CanonicalField →+* L) (a : CanonicalField) :
    toExtension φ (C a) = RatFunc.C (φ a) := by
  simp only [toExtension, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_C, RatFunc.algebraMap_C]

@[simp] theorem toExtension_X (φ : CanonicalField →+* L) :
    toExtension φ X = RatFunc.X := by
  simp only [toExtension, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, RatFunc.algebraMap_X]

theorem extension_Dfull_ne_zero (φ : CanonicalField →+* L) (i j : ℕ) :
    Dfull (toExtension φ (C canonicalThetaA)) (toExtension φ (C canonicalThetaB))
      (toExtension φ X) i j ≠ 0 := by
  rw [← Dfull_map]
  have hinj : Function.Injective (toExtension φ) :=
    (RatFunc.algebraMap_injective L).comp (Polynomial.map_injective φ φ.injective)
  have h := hinj.ne (denominator_ne_zero i j)
  rw [map_zero] at h
  exact h

theorem frequencyNumerator_extension (φ : CanonicalField →+* L) (i j t : ℕ) :
    MvPolynomial.map (toExtension φ) (frequencyNumerator i j t) =
      clearedPhi (MvPolynomial.C (toExtension φ (C canonicalThetaA)))
        (MvPolynomial.C (toExtension φ (C canonicalThetaB)))
        (MvPolynomial.C (toExtension φ X)) kapX gamX kapY gamY i j t := by
  have hD : ∀ a b, Dfull
      (MvPolynomial.C (σ := Fin 2) (toExtension φ (C canonicalThetaA)))
      (MvPolynomial.C (toExtension φ (C canonicalThetaB)))
      (MvPolynomial.C (toExtension φ X)) a b ≠ 0 := by
    intro a b
    rw [← Dfull_map]
    exact MvPolynomial.C_ne_zero.mpr (extension_Dfull_ne_zero φ a b)
  have h := clearedPhi_map (MvPolynomial.map (toExtension φ))
    (MvPolynomial.C (C canonicalThetaA)) (MvPolynomial.C (C canonicalThetaB))
    (MvPolynomial.C X) kapX gamX kapY gamY (by simpa using hD) i j t
  simpa [frequencyNumerator, kapX, gamX, kapY, gamY] using h

noncomputable def scalarHierarchy (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    (i j t : ℕ) : RatFunc L :=
  MvPolynomial.eval (fun x => RatFunc.C (freq x))
    (genericPhi (toExtension φ (C canonicalThetaA)) (toExtension φ (C canonicalThetaB))
      (toExtension φ X) i j t)

noncomputable def scalarNumerator (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    (i j t : ℕ) : Polynomial L :=
  MvPolynomial.eval (fun x => C (freq x))
    (MvPolynomial.map (Polynomial.mapRingHom φ) (frequencyNumerator i j t))

theorem scalarNumerator_map (φ : CanonicalField →+* L) (freq : Fin 2 → L) (i j t : ℕ) :
    algebraMap (Polynomial L) (RatFunc L) (scalarNumerator φ freq i j t) =
      MvPolynomial.eval (fun x => RatFunc.C (freq x))
        (clearedPhi (MvPolynomial.C (toExtension φ (C canonicalThetaA)))
          (MvPolynomial.C (toExtension φ (C canonicalThetaB)))
          (MvPolynomial.C (toExtension φ X)) kapX gamX kapY gamY i j t) := by
  rw [← frequencyNumerator_extension]
  have h := MvPolynomial.map_eval (algebraMap (Polynomial L) (RatFunc L))
    (fun x => C (freq x))
    (MvPolynomial.map (Polynomial.mapRingHom φ) (frequencyNumerator i j t))
  simpa only [scalarNumerator, MvPolynomial.map_map, Function.comp_def,
    RatFunc.algebraMap_C, toExtension] using h

theorem scalarHierarchy_fraction (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    (i j t : ℕ) :
    scalarHierarchy φ freq i j t =
      algebraMap (Polynomial L) (RatFunc L) (scalarNumerator φ freq i j t) /
        algebraMap (Polynomial L) (RatFunc L) ((denominator i j).map φ) := by
  rw [scalarHierarchy, genericPhi, map_mul, MvPolynomial.eval_C,
    ← scalarNumerator_map, ← Dfull_map]
  change (toExtension φ (denominator i j))⁻¹ * _ = _ / toExtension φ (denominator i j)
  rw [div_eq_mul_inv, mul_comm]

theorem scalarHierarchy_scaled_regular (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    (r : L) (i j t : ℕ) :
    (RatFunc.denom (algebraMap (Polynomial L) (RatFunc L) (X - C r) *
      scalarHierarchy φ freq i j t)).eval r ≠ 0 := by
  rw [scalarHierarchy_fraction]
  exact scaled_fraction_regular r _ _ (denominator_separable i j).map

theorem scalarHierarchy_matrix (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.T (RatFunc L) i j (RatFunc.C (φ canonicalThetaA))
        (RatFunc.C (φ canonicalThetaB)) RatFunc.X *ᵥ
        (fun t : Fin (min i j + 1) => scalarHierarchy φ freq i j t) =
      fun t : Fin (min i j + 1) => recursionSource
        (RatFunc.C (freq 0 - freq 0 ^ 2)) (RatFunc.C (1 - 2 * freq 0))
        (RatFunc.C (freq 1 - freq 1 ^ 2)) (RatFunc.C (1 - 2 * freq 1))
        (scalarHierarchy φ freq) i j t := by
  let ev := MvPolynomial.eval (fun x => RatFunc.C (freq x))
  have h := genericPhi_matrix (toExtension φ (C canonicalThetaA))
    (toExtension φ (C canonicalThetaB)) (toExtension φ X)
    (extension_Dfull_ne_zero φ) hi hj
  funext t
  have ht := congrArg ev (congrFun h t)
  rw [ev.map_mulVec, LinearAlgebra.Tridiag.T_map, recursionSource_map] at ht
  change _ = recursionSource
    (RatFunc.C (freq 0 - freq 0 ^ 2)) (RatFunc.C (1 - 2 * freq 0))
    (RatFunc.C (freq 1 - freq 1 ^ 2)) (RatFunc.C (1 - 2 * freq 1))
    (fun x y u => scalarHierarchy φ freq x y u) i j t
  simpa [ev, scalarHierarchy, kapX, gamX, kapY, gamY, map_ofNat, Function.comp_def] using ht

theorem scalarResidue_matrix (φ : CanonicalField →+* L) (freq : Fin 2 → L)
    (r : L) {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.T L i j (φ canonicalThetaA) (φ canonicalThetaB) r *ᵥ
        (fun t : Fin (min i j + 1) => poleCoefficient r (scalarHierarchy φ freq i j t)) =
      fun t : Fin (min i j + 1) => recursionSource
        (freq 0 - freq 0 ^ 2) (1 - 2 * freq 0)
        (freq 1 - freq 1 ^ 2) (1 - 2 * freq 1)
        (fun x y u => poleCoefficient r (scalarHierarchy φ freq x y u)) i j t :=
  poleCoefficient_matrix r _ _ _ _ _ _ (scalarHierarchy φ freq)
    (scalarHierarchy_scaled_regular φ freq r) i j (scalarHierarchy_matrix φ freq hi hj)

theorem scalarResidue_off (φ : CanonicalField →+* L) (freq : Fin 2 → L) (r : L)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hroot : (block p q).eval₂ φ r = 0) :
    ∀ i j t, ¬ (p ≤ i ∧ q ≤ j) → poleCoefficient r (scalarHierarchy φ freq i j t) = 0 := by
  intro i j t hoff
  apply scaled_value_zero
  rw [scalarHierarchy_fraction]
  intro hz
  have hd := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id L) r
    (RatFunc.denom_div_dvd (scalarNumerator φ freq i j t) ((denominator i j).map φ)) hz
  apply denominator_eval_ne_zero φ r hp hq hoff hroot
  simpa only [Polynomial.eval₂_id, Polynomial.eval_map] using hd

theorem source_base_zero_of_off (κA γA κB γB : L) (f : ℕ → ℕ → ℕ → L)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hoff : ∀ i j t, ¬ (p ≤ i ∧ q ≤ j) → f i j t = 0) (t : ℕ) :
    recursionSource κA γA κB γB f p q t = 0 := by
  have h20 u := hoff (p - 2) q u (by omega)
  have h10 u := hoff (p - 1) q u (by omega)
  have h02 u := hoff p (q - 2) u (by omega)
  have h01 u := hoff p (q - 1) u (by omega)
  have h22 u := hoff (p - 2) (q - 2) u (by omega)
  have h21 u := hoff (p - 2) (q - 1) u (by omega)
  have h12 u := hoff (p - 1) (q - 2) u (by omega)
  have h11 u := hoff (p - 1) (q - 1) u (by omega)
  simp only [recursionSource, h20, h10, h02, h01, h22, h21, h12, h11, mul_zero, add_zero]

theorem scalarResidue_kernel (φ : CanonicalField →+* L) (freq : Fin 2 → L) (r : L)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hroot : (block p q).eval₂ φ r = 0) :
    LinearAlgebra.Tridiag.T L p q (φ canonicalThetaA) (φ canonicalThetaB) r *ᵥ
      (fun t : Fin (min p q + 1) => poleCoefficient r (scalarHierarchy φ freq p q t)) = 0 := by
  rw [scalarResidue_matrix φ freq r hp hq]
  funext t
  exact source_base_zero_of_off _ _ _ _ _ hp hq (scalarResidue_off φ freq r hp hq hroot) t

theorem scalarResidue_propagates (φ : CanonicalField →+* L) (freq : Fin 2 → L) (r : L)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hroot : (block p q).eval₂ φ r = 0) :
    ∀ i j t, t ≤ min i j → poleCoefficient r (scalarHierarchy φ freq i j t) =
      Propagation.w (φ canonicalThetaA) (φ canonicalThetaB) r
        (freq 0 - freq 0 ^ 2) (1 - 2 * freq 0) (freq 1 - freq 1 ^ 2) (1 - 2 * freq 1)
        p q (fun u => poleCoefficient r (scalarHierarchy φ freq p q u)) i j t := by
  have hE : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) →
      LinearAlgebra.Tridiag.E L i j (φ canonicalThetaA) (φ canonicalThetaB) r ≠ 0 := by
    intro i j hi hj hne
    exact other_block_ne_zero φ r hp hq (by omega) (by omega) hne hroot
  have hbase : ∀ t, t ≤ min p q → poleCoefficient r (scalarHierarchy φ freq p q t) =
      (1 : L) * poleCoefficient r (scalarHierarchy φ freq p q t) := by simp
  have hrec : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) →
      LinearAlgebra.Tridiag.T L i j (φ canonicalThetaA) (φ canonicalThetaB) r *ᵥ
        (fun t : Fin (min i j + 1) => poleCoefficient r (scalarHierarchy φ freq i j t)) =
      fun t : Fin (min i j + 1) => Propagation.src
        (freq 0 - freq 0 ^ 2) (1 - 2 * freq 0) (freq 1 - freq 1 ^ 2) (1 - 2 * freq 1)
        (fun x y u => poleCoefficient r (scalarHierarchy φ freq x y u)) i j t := by
    intro i j hi hj _
    exact scalarResidue_matrix φ freq r (by omega) (by omega)
  have h := Propagation.res_eq_smul_w hp hq hE
    (scalarResidue_off φ freq r hp hq hroot) hbase hrec
  simpa only [one_mul] using h

end Rhone.Probability.ResidueSupport
