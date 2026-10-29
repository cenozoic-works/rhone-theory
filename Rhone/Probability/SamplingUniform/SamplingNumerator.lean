/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.Assembly
public import Rhone.Probability.SamplingUniform.ConstructionMap

/-! # A universal denominator-cleared sampling polynomial -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open Finset Matrix LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear
    LinearAlgebra.SlotDeletion SlotDeletion
open Analysis.RareAlleleHierarchy RareAlleleHierarchy
variable {R : Type*} [CommRing R]

noncomputable def fullRatio (a b ρ : R) (m x y : ℕ) : R :=
  if h : x ≤ m ∧ y ≤ m then
    Classical.choose (Dfull_dvd_Dfull a b ρ h.1 h.2)
  else 0

theorem Dfull_mul_fullRatio (a b ρ : R) (m x y : ℕ) (hx : x ≤ m) (hy : y ≤ m) :
    Dfull a b ρ x y * fullRatio a b ρ m x y = Dfull a b ρ m m := by
  rw [fullRatio, dite_eq_left ⟨hx, hy⟩]
  exact (Classical.choose_spec (Dfull_dvd_Dfull a b ρ hx hy)).symm

noncomputable def samplingNumerator (a b ρ p r : R) (m : ℕ) : R :=
  ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
    p ^ (m - S.card) * r ^ (m - T.card) *
      (fullRatio a b ρ m S.card T.card *
        clearedPhi a b ρ (p - p ^ 2) (1 - 2 * p) (r - r ^ 2) (1 - 2 * r)
          S.card T.card 0)

theorem finset_fin_card_le {m : ℕ} (S : Finset (Fin m)) : S.card ≤ m := by
  simpa using Finset.card_le_card (Finset.subset_univ S)

section Naturality
variable {S : Type*} [CommRing S] [IsDomain S]

theorem fullRatio_map (φ : R →+* S) (a b ρ : R) (m x y : ℕ)
    (hx : x ≤ m) (hy : y ≤ m) (hD : Dfull (φ a) (φ b) (φ ρ) x y ≠ 0) :
    φ (fullRatio a b ρ m x y) = fullRatio (φ a) (φ b) (φ ρ) m x y := by
  apply mul_left_cancel₀ hD
  have h := congrArg φ (Dfull_mul_fullRatio a b ρ m x y hx hy)
  simpa only [map_mul, Dfull_map, Dfull_mul_fullRatio (φ a) (φ b) (φ ρ) m x y hx hy]
    using h

theorem samplingNumerator_map (φ : R →+* S) (a b ρ p r : R)
    (hD : ∀ i j, Dfull (φ a) (φ b) (φ ρ) i j ≠ 0) (m : ℕ) :
    φ (samplingNumerator a b ρ p r m) =
      samplingNumerator (φ a) (φ b) (φ ρ) (φ p) (φ r) m := by
  rw [samplingNumerator, samplingNumerator, map_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro V _
  rw [map_mul, map_mul, map_pow, map_pow, map_mul,
    fullRatio_map φ a b ρ m U.card V.card (finset_fin_card_le U)
      (finset_fin_card_le V) (hD U.card V.card),
    clearedPhi_map φ a b ρ _ _ _ _ hD]
  simp only [map_sub, map_pow, map_one, map_mul, map_ofNat]

end Naturality

section Actual
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ p r : F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ (piOf p) (piOf r) q)
include ha hb hr hq

theorem map_samplingNumerator_eq_Dfull_mul_q (φ : R →+* F) (A B P u v : R)
    (hA : φ A = a) (hB : φ B = b) (hP : φ P = ρ)
    (hu : φ u = p) (hv : φ v = r) (m : ℕ) :
    φ (samplingNumerator A B P u v m) = Dfull a b ρ m m * q (samplingMM m) := by
  have hKA : φ (u - u ^ 2) = kap (piOf p) := by
    simp only [map_sub, map_pow, hu, kap, piOf, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hGA : φ (1 - 2 * u) = gam (piOf p) := by
    simp only [map_sub, map_one, map_mul, map_ofNat, hu, gam, piOf,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hKB : φ (v - v ^ 2) = kap (piOf r) := by
    simp only [map_sub, map_pow, hv, kap, piOf, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hGB : φ (1 - 2 * v) = gam (piOf r) := by
    simp only [map_sub, map_one, map_mul, map_ofNat, hv, gam, piOf,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hclear (S T : Finset (Fin m)) := map_clearedPhi_eq_Dfull_mul_Phi ha hb hr hq
    (piOf_sum p) (piOf_sum r) φ A B P (u - u ^ 2) (1 - 2 * u)
      (v - v ^ 2) (1 - 2 * v) hA hB hP hKA hGA hKB hGB S.card T.card 0
  rw [samplingNumerator, map_sum, q_samplingMM_expansion ha hb hr hq m,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [map_mul, map_pow, hu, hv, hclear]
  have hratio := congrArg φ (Dfull_mul_fullRatio A B P m S.card T.card
    (finset_fin_card_le S) (finset_fin_card_le T))
  simp only [map_mul, Dfull_map, hA, hB, hP] at hratio
  linear_combination p ^ (m - S.card) * r ^ (m - T.card) *
    Phi q (piOf p) (piOf r) S.card T.card 0 * hratio

end Actual

section Generic
variable {K : Type*} [Field K]
open MvPolynomial

theorem generic_samplingNumerator (a b ρ : K)
    (hD : ∀ i j, Dfull a b ρ i j ≠ 0) (m : ℕ) :
    samplingNumerator (C a) (C b) (C ρ) (X 0) (X 1) m =
      C (Dfull a b ρ m m) * genericSample a b ρ m := by
  rw [samplingNumerator, genericSample, assembledSample, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  change X 0 ^ (m - S.card) * X 1 ^ (m - T.card) *
    (fullRatio (C a) (C b) (C ρ) m S.card T.card *
      clearedPhi (C a) (C b) (C ρ) kapX gamX kapY gamY S.card T.card 0) = _
  rw [← genericPhi_clear a b ρ (hD S.card T.card)]
  have hratio := Dfull_mul_fullRatio (R := MvPolynomial (Fin 2) K)
    (C a) (C b) (C ρ) m S.card T.card
    (finset_fin_card_le S) (finset_fin_card_le T)
  rw [← Dfull_map C, ← Dfull_map C] at hratio
  linear_combination X 0 ^ (m - S.card) * X 1 ^ (m - T.card) *
    genericPhi a b ρ S.card T.card 0 * hratio

theorem generic_samplingNumerator_first_mixed [CharZero K] (a b ρ : K)
    (hD : ∀ i j, Dfull a b ρ i j ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    cf 1 1 (samplingNumerator (C a) (C b) (C ρ) (X 0) (X 1) m) =
      Dfull a b ρ m m * cf 1 1 (genericPhi a b ρ m m 0) := by
  rw [generic_samplingNumerator a b ρ hD m, cf_C_mul,
    genericSample_first_mixed a b ρ hD hm]

end Generic
end Rhone.Probability.SamplingUniform
