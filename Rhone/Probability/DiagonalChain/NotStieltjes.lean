/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalChain.Degrees
public import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The diagonal-chain value `ϑ^k_0` is never a Stieltjes function -/

@[expose] public section

namespace Rhone.Probability.DiagonalChain

open Matrix Polynomial LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation
open Analysis.RareAlleleHierarchy RareAlleleHierarchy

section Moments

variable {K : Type*} [Field K]

noncomputable def momentSeries (A B : Polynomial K) : PowerSeries K :=
  (PowerSeries.X : PowerSeries K) ^ (B.natDegree - A.natDegree)
    * ((A.reverse : PowerSeries K) * ((B.reverse : PowerSeries K))⁻¹)

noncomputable def momentAtInfty (A B : Polynomial K) (j : ℕ) : K :=
  PowerSeries.coeff (j + 1) (momentSeries A B)

theorem constantCoeff_reverse_ne_zero {B : Polynomial K} (hB : B ≠ 0) :
    PowerSeries.constantCoeff (B.reverse : PowerSeries K) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    Polynomial.coeff_zero_reverse]
  exact Polynomial.leadingCoeff_ne_zero.2 hB

theorem momentSeries_spec {A B : Polynomial K} (hB : B ≠ 0) :
    (B.reverse : PowerSeries K) * momentSeries A B
      = (PowerSeries.X : PowerSeries K) ^ (B.natDegree - A.natDegree)
        * (A.reverse : PowerSeries K) := by
  have hc := constantCoeff_reverse_ne_zero hB
  rw [momentSeries]
  have hrw : (B.reverse : PowerSeries K) * ((PowerSeries.X : PowerSeries K)
        ^ (B.natDegree - A.natDegree)
        * ((A.reverse : PowerSeries K) * ((B.reverse : PowerSeries K))⁻¹))
      = (PowerSeries.X : PowerSeries K) ^ (B.natDegree - A.natDegree)
        * (A.reverse : PowerSeries K)
        * ((B.reverse : PowerSeries K) * ((B.reverse : PowerSeries K))⁻¹) := by ring
  rw [hrw, PowerSeries.mul_inv_cancel _ hc, mul_one]

theorem momentAtInfty_eq_zero {A B : Polynomial K} {j : ℕ}
    (hj : j + 1 < B.natDegree - A.natDegree) : momentAtInfty A B j = 0 := by
  rw [momentAtInfty, momentSeries]
  exact PowerSeries.X_pow_dvd_iff.1 (dvd_mul_right _ _) (j + 1) hj

theorem momentAtInfty_ne_zero {A B : Polynomial K} (hA : A ≠ 0) (hB : B ≠ 0)
    (hd : A.natDegree < B.natDegree) :
    momentAtInfty A B (B.natDegree - A.natDegree - 1) ≠ 0 := by
  set d := B.natDegree - A.natDegree with hdd
  have hd1 : d - 1 + 1 = d := by omega
  have hstep := PowerSeries.coeff_X_pow_mul
    ((A.reverse : PowerSeries K) * ((B.reverse : PowerSeries K))⁻¹) d 0
  rw [Nat.zero_add] at hstep
  rw [momentAtInfty, hd1, momentSeries, ← hdd, hstep,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv]
  refine mul_ne_zero ?_ (inv_ne_zero (constantCoeff_reverse_ne_zero hB))
  exact constantCoeff_reverse_ne_zero hA

end Moments

section Count

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem frakE_sub_W_natDegree {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    (frakE k (C a) X).natDegree - (W k (C a) X).natDegree = 2 * k - 2 := by
  have h := degInfty_vartheta_zero ha hk
  have hk' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  omega

theorem moments_vanish {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) {j : ℕ} (hj : j + 4 ≤ 2 * k) :
    momentAtInfty (W k (C a) X) (frakE k (C a) X) j = 0 := by
  refine momentAtInfty_eq_zero ?_
  rw [frakE_sub_W_natDegree ha hk]
  omega

theorem moment_two_k_sub_three_ne_zero {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    momentAtInfty (W k (C a) X) (frakE k (C a) X) (2 * k - 3) ≠ 0 := by
  have hgap := frakE_sub_W_natDegree ha hk
  have hlt : (W k (C a) X).natDegree < (frakE k (C a) X).natDegree := by
    have := natDegree_W_add_two_le ha hk
    omega
  have hidx : (frakE k (C a) X).natDegree - (W k (C a) X).natDegree - 1 = 2 * k - 3 := by omega
  have h := momentAtInfty_ne_zero (W_poly_ne_zero ha hk) (frakE_poly_ne_zero ha k) hlt
  rwa [hidx] at h

theorem hankel_one_eq_zero {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    momentAtInfty (W k (C a) X) (frakE k (C a) X) 0 = 0 :=
  moments_vanish ha hk (by omega)

end Count

section Stieltjes

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def IsRatStieltjes (A B : Polynomial K) : Prop :=
  ∃ (n : ℕ) (c x : Fin n → K), (∀ i, 0 ≤ c i) ∧
    A * ∏ i, (X + C (x i))
      = B * ∑ i, C (c i) * ∏ l ∈ Finset.univ.erase i, (X + C (x l))

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cofactor_monic {n : ℕ} (x : Fin n → K) (i : Fin n) :
    (∏ l ∈ Finset.univ.erase i, (X + C (x l))).Monic :=
  monic_prod_of_monic _ _ fun l _ => monic_X_add_C (x l)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cofactor_natDegree {n : ℕ} (x : Fin n → K) (i : Fin n) :
    (∏ l ∈ Finset.univ.erase i, (X + C (x l))).natDegree = n - 1 := by
  rw [Polynomial.natDegree_prod _ _ fun l _ => (monic_X_add_C (x l)).ne_zero]
  rw [Finset.sum_congr rfl fun l _ => natDegree_X_add_C (x l)]
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem prod_root_natDegree {n : ℕ} (x : Fin n → K) :
    (∏ i, (X + C (x i))).natDegree = n := by
  rw [Polynomial.natDegree_prod _ _ fun l _ => (monic_X_add_C (x l)).ne_zero]
  rw [Finset.sum_congr rfl fun l _ => natDegree_X_add_C (x l)]
  simp

theorem not_isRatStieltjes_of_degree {A B : Polynomial K} (hA : A ≠ 0) (hB : B ≠ 0)
    (hd : A.natDegree + 2 ≤ B.natDegree) : ¬ IsRatStieltjes A B := by
  rintro ⟨n, c, x, hc, heq⟩
  set P : Polynomial K := ∏ i, (X + C (x i)) with hP
  set S : Polynomial K := ∑ i, C (c i) * ∏ l ∈ Finset.univ.erase i, (X + C (x l)) with hS
  have hPne : P ≠ 0 := by
    rw [hP]
    exact (monic_prod_of_monic _ _ fun l _ => monic_X_add_C (x l)).ne_zero
  have hPdeg : P.natDegree = n := by rw [hP]; exact prod_root_natDegree x
  have hScoeff : S.coeff (n - 1) = ∑ i, c i := by
    rw [hS, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_C_mul, ← cofactor_natDegree x i,
      (cofactor_monic x i).coeff_natDegree, mul_one]
  have hSle : S.natDegree ≤ n - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq (cofactor_natDegree x i))
  rcases eq_or_ne (∑ i, c i) 0 with hsum | hsum
  · have hci : ∀ i : Fin n, c i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).1 hsum i (Finset.mem_univ i)
    have hS0 : S = 0 := by
      rw [hS]
      exact Finset.sum_eq_zero fun i _ => by rw [hci i, map_zero, zero_mul]
    rw [hS0, mul_zero] at heq
    exact mul_ne_zero hA hPne heq
  · have hS0 : S ≠ 0 := fun h => hsum (by rw [← hScoeff, h, Polynomial.coeff_zero])
    have hSdeg : S.natDegree = n - 1 :=
      le_antisymm hSle (Polynomial.le_natDegree_of_ne_zero (by rw [hScoeff]; exact hsum))
    have hn : 1 ≤ n := by
      by_contra hcon
      obtain rfl : n = 0 := by omega
      exact hS0 (by rw [hS]; simp)
    have hdeg := congrArg Polynomial.natDegree heq
    rw [Polynomial.natDegree_mul hA hPne, Polynomial.natDegree_mul hB hS0,
      hPdeg, hSdeg] at hdeg
    omega

end Stieltjes

section Main

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem not_stieltjes {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    ¬ IsRatStieltjes (W k (C a) X) (frakE k (C a) X) :=
  not_isRatStieltjes_of_degree (W_poly_ne_zero ha hk) (frakE_poly_ne_zero ha k)
    (natDegree_W_add_two_le ha hk)

end Main

section TwoTwo

variable {S : Type*} [CommRing S]

theorem ED_two_eq (θ ρ : S) :
    ED 2 θ ρ = (4 * θ + 8) * ρ ^ 2 + (12 * θ ^ 2 + 76 * θ + 104) * ρ
      + (8 * θ ^ 3 + 80 * θ ^ 2 + 216 * θ + 144) := by
  rw [ED, E, T_two_two_generic, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

def EDeriv (θ ρ : S) : S := 2 * (4 * θ + 8) * ρ + (12 * θ ^ 2 + 76 * θ + 104)

theorem disc_E_two_two (θ : S) :
    (12 * θ ^ 2 + 76 * θ + 104) ^ 2
        - 4 * (4 * θ + 8) * (8 * θ ^ 3 + 80 * θ ^ 2 + 216 * θ + 144)
      = 16 * θ ^ 4 + 288 * θ ^ 3 + 2256 * θ ^ 2 + 6592 * θ + 6208 := by
  ring

end TwoTwo

section TwoTwoOrdered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem disc_E_two_two_pos {θ : F} (hθ : 0 ≤ θ) :
    0 < 16 * θ ^ 4 + 288 * θ ^ 3 + 2256 * θ ^ 2 + 6592 * θ + 6208 := by
  have h4 : (0 : F) ≤ θ ^ 4 := by positivity
  have h3 : (0 : F) ≤ θ ^ 3 := by positivity
  have h2 : (0 : F) ≤ θ ^ 2 := by positivity
  nlinarith

theorem root_neg {θ r : F} (hθ : 0 ≤ θ) (hr : ED 2 θ r = 0) : r < 0 := by
  by_contra hcon
  simp only [not_lt] at hcon
  exact (LinearAlgebra.GaloisDegreeSeven.E_pos (le_refl 2) (le_refl 2) hθ (le_refl (0 : F))
      hcon).ne' hr

theorem EDeriv_add_eq_zero {θ r₁ r₂ : F} (h1 : ED 2 θ r₁ = 0) (h2 : ED 2 θ r₂ = 0)
    (hne : r₁ ≠ r₂) : EDeriv θ r₁ + EDeriv θ r₂ = 0 := by
  rw [ED_two_eq] at h1 h2
  have hsub : (r₁ - r₂) * ((4 * θ + 8) * (r₁ + r₂) + (12 * θ ^ 2 + 76 * θ + 104)) = 0 := by
    linear_combination h1 - h2
  have hkey : (4 * θ + 8) * (r₁ + r₂) + (12 * θ ^ 2 + 76 * θ + 104) = 0 := by
    rcases mul_eq_zero.1 hsub with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  rw [EDeriv, EDeriv]
  linear_combination 2 * hkey

theorem EDeriv_ne_zero {θ r₁ r₂ : F} (hθ : 0 ≤ θ) (h1 : ED 2 θ r₁ = 0) (h2 : ED 2 θ r₂ = 0)
    (hne : r₁ ≠ r₂) : EDeriv θ r₁ ≠ 0 := by
  intro hz
  have hsum := EDeriv_add_eq_zero h1 h2 hne
  rw [hz, zero_add] at hsum
  have hA : (0 : F) < 4 * θ + 8 := by linarith
  have : 2 * (4 * θ + 8) * (r₁ - r₂) = 0 := by
    rw [EDeriv] at hz hsum
    linear_combination hz - hsum
  rcases mul_eq_zero.1 this with h | h
  · linarith [hA, h]
  · exact hne (sub_eq_zero.1 h)

theorem residues_opposite_sign {θ r₁ r₂ : F} (hθ : 0 ≤ θ) (h1 : ED 2 θ r₁ = 0)
    (h2 : ED 2 θ r₂ = 0) (hne : r₁ ≠ r₂) :
    (32 / EDeriv θ r₁) * (32 / EDeriv θ r₂) < 0 := by
  have hsum := EDeriv_add_eq_zero h1 h2 hne
  have hz1 : EDeriv θ r₁ ≠ 0 := EDeriv_ne_zero hθ h1 h2 hne
  have h2eq : EDeriv θ r₂ = -EDeriv θ r₁ := by linarith
  have hne0 : (32 : F) / EDeriv θ r₁ ≠ 0 := div_ne_zero (by norm_num) hz1
  have hsq : 0 < (32 / EDeriv θ r₁) * (32 / EDeriv θ r₁) := mul_self_pos.2 hne0
  rw [h2eq, div_neg]
  have hrw : (32 / EDeriv θ r₁) * -(32 / EDeriv θ r₁)
      = -((32 / EDeriv θ r₁) * (32 / EDeriv θ r₁)) := by ring
  rw [hrw]
  linarith

theorem rho_residues_opposite_sign {θ r₁ r₂ : F} (hθ : 0 ≤ θ) (h1 : ED 2 θ r₁ = 0)
    (h2 : ED 2 θ r₂ = 0) (hne : r₁ ≠ r₂) :
    (r₁ * (32 / EDeriv θ r₁)) * (r₂ * (32 / EDeriv θ r₂)) < 0 := by
  have hr1 := root_neg hθ h1
  have hr2 := root_neg hθ h2
  have hres := residues_opposite_sign hθ h1 h2 hne
  have hrr : 0 < r₁ * r₂ := mul_pos_of_neg_of_neg hr1 hr2
  have hrw : (r₁ * (32 / EDeriv θ r₁)) * (r₂ * (32 / EDeriv θ r₂))
      = (r₁ * r₂) * ((32 / EDeriv θ r₁) * (32 / EDeriv θ r₂)) := by ring
  rw [hrw]
  exact mul_neg_of_pos_of_neg hrr hres

end TwoTwoOrdered

end Rhone.Probability.DiagonalChain
