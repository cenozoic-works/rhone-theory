/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.Coordinates
public import Rhone.Analysis.DiagonalObstruction.SpectralTransport
public import Rhone.LinearAlgebra.Tridiag.RhoDegree

/-! # Degree estimates for the spectral polynomial of the diagonal chain -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial MvPolynomial LinearAlgebra.Tridiag Algebra.DiagonalObstruction
    Analysis.DiagonalObstruction

theorem coordinates_cont_degree_le (d b c : ℕ → Polynomial (Polynomial ℤ))
    (hd : ∀ t, (coordinates ℤ (d t)).totalDegree ≤ 1)
    (hb : ∀ t, (coordinates ℤ (b t)).totalDegree = 0)
    (hc : ∀ t, (coordinates ℤ (c t)).totalDegree ≤ 1) (n : ℕ) :
    (coordinates ℤ (cont d b c n)).totalDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [cont]
    | 1 => simpa [cont] using hd 0
    | k + 2 =>
      simp only [cont, map_sub, map_mul]
      apply (totalDegree_sub _ _).trans
      apply max_le
      · exact (totalDegree_mul _ _).trans (by
          have := hd (k + 1)
          have := ih (k + 1) (by omega)
          omega)
      · apply (totalDegree_mul _ _).trans
        have hbc := totalDegree_mul (coordinates ℤ (b k)) (coordinates ℤ (c k))
        rw [hb k] at hbc
        have := hc k
        have := ih k (by omega)
        omega

theorem spectral_totalDegree_le (m : ℕ) :
    (coordinates ℤ (spectralPolynomial m)).totalDegree ≤ m + 1 := by
  rw [spectralPolynomial_eq_cont]
  apply coordinates_cont_degree_le
  · intro t
    simp only [map_sub, map_add, map_mul, coordinates_X, coordinates_C_C, coordinates_C_X]
    change (MvPolynomial.X (0 : Fin 2) - (MvPolynomial.C (coalDiag m t) +
      MvPolynomial.X 1 * MvPolynomial.C (t : ℤ))).totalDegree ≤ 1
    apply (totalDegree_sub _ _).trans
    apply max_le
    · simp only [totalDegree_X, le_refl]
    · apply (totalDegree_add _ _).trans
      apply max_le
      · simp only [totalDegree_C, Nat.zero_le]
      · exact (totalDegree_mul _ _).trans (by
          simp only [totalDegree_X, totalDegree_C, Nat.add_zero, le_refl])
  · intro t
    rw [coordinates_C_C]
    exact totalDegree_C _
  · intro t
    rw [Polynomial.C_mul, map_mul, coordinates_C_X, coordinates_C_C]
    exact (totalDegree_mul _ _).trans (by
          simp only [totalDegree_X, totalDegree_C, Nat.add_zero, le_refl])

theorem spectral_totalDegree (m : ℕ) :
    (coordinates ℤ (spectralPolynomial m)).totalDegree = m + 1 := by
  apply le_antisymm (spectral_totalDegree_le m)
  have h := degreeOf_le_totalDegree (coordinates ℤ (spectralPolynomial m)) 0
  rwa [coordinates_spectral_degree, spectralPolynomial_natDegree] at h

theorem spectral_constant_coefficient_degree {m : ℕ} (hm : 2 ≤ m) :
    ((spectralPolynomial m).coeff 0).natDegree = m := by
  have hk : kappaT m m (0 : ℤ) 0 ≠ 0 := by
    have hmz : (2 : ℤ) ≤ m := by exact_mod_cast hm
    unfold kappaT
    simp only [add_zero]
    nlinarith
  have hd := natDegree_E_of_charZero m m (0 : ℤ) 0 hk
  simp only [Nat.min_self, Polynomial.C_0] at hd
  have he : E (Polynomial ℤ) m m 0 0 Polynomial.X ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hd
    omega
  have hv := spectralPolynomial_eval₂_eq_E (by omega : 1 ≤ m)
    (RingHom.id (Polynomial ℤ)) (0 : Polynomial ℤ)
  simp only [neg_zero, zero_mul, Polynomial.eval₂_id, RingHom.id_apply] at hv
  rw [Polynomial.coeff_zero_eq_eval_zero, hv,
    Polynomial.natDegree_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) he]
  simpa [Polynomial.natDegree_pow] using hd

theorem spectral_recombination_degree_ge {m : ℕ} (hm : 2 ≤ m) :
    m ≤ (coordinates ℤ (spectralPolynomial m)).degreeOf 1 := by
  have h := coordinates_coefficient_degree_le ℤ (spectralPolynomial m) 0
  rwa [spectral_constant_coefficient_degree hm] at h

theorem spectral_factor_degree_transfer {m : ℕ} (hm : 2 ≤ m)
    {F : Polynomial (Polynomial ℤ)} (hF : F ∣ spectralPolynomial m) :
    F.natDegree ≤ (coordinates ℤ F).degreeOf 1 + 1 := by
  have hP : coordinates ℤ (spectralPolynomial m) ≠ 0 := by
    simpa only [map_zero] using
      (coordinates ℤ).injective.ne (spectralPolynomial_monic m).ne_zero
  have hd := factor_degree_transfer (0 : Fin 2) 1 1 hP
    (map_dvd (coordinates ℤ).toRingHom hF)
    (by rw [spectral_totalDegree]; have := spectral_recombination_degree_ge hm; omega)
  change (coordinates ℤ F).degreeOf 0 ≤ (coordinates ℤ F).degreeOf 1 + 1 at hd
  rwa [coordinates_spectral_degree] at hd

end Rhone.Probability.RecombinationDegree
