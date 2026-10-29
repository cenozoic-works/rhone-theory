/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.Positivity
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Nonnegative-coefficient polynomial classes for continuants and entries of `E` -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open LinearAlgebra.Tridiag LinearAlgebra.RecombinationExpansion

abbrev PolZ : Type := MvPolynomial (Fin 3) ℤ

noncomputable def thA : PolZ := MvPolynomial.X 0

noncomputable def thB : PolZ := MvPolynomial.X 1

noncomputable def rho : PolZ := MvPolynomial.X 2

noncomputable def NN : Subsemiring PolZ :=
  (MvPolynomial.map (Nat.castRingHom ℤ)).rangeS

theorem coeff_nonneg_of_mem_NN {p : PolZ} (hp : p ∈ NN) (m : Fin 3 →₀ ℕ) :
    0 ≤ p.coeff m := by
  obtain ⟨q, rfl⟩ := RingHom.mem_rangeS.1 hp
  rw [MvPolynomial.coeff_map]
  exact Int.natCast_nonneg _

theorem thA_mem_NN : thA ∈ NN := ⟨MvPolynomial.X 0, MvPolynomial.map_X _ _⟩

theorem thB_mem_NN : thB ∈ NN := ⟨MvPolynomial.X 1, MvPolynomial.map_X _ _⟩

theorem rho_mem_NN : rho ∈ NN := ⟨MvPolynomial.X 2, MvPolynomial.map_X _ _⟩

section Generic

variable {S : Type*} [CommRing S] (A : Subsemiring S) {θA θB ρ : S}

theorem cont_mem (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) (i j : ℕ) {k : ℕ}
    (hk : k ≤ min i j + 1) :
    cont (dcoef S i j θA θB ρ) (bcoef S i j) (ccoef S ρ) k ∈ A := by
  match k with
  | 0 =>
    change (1 : S) ∈ A
    exact A.one_mem
  | (r + 1) =>
    rw [← (PH_eq_cont i j θA θB ρ r (by omega)).1]
    exact (PH_mem A i j hA hB hρ r).1

theorem Qc_mem (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) (i j : ℕ) {s : ℕ}
    (hs : s ≤ min i j + 1) :
    Qc (dcoef S i j θA θB ρ) (bcoef S i j) (ccoef S ρ) (min i j + 1) s ∈ A := by
  have h := (QN_mem A i j (min i j) hA hB hρ (min i j + 1 - s)).1
  rw [(QN_eq_Qc i j (min i j) (min_le_left i j) (min_le_right i j) θA θB ρ
    (min i j + 1 - s) (by omega)).1] at h
  rwa [show min i j + 1 - (min i j + 1 - s) = s from by omega] at h

theorem E_mem (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) (i j : ℕ) :
    E S i j θA θB ρ ∈ A := by
  rw [E_eq_cont]
  exact cont_mem A hA hB hρ i j (le_refl _)

theorem usmaniEntry_mem (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) (i j : ℕ) {t t' : ℕ}
    (ht : t ≤ min i j) (ht' : t' ≤ min i j) :
    usmaniEntry (dcoef S i j θA θB ρ) (bcoef S i j) (ccoef S ρ) (min i j + 1) t t' ∈ A := by
  have htwo : (2 : S) ∈ A := by
    have h := natCast_mem A 2
    simp only [Nat.cast_ofNat] at h
    exact h
  rcases Nat.le_total t t' with h | h
  · rw [usmaniEntry_T_of_le i j θA θB ρ h]
    exact A.mul_mem (A.mul_mem (A.mul_mem (A.pow_mem htwo _)
        (A.prod_mem fun s _ => natCast_mem A _))
      (cont_mem A hA hB hρ i j (by omega))) (Qc_mem A hA hB hρ i j (by omega))
  · rw [usmaniEntry_T_of_ge i j θA θB ρ h]
    exact A.mul_mem (A.mul_mem (A.mul_mem (A.pow_mem hρ _)
        (A.prod_mem fun s _ => A.add_mem (natCast_mem A s) A.one_mem))
      (cont_mem A hA hB hρ i j (by omega))) (Qc_mem A hA hB hρ i j (by omega))

end Generic

theorem cont_mem_NN (i j : ℕ) {k : ℕ} (hk : k ≤ min i j + 1) :
    cont (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) k ∈ NN :=
  cont_mem NN thA_mem_NN thB_mem_NN rho_mem_NN i j hk

theorem Qc_mem_NN (i j : ℕ) {s : ℕ} (hs : s ≤ min i j + 1) :
    Qc (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) (min i j + 1) s ∈ NN :=
  Qc_mem NN thA_mem_NN thB_mem_NN rho_mem_NN i j hs

theorem E_mem_NN (i j : ℕ) : E PolZ i j thA thB rho ∈ NN :=
  E_mem NN thA_mem_NN thB_mem_NN rho_mem_NN i j

theorem usmaniEntry_mem_NN (i j : ℕ) {t t' : ℕ} (ht : t ≤ min i j) (ht' : t' ≤ min i j) :
    usmaniEntry (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho)
      (min i j + 1) t t' ∈ NN :=
  usmaniEntry_mem NN thA_mem_NN thB_mem_NN rho_mem_NN i j ht ht'

theorem usmaniEntry_coeff_nonneg (i j : ℕ) {t t' : ℕ} (ht : t ≤ min i j) (ht' : t' ≤ min i j)
    (m : Fin 3 →₀ ℕ) :
    0 ≤ (usmaniEntry (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho)
        (min i j + 1) t t').coeff m :=
  coeff_nonneg_of_mem_NN (usmaniEntry_mem_NN i j ht ht') m

theorem cont_coeff_nonneg (i j : ℕ) {k : ℕ} (hk : k ≤ min i j + 1) (m : Fin 3 →₀ ℕ) :
    0 ≤ (cont (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) k).coeff m :=
  coeff_nonneg_of_mem_NN (cont_mem_NN i j hk) m

theorem Qc_coeff_nonneg (i j : ℕ) {s : ℕ} (hs : s ≤ min i j + 1) (m : Fin 3 →₀ ℕ) :
    0 ≤ (Qc (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho)
        (min i j + 1) s).coeff m :=
  coeff_nonneg_of_mem_NN (Qc_mem_NN i j hs) m

theorem prod_sub_pos {i j t t' : ℕ} (ht' : t' ≤ min i j) :
    0 < 2 ^ (t' - t) * ∏ s ∈ Finset.Ico t t', ((i - s) * (j - s)) := by
  refine Nat.mul_pos (Nat.two_pow_pos _) (Finset.prod_pos fun s hs => ?_)
  rw [Finset.mem_Ico] at hs
  exact Nat.mul_pos (by omega) (by omega)

theorem prod_succ_pos {t t' : ℕ} : 0 < ∏ s ∈ Finset.Ico t' t, (s + 1) :=
  Finset.prod_pos fun s _ => Nat.succ_pos s

theorem usmaniEntry_upper_form (i j : ℕ) {t t' : ℕ} (ht' : t' ≤ min i j) (h : t ≤ t') :
    ∃ (c : ℕ) (N : PolZ), 0 < c ∧ N ∈ NN ∧
      usmaniEntry (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho)
          (min i j + 1) t t' = (c : PolZ) * N := by
  refine ⟨2 ^ (t' - t) * ∏ s ∈ Finset.Ico t t', ((i - s) * (j - s)),
    cont (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) t
      * Qc (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) (min i j + 1) (t' + 1),
    prod_sub_pos ht',
    NN.mul_mem (cont_mem_NN i j (by omega)) (Qc_mem_NN i j (by omega)), ?_⟩
  rw [usmaniEntry_T_of_le i j thA thB rho h]
  push_cast
  ring

theorem usmaniEntry_lower_form (i j : ℕ) {t t' : ℕ} (ht : t ≤ min i j) (h : t' ≤ t) :
    ∃ (c : ℕ) (N : PolZ), 0 < c ∧ N ∈ NN ∧
      usmaniEntry (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho)
          (min i j + 1) t t' = rho ^ (t - t') * (c : PolZ) * N := by
  refine ⟨∏ s ∈ Finset.Ico t' t, (s + 1),
    cont (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) t'
      * Qc (dcoef PolZ i j thA thB rho) (bcoef PolZ i j) (ccoef PolZ rho) (min i j + 1) (t + 1),
    prod_succ_pos,
    NN.mul_mem (cont_mem_NN i j (by omega)) (Qc_mem_NN i j (by omega)), ?_⟩
  rw [usmaniEntry_T_of_ge i j thA thB rho h]
  push_cast
  ring

section Ordered

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] {θA θB ρ : R}

theorem mem_nonneg_iff (x : R) : x ∈ Subsemiring.nonneg R ↔ 0 ≤ x :=
  Subsemiring.mem_nonneg

theorem cont_nonneg (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ) {k : ℕ}
    (hk : k ≤ min i j + 1) :
    0 ≤ cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) k :=
  cont_mem (Subsemiring.nonneg R) hA hB hρ i j hk

theorem Qc_nonneg (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ) {s : ℕ}
    (hs : s ≤ min i j + 1) :
    0 ≤ Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) s :=
  Qc_mem (Subsemiring.nonneg R) hA hB hρ i j hs

theorem E_nonneg (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ) :
    0 ≤ E R i j θA θB ρ :=
  E_mem (Subsemiring.nonneg R) hA hB hρ i j

theorem usmaniEntry_nonneg (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ) {t t' : ℕ}
    (ht : t ≤ min i j) (ht' : t' ≤ min i j) :
    0 ≤ usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) t t' :=
  usmaniEntry_mem (Subsemiring.nonneg R) hA hB hρ i j ht ht'

end Ordered

theorem inv_T_nonneg {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ)
    (hE : 0 < E F i j θA θB ρ) (t t' : Fin (min i j + 1)) :
    0 ≤ (T F i j θA θB ρ)⁻¹ t t' := by
  have hc : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (min i j + 1) ≠ 0 := by
    rw [← E_eq_cont]; exact ne_of_gt hE
  rw [T_eq_trid, inv_trid _ _ _ _ hc, Matrix.smul_apply, usmani_apply, smul_eq_mul]
  refine mul_nonneg (le_of_lt (inv_pos.2 ?_)) ?_
  · rw [← E_eq_cont]; exact hE
  · exact usmaniEntry_nonneg hA hB hρ i j (Nat.lt_succ_iff.1 t.isLt) (Nat.lt_succ_iff.1 t'.isLt)

end Rhone.Analysis.RecombinationExpansion
