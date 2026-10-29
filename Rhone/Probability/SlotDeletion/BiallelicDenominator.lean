/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Assembly
public import Rhone.LinearAlgebra.SlotDeletion.Denom

/-! # DL‑3 — the biallelic denominator law, `⊆` direction -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset Matrix LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section PhiZero

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable {q : Config 2 2 → F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem Phi_zero_zero (hq : IsSolution θA θB ρ πA πB q) (t : ℕ) : Phi q πA πB 0 0 t = 1 := by
  have hxi : ∀ (α : Fin 0 → Fin 2) (β : Fin 0 → Fin 2), xi (canM 0 0 t) α β = 0 := by
    intro α β
    refine Config.ext (funext fun i => ?_) (funext fun j => ?_)
      (funext fun i => funext fun j => ?_) <;>
      simp [xi_a, xi_b, xi_c, freeA, freeB]
  rw [Phi, Q]
  simp only [hxi, hq.empty, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  simp

end PhiZero

section Edge

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem phi_A_rec (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) {i : ℕ} (hi : 2 ≤ i) :
    (((i - 1 : ℕ) : F) + θA) * Phi q πA πB i 0 0
      = ((i - 1 : ℕ) : F)
        * (kap πA * Phi q πA πB (i - 2) 0 0 + gam πA * Phi q πA πB (i - 1) 0 0) := by
  have h := dgQ_mul_Phi_sub_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i 0 0 (by omega) le_rfl
  have hd : dgQ θA θB ρ i 0 0 = (i : F) * (((i - 1 : ℕ) : F) + θA) := by
    rw [dgQ]
    simp only [Nat.add_zero, Nat.sub_zero, Nat.cast_zero, Nat.cast_mul]
    ring
  have hR : phiRecursionSource q πA πB i 0 0
      = (i : F) * ((i - 1 : ℕ) : F)
        * (kap πA * Phi q πA πB (i - 2) 0 0 + gam πA * Phi q πA πB (i - 1) 0 0) := by
    rw [phiRecursionSource]
    simp only [Nat.sub_zero, Nat.add_zero, Nat.mul_zero, Nat.zero_mul, Nat.cast_zero,
      Nat.cast_mul]
    ring
  rw [hd, hR] at h
  simp only [Nat.sub_zero, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, sub_zero] at h
  have hi0 : ((i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine mul_left_cancel₀ hi0 ?_
  linear_combination h

theorem phi_B_rec (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) {j : ℕ} (hj : 2 ≤ j) :
    (((j - 1 : ℕ) : F) + θB) * Phi q πA πB 0 j 0
      = ((j - 1 : ℕ) : F)
        * (kap πB * Phi q πA πB 0 (j - 2) 0 + gam πB * Phi q πA πB 0 (j - 1) 0) := by
  have h := dgQ_mul_Phi_sub_eq_phiRecursionSource hθA hθB hρ hq hπA hπB 0 j 0 le_rfl (by omega)
  have hd : dgQ θA θB ρ 0 j 0 = (j : F) * (((j - 1 : ℕ) : F) + θB) := by
    rw [dgQ]
    simp only [Nat.zero_add, Nat.sub_zero, Nat.cast_zero, Nat.cast_mul]
    ring
  have hR : phiRecursionSource q πA πB 0 j 0
      = (j : F) * ((j - 1 : ℕ) : F)
        * (kap πB * Phi q πA πB 0 (j - 2) 0 + gam πB * Phi q πA πB 0 (j - 1) 0) := by
    rw [phiRecursionSource]
    simp only [Nat.sub_zero, Nat.add_zero, Nat.mul_zero, Nat.zero_mul, Nat.cast_zero,
      Nat.cast_mul]
    ring
  rw [hd, hR] at h
  simp only [Nat.sub_zero, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, sub_zero] at h
  have hj0 : ((j : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine mul_left_cancel₀ hj0 ?_
  linear_combination h

end Edge

section Witness

variable {F : Type*} [Field F] {θA θB ρ : F} (A : Subring F)

theorem poch_dvd_mem (haA : θA ∈ A) {m n : ℕ} (h : m ≤ n) :
    ∃ c ∈ A, LinearAlgebra.SlotDeletion.poch θA n = LinearAlgebra.SlotDeletion.poch θA m * c := by
  obtain ⟨c, hc⟩ := LinearAlgebra.SlotDeletion.poch_dvd (⟨θA, haA⟩ : A) h
  refine ⟨(c : F), c.2, ?_⟩
  have h2 := congrArg (A.subtype) hc
  rwa [map_mul, LinearAlgebra.SlotDeletion.poch_map, LinearAlgebra.SlotDeletion.poch_map] at h2

theorem Dfull_dvd_Dfull_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    {i' j' i j : ℕ} (hi' : i' ≤ i) (hj' : j' ≤ j) :
    ∃ c ∈ A, LinearAlgebra.SlotDeletion.Dfull θA θB ρ i j = LinearAlgebra.SlotDeletion.Dfull θA θB ρ
        i' j' * c := by
  obtain ⟨c, hc⟩ := LinearAlgebra.SlotDeletion.Dfull_dvd_Dfull (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩
      hi' hj'
  refine ⟨(c : F), c.2, ?_⟩
  have h2 := congrArg (A.subtype) hc
  rwa [map_mul, LinearAlgebra.SlotDeletion.Dfull_map, LinearAlgebra.SlotDeletion.Dfull_map] at h2

theorem Dfull_dvd_Dcut_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    {i' j' i j : ℕ} (hi' : i' ≤ i) (hj' : j' ≤ j) (hne : i' < i ∨ j' < j) (hi : 2 ≤ i) :
    ∃ c ∈ A, LinearAlgebra.SlotDeletion.Dcut θA θB ρ i j = LinearAlgebra.SlotDeletion.Dfull θA θB ρ
        i' j' * c := by
  obtain ⟨c, hc⟩ := LinearAlgebra.SlotDeletion.Dfull_dvd_Dcut (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ hi'
      hj' hne hi
  refine ⟨(c : F), c.2, ?_⟩
  have h2 := congrArg (A.subtype) hc
  rwa [map_mul, LinearAlgebra.SlotDeletion.Dcut_map, LinearAlgebra.SlotDeletion.Dfull_map] at h2

end Witness

section Step1

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (A : Subring F)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem kap_mem (hπ : ∀ i, πA i ∈ A) : kap πA ∈ A := A.mul_mem (hπ 0) (hπ 1)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem gam_mem (hπ : ∀ i, πA i ∈ A) : gam πA ∈ A := A.sub_mem (hπ 1) (hπ 0)

include hθA hθB hρ hq

omit [LinearOrder F] [IsStrictOrderedRing F] hθA hθB hρ hq in
theorem mul_phiRecursionSource_mem {X : F} {i j : ℕ}
    (hcoef : ∀ i' j' s, i' ≤ i → j' ≤ j → (i' < i ∨ j' < j) →
      X * Phi q πA πB i' j' s ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A) (hi : 2 ≤ i) (hj : 2 ≤ j) (t : ℕ) :
    X * phiRecursionSource q πA πB i j t ∈ A := by
  have hn : ∀ m : ℕ, ((m : ℕ) : F) ∈ A := fun m => natCast_mem A m
  have h2 : (2 : F) ∈ A := by
    have h := natCast_mem A 2
    rwa [Nat.cast_ofNat] at h
  have hkA : kap πA ∈ A := kap_mem A hπAm
  have hgA : gam πA ∈ A := gam_mem A hπAm
  have hkB : kap πB ∈ A := kap_mem A hπBm
  have hgB : gam πB ∈ A := gam_mem A hπBm
  have hrw : X * phiRecursionSource q πA πB i j t
      = kap πA * ((((i - t) * (i - t - 1) : ℕ) : F) * (X * Phi q πA πB (i - 2) j t)
          + 2 * (((i - t) * t : ℕ) : F) * (X * Phi q πA πB (i - 2) j (t - 1)))
        + gam πA * (((i - t) * (i + t - 1) : ℕ) : F) * (X * Phi q πA πB (i - 1) j t)
        + kap πB * ((((j - t) * (j - t - 1) : ℕ) : F) * (X * Phi q πA πB i (j - 2) t)
          + 2 * (((j - t) * t : ℕ) : F) * (X * Phi q πA πB i (j - 2) (t - 1)))
        + gam πB * (((j - t) * (j + t - 1) : ℕ) : F) * (X * Phi q πA πB i (j - 1) t)
        + ((t * (t - 1) : ℕ) : F)
            * (kap πA * kap πB * (X * Phi q πA πB (i - 2) (j - 2) (t - 2))
              + kap πA * gam πB * (X * Phi q πA πB (i - 2) (j - 1) (t - 2))
              + gam πA * kap πB * (X * Phi q πA πB (i - 1) (j - 2) (t - 2))
              + gam πA * gam πB * (X * Phi q πA πB (i - 1) (j - 1) (t - 1))) := by
    rw [phiRecursionSource]; ring
  rw [hrw]
  refine A.add_mem (A.add_mem (A.add_mem (A.add_mem ?_ ?_) ?_) ?_) ?_
  · exact A.mul_mem hkA (A.add_mem (A.mul_mem (hn _) (hcoef _ _ _ (by omega) le_rfl
      (Or.inl (by omega)))) (A.mul_mem (A.mul_mem h2 (hn _))
        (hcoef _ _ _ (by omega) le_rfl (Or.inl (by omega)))))
  · exact A.mul_mem (A.mul_mem hgA (hn _))
      (hcoef _ _ _ (by omega) le_rfl (Or.inl (by omega)))
  · exact A.mul_mem hkB (A.add_mem (A.mul_mem (hn _) (hcoef _ _ _ le_rfl (by omega)
      (Or.inr (by omega)))) (A.mul_mem (A.mul_mem h2 (hn _))
        (hcoef _ _ _ le_rfl (by omega) (Or.inr (by omega)))))
  · exact A.mul_mem (A.mul_mem hgB (hn _))
      (hcoef _ _ _ le_rfl (by omega) (Or.inr (by omega)))
  · refine A.mul_mem (hn _) (A.add_mem (A.add_mem (A.add_mem ?_ ?_) ?_) ?_)
    · exact A.mul_mem (A.mul_mem hkA hkB)
        (hcoef _ _ _ (by omega) (by omega) (Or.inl (by omega)))
    · exact A.mul_mem (A.mul_mem hkA hgB)
        (hcoef _ _ _ (by omega) (by omega) (Or.inl (by omega)))
    · exact A.mul_mem (A.mul_mem hgA hkB)
        (hcoef _ _ _ (by omega) (by omega) (Or.inl (by omega)))
    · exact A.mul_mem (A.mul_mem hgA hgB)
        (hcoef _ _ _ (by omega) (by omega) (Or.inl (by omega)))

omit [LinearOrder F] [IsStrictOrderedRing F] hθA hθB hρ hq in
theorem adjugate_T_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A) (i j : ℕ)
    (s s' : Fin (min i j + 1)) : adjugate (LinearAlgebra.Tridiag.T F i j θA θB ρ) s s' ∈ A := by
  have hT : (LinearAlgebra.Tridiag.T A i j ⟨θA, haA⟩ ⟨θB, haB⟩ ⟨ρ, haρ⟩).map A.subtype
      = LinearAlgebra.Tridiag.T F i j θA θB ρ := LinearAlgebra.Tridiag.T_map A.subtype i j _ _ _
  have hadj := RingHom.map_adjugate A.subtype
    (LinearAlgebra.Tridiag.T A i j ⟨θA, haA⟩ ⟨θB, haB⟩ ⟨ρ, haρ⟩)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hT] at hadj
  rw [← hadj]
  exact (adjugate (LinearAlgebra.Tridiag.T A i j ⟨θA, haA⟩ ⟨θB, haB⟩ ⟨ρ, haρ⟩) s s').2

theorem Dfull_mul_Phi_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    ∀ (n i j : ℕ), i + j ≤ n → ∀ t : ℕ,
      LinearAlgebra.SlotDeletion.Dfull θA θB ρ i j * Phi q πA πB i j t ∈ A := by
  have hn : ∀ m : ℕ, ((m : ℕ) : F) ∈ A := fun m => natCast_mem A m
  have hkA : kap πA ∈ A := kap_mem A hπAm
  have hgA : gam πA ∈ A := gam_mem A hπAm
  have hkB : kap πB ∈ A := kap_mem A hπBm
  have hgB : gam πB ∈ A := gam_mem A hπBm
  have hbase : ∀ t : ℕ, LinearAlgebra.SlotDeletion.Dfull θA θB ρ 0 0 * Phi q πA πB 0 0 t ∈ A := by
    intro t
    rw [Phi_zero_zero hq, LinearAlgebra.SlotDeletion.Dfull, LinearAlgebra.SlotDeletion.poch_zero,
        LinearAlgebra.SlotDeletion.poch_zero, LinearAlgebra.SlotDeletion.Erect_zero_left]
    simp only [mul_one]
    exact A.one_mem
  intro n
  induction n with
  | zero =>
      intro i j hij t
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst hi; subst hj
      exact hbase t
  | succ n ih =>
      intro i j hij t
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i
        · rcases Nat.lt_or_ge j 2 with hj2 | hj2
          · interval_cases j
            · exact hbase t
            · rw [Phi_j_one hθA hθB hρ hq hπA hπB, mul_zero]
              exact A.zero_mem
          · obtain ⟨c, hcA, hc⟩ := poch_dvd_mem A haB (show j - 2 ≤ j - 1 by omega)
            have hmin : min 0 j = 0 := by omega
            have hPt : Phi q πA πB 0 j t = Phi q πA πB 0 j 0 := by
              rw [Phi_of_min_le q πA πB (by omega : min 0 j ≤ t), hmin]
            have hrec := phi_B_rec hθA hθB hρ hq hπA hπB (show 2 ≤ j by omega)
            have hsplit := LinearAlgebra.SlotDeletion.poch_succ_top θB (show 2 ≤ j by omega)
            have hkey : LinearAlgebra.SlotDeletion.Dfull θA θB ρ 0 j * Phi q πA πB 0 j t
                = ((j - 1 : ℕ) : F)
                  * (kap πB * (c *
                      (LinearAlgebra.SlotDeletion.Dfull θA θB ρ 0 (j - 2) * Phi q πA πB 0 (j - 2)
                      0))
                    + gam πB * (LinearAlgebra.SlotDeletion.Dfull θA θB ρ 0 (j - 1) * Phi q πA πB 0
                        (j - 1) 0)) := by
              rw [LinearAlgebra.SlotDeletion.Dfull_i_zero, LinearAlgebra.SlotDeletion.Dfull_i_zero,
                  LinearAlgebra.SlotDeletion.Dfull_i_zero, hPt, hsplit, hc]
              linear_combination (LinearAlgebra.SlotDeletion.poch θB (j - 2) * c) * hrec
            rw [hkey]
            exact A.mul_mem (hn _) (A.add_mem
              (A.mul_mem hkB (A.mul_mem hcA (ih 0 (j - 2) (by omega) 0)))
              (A.mul_mem hgB (ih 0 (j - 1) (by omega) 0)))
        · rw [Phi_i_one hθA hθB hρ hq hπA, mul_zero]
          exact A.zero_mem
      · rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · interval_cases j
          · obtain ⟨c, hcA, hc⟩ := poch_dvd_mem A haA (show i - 2 ≤ i - 1 by omega)
            have hPt : Phi q πA πB i 0 t = Phi q πA πB i 0 0 := by
              rw [Phi_of_min_le q πA πB (by omega : min i 0 ≤ t)]
              simp
            have hrec := phi_A_rec hθA hθB hρ hq hπA hπB (show 2 ≤ i by omega)
            have hsplit := LinearAlgebra.SlotDeletion.poch_succ_top θA (show 2 ≤ i by omega)
            have hkey : LinearAlgebra.SlotDeletion.Dfull θA θB ρ i 0 * Phi q πA πB i 0 t
                = ((i - 1 : ℕ) : F)
                  * (kap πA * (c *
                      (LinearAlgebra.SlotDeletion.Dfull θA θB ρ (i - 2) 0 * Phi q πA πB (i - 2) 0
                      0))
                    + gam πA * (LinearAlgebra.SlotDeletion.Dfull θA θB ρ (i - 1) 0 * Phi q πA πB
                        (i - 1) 0 0)) := by
              rw [LinearAlgebra.SlotDeletion.Dfull_j_zero, LinearAlgebra.SlotDeletion.Dfull_j_zero,
                  LinearAlgebra.SlotDeletion.Dfull_j_zero, hPt, hsplit, hc]
              linear_combination (LinearAlgebra.SlotDeletion.poch θA (i - 2) * c) * hrec
            rw [hkey]
            exact A.mul_mem (hn _) (A.add_mem
              (A.mul_mem hkA (A.mul_mem hcA (ih (i - 2) 0 (by omega) 0)))
              (A.mul_mem hgA (ih (i - 1) 0 (by omega) 0)))
          · rw [Phi_j_one hθA hθB hρ hq hπA hπB, mul_zero]
            exact A.zero_mem
        · have hcoef : ∀ i' j' s, i' ≤ i → j' ≤ j → (i' < i ∨ j' < j) →
              LinearAlgebra.SlotDeletion.Dcut θA θB ρ i j * Phi q πA πB i' j' s ∈ A := by
            intro i' j' s hi' hj' hne
            obtain ⟨c, hcA, hc⟩ := Dfull_dvd_Dcut_mem A haA haB haρ hi' hj' hne (by omega)
            have hrw : LinearAlgebra.SlotDeletion.Dcut θA θB ρ i j * Phi q πA πB i' j' s
                = c * (LinearAlgebra.SlotDeletion.Dfull θA θB ρ i' j' * Phi q πA πB i' j' s) := by
              rw [hc]; ring
            rw [hrw]
            refine A.mul_mem hcA (ih i' j' ?_ s)
            rcases hne with h | h <;> omega
          have hsrc : ∀ s : ℕ, LinearAlgebra.SlotDeletion.Dcut θA θB ρ i j * phiRecursionSource q πA
              πB i j s ∈ A := fun s =>
            mul_phiRecursionSource_mem A hcoef hπAm hπBm (by omega) (by omega) s
          have hmat := T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j
          have h1 : adjugate (LinearAlgebra.Tridiag.T F i j θA θB ρ)
                *ᵥ (LinearAlgebra.Tridiag.T F i j θA θB ρ
                  *ᵥ fun s : Fin (min i j + 1) => Phi q πA πB i j (s : ℕ))
              = adjugate (LinearAlgebra.Tridiag.T F i j θA θB ρ)
                *ᵥ fun s : Fin (min i j + 1) => phiRecursionSource q πA πB i j (s : ℕ) := by
            rw [hmat]
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
            Matrix.one_mulVec] at h1
          have hstep : ∀ s : Fin (min i j + 1),
              LinearAlgebra.SlotDeletion.Dfull θA θB ρ i j * Phi q πA πB i j (s : ℕ) ∈ A := by
            intro s
            have hs := congrFun h1 s
            simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at hs
            have hval : LinearAlgebra.SlotDeletion.Dfull θA θB ρ i j * Phi q πA πB i j (s : ℕ)
                = ∑ s' : Fin (min i j + 1), adjugate (LinearAlgebra.Tridiag.T F i j θA θB ρ) s s'
                    * (LinearAlgebra.SlotDeletion.Dcut θA θB ρ i j * phiRecursionSource q πA πB i j
                        (s' : ℕ)) := by
              rw [← LinearAlgebra.SlotDeletion.Dcut_mul_E θA θB ρ
                  (show 2 ≤ i by omega) (show 2 ≤ j by omega),
                mul_assoc, LinearAlgebra.Tridiag.E, hs, Finset.mul_sum]
              exact Finset.sum_congr rfl fun s' _ => by ring
            rw [hval]
            exact A.sum_mem fun s' _ =>
              A.mul_mem (adjugate_T_mem A haA haB haρ i j s s') (hsrc _)
          rcases Nat.lt_or_ge t (min i j + 1) with hlt | hge
          · exact hstep ⟨t, hlt⟩
          · rw [Phi_of_min_le q πA πB (by omega : min i j ≤ t)]
            exact hstep ⟨min i j, Nat.lt_succ_self _⟩

theorem Dfull_mul_Phi_mem' (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j t : ℕ) :
    LinearAlgebra.SlotDeletion.Dfull θA θB ρ i j * Phi q πA πB i j t ∈ A :=
  Dfull_mul_Phi_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB (i + j) i j le_rfl t

end Step1

section Step2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (A : Subring F)
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
include hθA hθB hρ hq

theorem Dfull_mul_q_xi_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    LinearAlgebra.SlotDeletion.Dfull θA θB ρ (Fintype.card SA) (Fintype.card SB) * q (xi M α β) ∈
        A := by
  rw [q_xi_eq_sum_Phi hθA hθB hρ hq hπA hπB M hM α β, Finset.mul_sum]
  refine A.sum_mem fun S _ => ?_
  rw [Finset.mul_sum]
  refine A.sum_mem fun T _ => ?_
  have hS : S.card ≤ Fintype.card SA := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hT : T.card ≤ Fintype.card SB := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  obtain ⟨c, hcA, hc⟩ := Dfull_dvd_Dfull_mem A haA haB haρ hS hT
  have hrw : LinearAlgebra.SlotDeletion.Dfull θA θB ρ (Fintype.card SA) (Fintype.card SB)
        * (((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
            * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v)))
          * Phi q πA πB S.card T.card (pairsIn M S T).card)
      = (((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
            * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v))) * c)
        * (LinearAlgebra.SlotDeletion.Dfull θA θB ρ S.card T.card * Phi q πA πB S.card T.card
            (pairsIn M S T).card) := by
    rw [hc]; ring
  rw [hrw]
  exact A.mul_mem (A.mul_mem (labelledCoeff_prod_mem A hπAm hπBm S T α β) hcA)
    (Dfull_mul_Phi_mem' hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB _ _ _)

end Step2

end Rhone.Probability.SlotDeletion
