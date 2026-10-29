/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.Construction
public import Rhone.Probability.SamplingNumerators.Mapping
public import Rhone.Probability.SamplingNumerators.PhiCleared

/-! # Evaluation of the universal numerator on sampling solutions -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Matrix LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

section Edges

variable {R S : Type*} [CommRing R] [CommRing S]

theorem edgeFactor_map (φ : R →+* S) (a : R) (n : ℕ) :
    φ (edgeFactor a n) = edgeFactor (φ a) n := by
  by_cases hn : 2 ≤ n <;> simp [edgeFactor, hn]

theorem edgeNumerator_map (φ : R →+* S) (a κ γ : R) (n : ℕ) :
    φ (edgeNumerator a κ γ n) = edgeNumerator (φ a) (φ κ) (φ γ) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [edgeNumerator]
  | one => simp [edgeNumerator]
  | more n ih0 ih1 =>
    simp only [edgeNumerator, map_mul, map_add, map_natCast, edgeFactor_map, ih0, ih1]

theorem edgeNumerator_eq_poch_mul (a κ γ : R) (v : ℕ → R)
    (h0 : v 0 = 1) (h1 : v 1 = 0)
    (hr : ∀ n, 2 ≤ n → (a + (n - 1 : ℕ)) * v n =
      (n - 1 : ℕ) * (κ * v (n - 2) + γ * v (n - 1))) (n : ℕ) :
    edgeNumerator a κ γ n = poch a n * v n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [edgeNumerator, h0]
  | one => simp [edgeNumerator, h1]
  | more n ih0 ih1 =>
    have hrec := hr (n + 2) (by omega)
    simp only [Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega] at hrec
    rw [edgeNumerator, ih0, ih1]
    calc
      (n + 1 : ℕ) * (κ * edgeFactor a (n + 1) * (poch a n * v n) +
          γ * (poch a (n + 1) * v (n + 1))) =
          poch a (n + 1) * ((n + 1 : ℕ) * (κ * v n + γ * v (n + 1))) := by
        rw [poch_edgeFactor a (n + 1)]
        simp only [Nat.add_sub_cancel]
        ring
      _ = poch a (n + 1) * ((a + (n + 1 : ℕ)) * v (n + 2)) := by rw [hrec]
      _ = poch a (n + 2) * v (n + 2) := by
        rw [poch_edgeFactor a (n + 2)]
        simp only [edgeFactor, show 2 ≤ n + 2 by omega, ↓reduceIte,
          show n + 2 - 1 = n + 1 by omega]
        ring

end Edges

section Actual

variable {R F : Type*} [CommRing R]
variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ πA πB q)
variable (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)

include ha hb hr hq hπA hπB

theorem edgeNumerator_A_eq_poch_mul_Phi (i t : ℕ) :
    edgeNumerator a (kap πA) (gam πA) i = poch a i * Phi q πA πB i 0 t := by
  have hclamp (i t : ℕ) : Phi q πA πB i 0 t = Phi q πA πB i 0 0 := by
    simpa using Phi_of_min_le q πA πB (i := i) (j := 0) (t := t) (by simp)
  rw [hclamp]
  apply edgeNumerator_eq_poch_mul
  · exact Phi_zero_zero hq 0
  · exact Phi_i_one ha hb hr hq hπA 0 0
  · intro n hn
    simpa only [add_comm] using phi_A_rec ha hb hr hq hπA hπB hn

theorem edgeNumerator_B_eq_poch_mul_Phi (j t : ℕ) :
    edgeNumerator b (kap πB) (gam πB) j = poch b j * Phi q πA πB 0 j t := by
  have hclamp (j t : ℕ) : Phi q πA πB 0 j t = Phi q πA πB 0 j 0 := by
    simpa using Phi_of_min_le q πA πB (i := 0) (j := j) (t := t) (by simp)
  rw [hclamp]
  apply edgeNumerator_eq_poch_mul
  · exact Phi_zero_zero hq 0
  · exact Phi_j_one ha hb hr hq hπA hπB 0 0
  · intro n hn
    simpa only [add_comm] using phi_B_rec ha hb hr hq hπA hπB hn

theorem map_clearedPhi_eq_Dfull_mul_Phi (φ : R →+* F) (A B P KA GA KB GB : R)
    (hA : φ A = a) (hB : φ B = b) (hP : φ P = ρ)
    (hKA : φ KA = kap πA) (hGA : φ GA = gam πA)
    (hKB : φ KB = kap πB) (hGB : φ GB = gam πB) (i j t : ℕ) :
    φ (clearedPhi A B P KA GA KB GB i j t) =
      Dfull a b ρ i j * Phi q πA πB i j t := by
  have main : ∀ n i j, i + j = n → ∀ t,
      φ (clearedPhi A B P KA GA KB GB i j t) =
        Dfull a b ρ i j * Phi q πA πB i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j hij t
      by_cases hj0 : j = 0
      · subst j
        rw [clearedPhi_A, edgeNumerator_map, hA, hKA, hGA, Dfull_j_zero]
        exact edgeNumerator_A_eq_poch_mul_Phi ha hb hr hq hπA hπB i t
      by_cases hi0 : i = 0
      · subst i
        rw [clearedPhi_B, edgeNumerator_map, hB, hKB, hGB, Dfull_i_zero]
        exact edgeNumerator_B_eq_poch_mul_Phi ha hb hr hq hπA hπB j t
      by_cases hi1 : i = 1
      · subst i
        rw [clearedPhi_one_left, map_zero, Phi_i_one ha hb hr hq hπA, mul_zero]
      by_cases hj1 : j = 1
      · subst j
        rw [clearedPhi_one_right, map_zero, Phi_j_one ha hb hr hq hπA hπB, mul_zero]
      have hi : 2 ≤ i := by omega
      have hj : 2 ≤ j := by omega
      let V : ℕ → ℕ → ℕ → R := fun x y u =>
        cutRatio A B P i j x y * clearedPhi A B P KA GA KB GB x y u
      have hlower (x y u : ℕ) (hx : x ≤ i) (hy : y ≤ j) (hs : x + y < i + j) :
          φ (V x y u) = Dcut a b ρ i j * Phi q πA πB x y u := by
        have hrq := congrArg φ (Dfull_mul_cutRatio A B P hx hy (by omega) hi)
        simp only [map_mul, Dfull_map, Dcut_map, hA, hB, hP] at hrq
        change φ (cutRatio A B P i j x y * clearedPhi A B P KA GA KB GB x y u) = _
        rw [map_mul, ih (x + y) (by omega) x y rfl u]
        calc
          φ (cutRatio A B P i j x y) *
              (Dfull a b ρ x y * Phi q πA πB x y u) =
              (Dfull a b ρ x y * φ (cutRatio A B P i j x y)) *
                Phi q πA πB x y u := by ring
          _ = _ := by rw [hrq]
      have hsource (s : Fin (min i j + 1)) :
          φ (RareAlleleHierarchy.recursionSource KA GA KB GB V i j s) =
            Dcut a b ρ i j * phiRecursionSource q πA πB i j s := by
        rw [recursionSource_map, hKA, hGA, hKB, hGB]
        rw [recursionSource_congr_lower (kap πA) (gam πA) (kap πB) (gam πB) hi hj hlower]
        rw [recursionSource_mul, RareAlleleHierarchy.recursionSource_eq_phiRecursionSource]
      have hlevel : Phi q πA πB i j (blockLevel i j t) = Phi q πA πB i j t := by
        change Phi q πA πB i j (min t (min i j)) = _
        by_cases ht : t ≤ min i j
        · rw [min_eq_left ht]
        · rw [min_eq_right (by omega : min i j ≤ t)]
          exact (Phi_of_min_le q πA πB (by omega : min i j ≤ t)).symm
      rw [clearedPhi_interior A B P KA GA KB GB hi hj]
      change φ (((Analysis.DenominatorEquation.U R i j A B P) *ᵥ
        (fun s : Fin (min i j + 1) => RareAlleleHierarchy.recursionSource KA GA KB GB V i j s))
          (blockLevel i j t)) = _
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul,
        SamplingNumerators.U_map, hA, hB, hP, hsource]
      have hc := congrFun (DenominatorEquation.E_smul_Phi ha hb hr hq hπA hπB i j)
        (blockLevel i j t)
      change LinearAlgebra.Tridiag.E F i j a b ρ * Phi q πA πB i j (blockLevel i j t) =
        ∑ s : Fin (min i j + 1), Analysis.DenominatorEquation.U F i j a b ρ (blockLevel i j t) s *
          phiRecursionSource q πA πB i j s at hc
      calc
        (∑ s : Fin (min i j + 1), Analysis.DenominatorEquation.U F i j a b ρ (blockLevel i j t) s *
            (Dcut a b ρ i j * phiRecursionSource q πA πB i j s)) =
            Dcut a b ρ i j * (∑ s : Fin (min i j + 1),
              Analysis.DenominatorEquation.U F i j a b ρ (blockLevel i j t) s * phiRecursionSource q
                  πA πB i j s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = Dfull a b ρ i j * Phi q πA πB i j t := by
          rw [← hc, hlevel, ← mul_assoc, Dcut_mul_E a b ρ hi hj]
  exact main (i + j) i j rfl t

end Actual

end Rhone.Probability.SamplingUniform
