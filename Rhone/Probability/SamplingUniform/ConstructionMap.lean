/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.SolutionEvaluation

/-! # Naturality of the universal numerator -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Matrix LinearAlgebra.SlotDeletion SlotDeletion

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

theorem cutRatio_map (φ : R →+* S) (a b ρ : R) {i j x y : ℕ}
    (hx : x ≤ i) (hy : y ≤ j) (hlt : x < i ∨ y < j) (hi : 2 ≤ i)
    (hD : Dfull (φ a) (φ b) (φ ρ) x y ≠ 0) :
    φ (cutRatio a b ρ i j x y) = cutRatio (φ a) (φ b) (φ ρ) i j x y := by
  apply mul_left_cancel₀ hD
  have h := congrArg φ (Dfull_mul_cutRatio a b ρ hx hy hlt hi)
  simpa only [map_mul, Dfull_map, Dcut_map,
    Dfull_mul_cutRatio (φ a) (φ b) (φ ρ) hx hy hlt hi] using h

theorem clearedPhi_map (φ : R →+* S) (a b ρ κA γA κB γB : R)
    (hD : ∀ i j, Dfull (φ a) (φ b) (φ ρ) i j ≠ 0) (i j t : ℕ) :
    φ (clearedPhi a b ρ κA γA κB γB i j t) =
      clearedPhi (φ a) (φ b) (φ ρ) (φ κA) (φ γA) (φ κB) (φ γB) i j t := by
  have main : ∀ n i j, i + j = n → ∀ t,
      φ (clearedPhi a b ρ κA γA κB γB i j t) =
        clearedPhi (φ a) (φ b) (φ ρ) (φ κA) (φ γA) (φ κB) (φ γB) i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j hij t
      by_cases hj0 : j = 0
      · subst j
        rw [clearedPhi_A, clearedPhi_A, edgeNumerator_map]
      by_cases hi0 : i = 0
      · subst i
        rw [clearedPhi_B, clearedPhi_B, edgeNumerator_map]
      by_cases hi1 : i = 1
      · subst i
        rw [clearedPhi_one_left, clearedPhi_one_left, map_zero]
      by_cases hj1 : j = 1
      · subst j
        rw [clearedPhi_one_right, clearedPhi_one_right, map_zero]
      have hi : 2 ≤ i := by omega
      have hj : 2 ≤ j := by omega
      rw [clearedPhi_interior a b ρ κA γA κB γB hi hj,
        clearedPhi_interior (φ a) (φ b) (φ ρ) (φ κA) (φ γA) (φ κB) (φ γB) hi hj]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, SamplingNumerators.U_map]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      rw [recursionSource_map]
      apply recursionSource_congr_lower (φ κA) (φ γA) (φ κB) (φ γB) hi hj
      intro x y u hx hy hs
      rw [map_mul, cutRatio_map φ a b ρ hx hy (by omega) hi (hD x y),
        ih (x + y) (by omega) x y rfl u]
  exact main (i + j) i j rfl t

end Rhone.Probability.SamplingUniform
