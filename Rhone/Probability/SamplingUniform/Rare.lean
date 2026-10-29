/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.Generic

/-! # Rare-frequency coefficients of the concrete generic hierarchy -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open MvPolynomial LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy
    RareAlleleHierarchy

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem vanish_A_active {a b ρ : K}
    {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K} (hD : IsRecursionSolution a b ρ Φ)
    (hE : ∀ i j : ℕ, 2 ≤ i → j ≠ 1 → LinearAlgebra.Tridiag.E K i j a b ρ ≠ 0)
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h1B : ∀ a u : ℕ, Φ a 1 u = 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (i j t : ℕ) (hi : 1 ≤ i) : Van 0 (Φ i j t) := by
  have key : ∀ n i j t : ℕ, i + j ≤ n → 1 ≤ i → Van 0 (Φ i j t) := by
    intro n
    induction n with
    | zero => intro i j t hn hi; omega
    | succ n ih =>
      intro i j t hn hi
      have ihlt : ∀ x y u : ℕ, 1 ≤ x → x + y < i + j → Van 0 (Φ x y u) :=
        fun x y u hx hxy => ih x y u (by omega) hx
      rcases Nat.eq_or_lt_of_le hi with hi1 | hi2
      · rw [← hi1, h1A j t]
        exact Van.zero 0
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · refine van_of_van_src hD (hE i 0 (by omega) (by omega)) hrange (fun s hs => ?_) t
          have hs0 : s = 0 := by simpa using hs
          subst hs0
          exact van_recursionSource_zero (by omega) (fun x y u hx hxy => ih x y u (by omega) hx)
        · rcases Nat.eq_or_lt_of_le hj with hj1 | hj2
          · rw [← hj1, h1B i t]
            exact Van.zero 0
          · exact van_of_van_src hD (hE i j (by omega) (by omega)) hrange
              (fun s _ => van_recursionSource (by omega) (by omega) ihlt) t
  exact key (i + j) i j t (le_refl _) hi

private theorem E_edge_ne_zero (a b ρ : K) (hP : ∀ n, poch a n ≠ 0)
    {i : ℕ} (hi : 2 ≤ i) : LinearAlgebra.Tridiag.E K i 0 a b ρ ≠ 0 := by
  have hlast : a + ((i - 1 : ℕ) : K) ≠ 0 := by
    have hp := hP i
    rw [poch_succ_top a hi] at hp
    exact (mul_ne_zero_iff.mp hp).2
  have heq : LinearAlgebra.Tridiag.E K i 0 a b ρ = (i : K) * (a + ((i - 1 : ℕ) : K)) := by
    rw [LinearAlgebra.Tridiag.E_eq_cont]
    simp [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef]
    ring
  rw [heq]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hlast

theorem generic_E_active (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0)
    {i j : ℕ} (hi : i ≠ 1) (hj : j ≠ 1) (hn : 2 ≤ i + j) :
    LinearAlgebra.Tridiag.E K i j a b ρ ≠ 0 := by
  by_cases hj0 : j = 0
  · subst j
    exact E_edge_ne_zero a b ρ (fun n => by simpa [Dfull_j_zero] using hD n 0) (by omega)
  by_cases hi0 : i = 0
  · subst i
    rw [E_swap]
    exact E_edge_ne_zero b a ρ (fun n => by simpa [Dfull_i_zero] using hD 0 n) (by omega)
  have hd := hD i j
  rw [← Dcut_mul_E a b ρ (by omega : 2 ≤ i) (by omega : 2 ≤ j)] at hd
  exact (mul_ne_zero_iff.mp hd).2

theorem genericPhi_vanA (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0)
    (i j t : ℕ) (hi : 1 ≤ i) : Van 0 (genericPhi a b ρ i j t) := by
  apply vanish_A_active (genericPhi_isRecursionSolution a b ρ hD)
    (fun i j hi hj => generic_E_active a b ρ hD (by omega) hj (by omega))
    (genericPhi_one_left a b ρ) (genericPhi_one_right a b ρ) (genericPhi_clamp a b ρ) i j t hi

theorem genericPhi_vanB (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0)
    (i j t : ℕ) (hj : 1 ≤ j) : Van 1 (genericPhi a b ρ i j t) := by
  refine Van_one_of_Van_zero_rename ?_
  refine vanish_A_active (Φ := fun x y u => rename swp (genericPhi a b ρ y x u))
    (isRecursionSolution_swap (genericPhi_isRecursionSolution a b ρ hD)) ?_ ?_ ?_ ?_ j i t hj
  · intro x y hx hy
    rw [E_swap]
    exact generic_E_active a b ρ hD hy (by omega) (by omega)
  · intro y u
    simp
  · intro x u
    simp
  · intro x y u hu
    rw [genericPhi_clamp a b ρ y x u (by omega), Nat.min_comm x y]

theorem genericPhi_rareHyp (a b ρ : K) (hD : ∀ i j, Dfull a b ρ i j ≠ 0) :
    RareHyp (alphaSeq a) (alphaSeq b) (genericPhi a b ρ) := by
  refine ⟨genericPhi_vanA a b ρ hD, genericPhi_vanB a b ρ hD,
    genericPhi_one_left a b ρ, genericPhi_one_right a b ρ, ?_, ?_, ?_⟩
  · intro u
    rw [genericPhi_zero_zero]
    simp [cf, mon]
  · intro j u hj
    rw [genericPhi_clamp a b ρ 0 j u (by simp), Nat.zero_min]
    apply beta_eq_alphaSeq (genericPhi_isRecursionSolution a b ρ hD) (genericPhi_vanB a b ρ hD)
      (genericPhi_one_right a b ρ) (by rw [genericPhi_zero_zero]; simp [cf, mon]) hj
    simpa [Dfull_i_zero, poch] using hD 0 j
  · intro i u hi
    rw [genericPhi_clamp a b ρ i 0 u (by simp), Nat.min_zero]
    apply alpha_eq_alphaSeq (genericPhi_isRecursionSolution a b ρ hD) (genericPhi_vanA a b ρ hD)
      (genericPhi_one_left a b ρ) (by rw [genericPhi_zero_zero]; simp [cf, mon]) hi
    simpa [Dfull_j_zero, poch] using hD i 0

end Rhone.Probability.SamplingUniform
