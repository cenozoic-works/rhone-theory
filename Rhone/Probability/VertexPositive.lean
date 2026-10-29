/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Vertex

/-! # Vanishing of the `Φ` polynomials when `E_{i,j}` is nonzero off the origin -/

@[expose] public section

namespace Rhone.Probability.VertexPositivity

open MvPolynomial Analysis Rhone.LinearAlgebra Analysis.RareAlleleHierarchy RareAlleleHierarchy

theorem E_zero_zero {K : Type*} [Field K] (θA θB ρ : K) : Tridiag.E K 0 0 θA θB ρ = 0 := by
  rw [Tridiag.E_eq_cont]
  simp [Tridiag.cont, Tridiag.dcoef]

theorem not_forall_E_ne_zero {K : Type*} [Field K] (θA θB ρ : K) :
    ¬ ∀ i j : ℕ, Tridiag.E K i j θA θB ρ ≠ 0 :=
  fun h => h 0 0 (E_zero_zero θA θB ρ)

variable {K : Type*} [Field K] {θA θB ρ : K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem vanish_A_of_pos (hD : IsRecursionSolution θA θB ρ Φ)
    (hE : ∀ i j : ℕ, 0 < i + j → Tridiag.E K i j θA θB ρ ≠ 0)
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h1B : ∀ a u : ℕ, Φ a 1 u = 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (i j t : ℕ) (hi : 1 ≤ i) : Van 0 (Φ i j t) := by
  have key : ∀ n i j t : ℕ, i + j ≤ n → 1 ≤ i → Van 0 (Φ i j t) := by
    intro n
    induction n with
    | zero => intro i j t hn hi; omega
    | succ n ih =>
      intro i j t hn hi
      have ihlt : ∀ a b u : ℕ, 1 ≤ a → a + b < i + j → Van 0 (Φ a b u) :=
        fun a b u ha hab => ih a b u (by omega) ha
      rcases Nat.eq_or_lt_of_le hi with hi1 | hi2
      · rw [← hi1, h1A j t]
        exact Van.zero 0
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · refine van_of_van_src hD (hE i 0 (by omega)) hrange (fun s hs => ?_) t
          have hs0 : s = 0 := by simpa using hs
          subst hs0
          exact van_recursionSource_zero (by omega) (fun a b u ha hab => ih a b u (by omega) ha)
        · rcases Nat.eq_or_lt_of_le hj with hj1 | hj2
          · rw [← hj1, h1B i t]
            exact Van.zero 0
          · exact van_of_van_src hD (hE i j (by omega)) hrange
              (fun s _ => van_recursionSource (by omega) (by omega) ihlt) t
  exact key (i + j) i j t (le_refl _) hi

theorem vanish_B_of_pos (hD : IsRecursionSolution θA θB ρ Φ)
    (hE : ∀ i j : ℕ, 0 < i + j → Tridiag.E K i j θA θB ρ ≠ 0)
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h1B : ∀ a u : ℕ, Φ a 1 u = 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (i j t : ℕ) (hj : 1 ≤ j) : Van 1 (Φ i j t) := by
  refine Van_one_of_Van_zero_rename ?_
  refine vanish_A_of_pos
      (Φ := fun a b u => rename swp (Φ b a u)) (isRecursionSolution_swap hD) ?_ ?_ ?_ ?_
    j i t hj
  · intro a b hab
    rw [E_swap a b θB θA ρ]
    exact hE b a (by omega)
  · intro b u
    rw [h1B b u, map_zero]
  · intro a u
    rw [h1A a u, map_zero]
  · intro a b u hu
    rw [hrange b a u (by omega), Nat.min_comm a b]

end Rhone.Probability.VertexPositivity
