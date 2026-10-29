/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Ewens
public import Rhone.Probability.Ewens
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Basic.Real.Basic

/-!
# Executable Ewens quantities equal the specification

Source: ewens1972, eq. (11), (22)–(23), (30), pp. 91, 95, 102; durrett2008, Thm 1.11. -/

@[expose] public section
namespace Rhone.Computation.Ewens
open Finset

theorem factorial_eq (n : Nat) : factorial n = Nat.factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.factorial_succ, ih]

theorem risingFactorial_eq (θ : ℚ) (n : Nat) :
    risingFactorial θ n = (ascPochhammer ℚ n).eval θ := by
  induction n with
  | zero => simp [risingFactorial]
  | succ n ih => rw [ascPochhammer_succ_eval, ← ih]; rfl

private theorem getD_zipWith_add (a b : List Nat) (h : a.length = b.length) (k : Nat) :
    (List.zipWith (· + ·) a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  induction a generalizing b k with
  | nil =>
    cases b with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      cases k with
      | zero => simp
      | succ k => simpa using ih ys (by simpa using h) k

private theorem getD_map_append_zero (n : Nat) (row : List Nat) (k : Nat) :
    (row.map (n * ·) ++ [0]).getD k 0 = n * row.getD k 0 := by
  induction row generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

private theorem stirlingStep_getD (n : Nat) (row : List Nat) (k : Nat) :
    (stirlingStep n row).getD k 0 =
      n * row.getD k 0 + (match k with | 0 => 0 | k + 1 => row.getD k 0) := by
  unfold stirlingStep
  rw [getD_zipWith_add _ _ (by simp), getD_map_append_zero]
  cases k <;> simp

theorem stirling_eq (n k : Nat) : stirling n k = Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [stirling, stirlingRow]
  | succ n ih =>
    have e : stirling (n + 1) k =
        n * stirling n k + (match k with | 0 => 0 | k + 1 => stirling n k) :=
      stirlingStep_getD n (stirlingRow n) k
    rw [e]
    cases k with
    | zero =>
      rw [ih]
      cases n with
      | zero => simp
      | succ m => simp [Nat.stirlingFirst]
    | succ k => simp only [ih, Nat.stirlingFirst]

theorem classProduct_eq (θ : ℚ) (parts : List Nat) (m : Nat) :
    classProduct θ parts m = ∏ j ∈ Icc 1 m, classFactor θ parts j := by
  induction m with
  | zero => simp [classProduct]
  | succ m ih => rw [Finset.prod_Icc_succ_top (by omega), ← ih]; rfl

theorem harmonicSum_eq (θ : ℚ) (n : Nat) :
    harmonicSum θ n = ∑ i ∈ range n, θ / (θ + i) := by
  induction n with
  | zero => simp [harmonicSum]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

def toPartition (parts : List Nat) (h : ∀ x ∈ parts, 0 < x) : Nat.Partition parts.sum where
  parts := (parts : Multiset Nat)
  parts_pos := fun {i} hi => h i (by simpa using hi)
  parts_sum := by simp

theorem esf_eq_none_iff (θ : ℚ) (parts : List Nat) :
    esf θ parts = none ↔ θ ≤ 0 ∨ ∃ x ∈ parts, x = 0 := by
  unfold esf
  by_cases h : θ ≤ 0 ∨ parts.any (· == 0) = true
  · simp only [h, ↓reduceIte, true_iff]
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
      exact ⟨x, hx, by simpa using hx0⟩
  · simp only [h, ↓reduceIte, reduceCtorEq, false_iff]
    intro h'
    apply h
    rcases h' with h' | ⟨x, hx, hx0⟩
    · exact Or.inl h'
    · exact Or.inr (List.any_eq_true.2 ⟨x, hx, by simp [hx0]⟩)

theorem esf_eq_some (θ : ℚ) (hθ : 0 < θ) (parts : List Nat) (hp : ∀ x ∈ parts, 0 < x) :
    esf θ parts = some (Rhone.Probability.esf θ (toPartition parts hp)) := by
  have hany : parts.any (· == 0) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
    have := hp x hx
    simp at hx0
    omega
  have hne : ¬ (θ ≤ 0 ∨ parts.any (· == 0) = true) := by
    simp [hany, hθ]
  unfold esf
  simp only [hne, ↓reduceIte]
  rw [Rhone.Probability.esf_eq_prod, classProduct_eq, risingFactorial_eq,
    factorial_eq]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [classFactor, toPartition, factorial_eq, Multiset.coe_count]

private theorem cast_ascPochhammer (θ : ℚ) (n : Nat) :
    (((ascPochhammer ℚ n).eval θ : ℚ) : ℝ) = (ascPochhammer ℝ n).eval (θ : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Rat.cast_mul, ih]; simp

theorem esf_eq_some_real (θ : ℚ) (hθ : 0 < θ) (parts : List Nat) (hp : ∀ x ∈ parts, 0 < x) :
    ∃ q : ℚ, esf θ parts = some q ∧
      (q : ℝ) = Rhone.Probability.esf (θ : ℝ) (toPartition parts hp) := by
  refine ⟨_, esf_eq_some θ hθ parts hp, ?_⟩
  rw [Rhone.Probability.esf_eq_prod (θ : ℝ), Rhone.Probability.esf_eq_prod θ]
  rw [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, cast_ascPochhammer, Rat.cast_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have h := map_pow (Rat.castHom ℝ) (θ / (j : ℚ))
    (Multiset.count j (toPartition parts hp).parts)
  rw [Rat.coe_castHom] at h
  rw [Rat.cast_div, h]
  simp

theorem alleleCountProb_eq_some (θ : ℚ) (hθ : 0 < θ) (n k : Nat) :
    alleleCountProb θ n k = some (∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => p.parts.card = k), Rhone.Probability.esf θ p) := by
  rw [Rhone.Probability.sum_esf_card]
  unfold alleleCountProb
  have hn : ¬ θ ≤ 0 := not_le.2 hθ
  simp only [hn, ↓reduceIte]
  rw [risingFactorial_eq, stirling_eq]

theorem alleleCountProb_eq_none_iff (θ : ℚ) (n k : Nat) :
    alleleCountProb θ n k = none ↔ θ ≤ 0 := by
  unfold alleleCountProb
  by_cases h : θ ≤ 0 <;> simp [h]

theorem expectedAlleles_eq_some (θ : ℚ) (hθ : 0 < θ) (n : Nat) :
    expectedAlleles θ n = some (∑ p : Nat.Partition n,
      (p.parts.card : ℚ) * Rhone.Probability.esf θ p) := by
  rw [Rhone.Probability.sum_card_mul_esf θ n (fun i _ => by positivity)]
  unfold expectedAlleles
  have hn : ¬ θ ≤ 0 := not_le.2 hθ
  simp only [hn, ↓reduceIte]
  rw [harmonicSum_eq]

theorem expectedAlleles_eq_none_iff (θ : ℚ) (n : Nat) :
    expectedAlleles θ n = none ↔ θ ≤ 0 := by
  unfold expectedAlleles
  by_cases h : θ ≤ 0 <;> simp [h]

end Rhone.Computation.Ewens
