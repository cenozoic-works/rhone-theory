/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Closure.CFinite
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # No hypergeometric step operator annihilates an exponential sum with more than two roots -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open Polynomial

variable {F : Type*} [Field F] [CharZero F]

noncomputable def step (a : F) (c : F → F[X]) (r : F) : F[X] :=
  C r * Closure.shift (c r) - C a * c r

omit [CharZero F] in
theorem eval_step (a : F) (c : F → F[X]) (r x : F) :
    (step a c r).eval x = r * (c r).eval (x + 1) - a * (c r).eval x := by
  rw [step]
  simp

omit [CharZero F] in
theorem coeff_step_natDegree (a r : F) (c : F → F[X]) :
    (step a c r).coeff (c r).natDegree = (r - a) * (c r).leadingCoeff := by
  have h1 : (Closure.shift (c r)).coeff (c r).natDegree = (c r).leadingCoeff := by
    rw [← Closure.natDegree_shift (c r)]
    exact Closure.leadingCoeff_shift (c r)
  have h2 : (c r).coeff (c r).natDegree = (c r).leadingCoeff := rfl
  rw [step, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, h1, h2]
  ring

omit [CharZero F] in
theorem natDegree_step_le (a r : F) (c : F → F[X]) :
    (step a c r).natDegree ≤ (c r).natDegree := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (Polynomial.natDegree_C_mul_le r (Closure.shift (c r)))
      (le_of_eq (Closure.natDegree_shift (c r)))
  · exact Polynomial.natDegree_C_mul_le a (c r)

omit [CharZero F] in
theorem step_ne_zero {a r : F} (hra : r ≠ a) {c : F → F[X]} (h : c r ≠ 0) :
    step a c r ≠ 0 := by
  intro hz
  have hc := coeff_step_natDegree a r c
  rw [hz, Polynomial.coeff_zero] at hc
  have h1 : (c r).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h
  rcases mul_eq_zero.mp hc.symm with h' | h'
  · exact hra (sub_eq_zero.mp h')
  · exact h1 h'

omit [CharZero F] in
theorem natDegree_step_lt {a : F} {c : F → F[X]} (hz : step a c a ≠ 0) :
    (step a c a).natDegree < (c a).natDegree := by
  refine lt_of_le_of_ne (natDegree_step_le a a c) fun heq => ?_
  have hc := coeff_step_natDegree a a c
  rw [sub_self, zero_mul, ← heq] at hc
  exact (Polynomial.leadingCoeff_ne_zero.mpr hz) hc

noncomputable def expEval (c : F → F[X]) (a : F) (s : Finset F) (k : ℕ) : F :=
  (c a).eval (k : F) * a ^ k + ∑ r ∈ s, (c r).eval (k : F) * r ^ k

omit [CharZero F] in
theorem expEval_step (a : F) (c : F → F[X]) (s : Finset F) (k : ℕ) :
    expEval (fun r => step a c r) a s k
      = expEval c a s (k + 1) - a * expEval c a s k := by
  have hcast : ((k + 1 : ℕ) : F) = (k : F) + 1 := by push_cast; ring
  have hterm : ∀ r : F, (step a c r).eval (k : F) * r ^ k
      = (c r).eval ((k : F) + 1) * r ^ (k + 1) - a * ((c r).eval (k : F) * r ^ k) := by
    intro r
    rw [eval_step]
    ring
  simp only [expEval, hterm, hcast]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

omit [CharZero F] in
theorem exists_kill (a : F) (s : Finset F) (ha : a ∉ s) (N : ℕ) :
    ∀ w : ℕ, ∀ c : F → F[X], (c a = 0 ∨ (c a).natDegree < w) →
      (∀ k : ℕ, N ≤ k → expEval c a s k = 0) →
      ∃ c' : F → F[X], (∀ r ∈ s, c r ≠ 0 → c' r ≠ 0) ∧
        ∀ k : ℕ, N ≤ k → ∑ r ∈ s, (c' r).eval (k : F) * r ^ k = 0 := by
  intro w
  induction w with
  | zero =>
    intro c hw hsum
    have hca : c a = 0 := by
      rcases hw with h | h
      · exact h
      · exact absurd h (Nat.not_lt_zero _)
    refine ⟨c, fun _ _ h => h, fun k hk => ?_⟩
    have h := hsum k hk
    rw [expEval, hca] at h
    simpa using h
  | succ w ih =>
    intro c hw hsum
    rcases eq_or_ne (c a) 0 with hca | hca
    · refine ⟨c, fun _ _ h => h, fun k hk => ?_⟩
      have h := hsum k hk
      rw [expEval, hca] at h
      simpa using h
    · have hnext : step a c a = 0 ∨ (step a c a).natDegree < w := by
        rcases eq_or_ne (step a c a) 0 with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          have h1 := natDegree_step_lt h
          have h2 : (c a).natDegree < w + 1 := hw.resolve_left hca
          omega
      have hstepsum : ∀ k : ℕ, N ≤ k → expEval (fun r => step a c r) a s k = 0 := by
        intro k hk
        rw [expEval_step, hsum k hk, hsum (k + 1) (by omega), mul_zero, sub_zero]
      obtain ⟨c', hc'ne, hc'sum⟩ := ih (fun r => step a c r) hnext hstepsum
      refine ⟨c', ?_, hc'sum⟩
      intro r hr hcr
      refine hc'ne r hr (step_ne_zero ?_ hcr)
      intro hra
      subst hra
      exact ha hr

theorem eq_zero_of_expEval_eq_zero (N : ℕ) :
    ∀ s : Finset F, (0 : F) ∉ s → ∀ c : F → F[X],
      (∀ k : ℕ, N ≤ k → ∑ r ∈ s, (c r).eval (k : F) * r ^ k = 0) → ∀ r ∈ s, c r = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _ r hr
    exact absurd hr (by simp)
  | @insert a s ha ih =>
    intro h0 c hsum
    have haz : a ≠ 0 := by
      intro h
      apply h0
      rw [← h]
      exact Finset.mem_insert_self a s
    have hs0 : (0 : F) ∉ s := fun h => h0 (Finset.mem_insert_of_mem h)
    have hsplit : ∀ k : ℕ, N ≤ k → expEval c a s k = 0 := by
      intro k hk
      have h := hsum k hk
      rwa [Finset.sum_insert ha, ← expEval] at h
    obtain ⟨c', hc'ne, hc'sum⟩ := exists_kill a s ha N ((c a).natDegree + 1) c
      (Or.inr (Nat.lt_succ_self _)) hsplit
    have hzero : ∀ r ∈ s, c' r = 0 := ih hs0 c' hc'sum
    have hcs : ∀ r ∈ s, c r = 0 := by
      intro r hr
      by_contra hcr
      exact hc'ne r hr hcr (hzero r hr)
    have hca : c a = 0 := by
      refine Closure.eq_zero_of_eval_natCast_eq_zero (N := N) fun k hk => ?_
      have h := hsum k hk
      have hz : ∑ r ∈ s, (c r).eval (k : F) * r ^ k = 0 :=
        Finset.sum_eq_zero fun r hr => by rw [hcs r hr]; simp
      rw [Finset.sum_insert ha, hz, add_zero] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero k haz)
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact hca
    · exact hcs r hr'

noncomputable def expSum (s : Finset F) (α : F → F) (k : ℕ) : F := ∑ r ∈ s, α r * r ^ k

noncomputable def expPolySum (s : Finset F) (c : F → F[X]) (k : ℕ) : F :=
  ∑ r ∈ s, (c r).eval (k : F) * r ^ k

omit [CharZero F] in
theorem expSum_eq_expPolySum (s : Finset F) (α : F → F) :
    expSum s α = expPolySum s fun r => C (α r) := by
  funext k
  rw [expSum, expPolySum]
  exact Finset.sum_congr rfl fun r _ => by rw [Polynomial.eval_C]

omit [CharZero F] in
theorem eval_prodRoots (s : Finset F) (x : F) :
    (∏ r ∈ s, (X - C r)).eval x = ∏ r ∈ s, (x - r) := by
  rw [Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun r _ => by simp

omit [CharZero F] in
theorem expSum_cfinite (s : Finset F) (α : F → F) (k : ℕ) :
    ∑ m ∈ Finset.range (s.card + 1),
      (∏ r ∈ s, (X - C r)).coeff m * expSum s α (k + m) = 0 := by
  set χ : F[X] := ∏ r ∈ s, (X - C r) with hχ
  have hdeg : χ.natDegree = s.card := by
    rw [hχ, Polynomial.natDegree_prod s (fun r => X - C r)
      fun r _ => Polynomial.X_sub_C_ne_zero r]
    simp
  have hroot : ∀ r ∈ s, χ.eval r = 0 := by
    intro r hr
    rw [hχ, eval_prodRoots]
    exact Finset.prod_eq_zero hr (sub_self r)
  have hterm : ∀ m : ℕ, χ.coeff m * expSum s α (k + m)
      = ∑ r ∈ s, χ.coeff m * (α r * r ^ k) * r ^ m := by
    intro m
    rw [expSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [pow_add]; ring
  calc ∑ m ∈ Finset.range (s.card + 1), χ.coeff m * expSum s α (k + m)
      = ∑ m ∈ Finset.range (s.card + 1), ∑ r ∈ s, χ.coeff m * (α r * r ^ k) * r ^ m :=
        Finset.sum_congr rfl fun m _ => hterm m
    _ = ∑ r ∈ s, ∑ m ∈ Finset.range (s.card + 1), χ.coeff m * (α r * r ^ k) * r ^ m :=
        Finset.sum_comm
    _ = ∑ r ∈ s, α r * r ^ k * χ.eval r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Polynomial.eval_eq_sum_range' (n := s.card + 1) (by omega) r, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun r hr => by rw [hroot r hr, mul_zero]

omit [CharZero F] in
theorem shift_ne_zero {p : F[X]} (h : p ≠ 0) : Closure.shift p ≠ 0 := by
  intro hz
  have hlc := Closure.leadingCoeff_shift p
  rw [hz, Polynomial.leadingCoeff_zero] at hlc
  exact (Polynomial.leadingCoeff_ne_zero.mpr h) hlc.symm

theorem not_isHypergeometric_expPolySum (s : Finset F) (h0 : (0 : F) ∉ s) (c : F → F[X])
    {r₁ r₂ : F} (h1 : r₁ ∈ s) (h2 : r₂ ∈ s) (hne : r₁ ≠ r₂)
    (hc1 : c r₁ ≠ 0) (hc2 : c r₂ ≠ 0) :
    ¬ Closure.IsHypergeometric (expPolySum s c) := by
  rintro ⟨P, Q, N, hQ, hrel⟩
  have hr1 : r₁ ≠ 0 := by
    intro hz
    apply h0
    rw [← hz]
    exact h1
  have hkey : ∀ k : ℕ, N ≤ k →
      ∑ r ∈ s, ((fun r => C r * Closure.shift (c r) * Q - c r * P) r).eval (k : F) * r ^ k
        = 0 := by
    intro k hk
    have h := hrel k hk
    rw [expPolySum, expPolySum] at h
    have hcast : ((k + 1 : ℕ) : F) = (k : F) + 1 := by push_cast; ring
    rw [hcast] at h
    have hgoal :
        ∑ r ∈ s, ((fun r => C r * Closure.shift (c r) * Q - c r * P) r).eval (k : F) * r ^ k
          = (∑ r ∈ s, (c r).eval ((k : F) + 1) * r ^ (k + 1)) * Q.eval (k : F)
            - (∑ r ∈ s, (c r).eval (k : F) * r ^ k) * P.eval (k : F) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Closure.eval_shift]
      rw [pow_succ]
      ring
    rw [hgoal, h, sub_self]
  have hzero := eq_zero_of_expEval_eq_zero N s h0
    (fun r => C r * Closure.shift (c r) * Q - c r * P) hkey
  have hsplit : ∀ r ∈ s, C r * Closure.shift (c r) * Q = c r * P := by
    intro r hr
    have h : C r * Closure.shift (c r) * Q - c r * P = 0 := hzero r hr
    linear_combination h
  have hP : P ≠ 0 := by
    intro hP0
    have h := hsplit r₁ h1
    rw [hP0, mul_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hr1 (Polynomial.C_eq_zero.mp h'')
      · exact shift_ne_zero hc1 h''
    · exact hQ h'
  have hcross : C r₁ * (Closure.shift (c r₁) * c r₂) = C r₂ * (c r₁ * Closure.shift (c r₂)) := by
    refine mul_left_cancel₀ (mul_ne_zero hP hQ) ?_
    have hA := hsplit r₁ h1
    have hB := hsplit r₂ h2
    calc P * Q * (C r₁ * (Closure.shift (c r₁) * c r₂))
        = (C r₁ * Closure.shift (c r₁) * Q) * (c r₂ * P) := by ring
      _ = (c r₁ * P) * (C r₂ * Closure.shift (c r₂) * Q) := by rw [hA, hB]
      _ = P * Q * (C r₂ * (c r₁ * Closure.shift (c r₂))) := by ring
  have hlc := congrArg Polynomial.leadingCoeff hcross
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_C,
    Closure.leadingCoeff_shift, Closure.leadingCoeff_shift] at hlc
  have hne1 : (c r₁).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc1
  have hne2 : (c r₂).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc2
  refine hne ?_
  have hmul : (r₁ - r₂) * ((c r₁).leadingCoeff * (c r₂).leadingCoeff) = 0 := by
    linear_combination hlc
  rcases mul_eq_zero.mp hmul with h' | h'
  · exact sub_eq_zero.mp h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hne1
    · exact absurd h'' hne2

theorem not_isHypergeometric_expSum (s : Finset F) (h0 : (0 : F) ∉ s) (α : F → F)
    {r₁ r₂ : F} (h1 : r₁ ∈ s) (h2 : r₂ ∈ s) (hne : r₁ ≠ r₂)
    (hα1 : α r₁ ≠ 0) (hα2 : α r₂ ≠ 0) :
    ¬ Closure.IsHypergeometric (expSum s α) := by
  rw [expSum_eq_expPolySum]
  refine not_isHypergeometric_expPolySum s h0 (fun r => C (α r)) h1 h2 hne ?_ ?_
  · exact fun h => hα1 (Polynomial.C_eq_zero.mp h)
  · exact fun h => hα2 (Polynomial.C_eq_zero.mp h)

end Rhone.Analysis.RecombinationExpansion
