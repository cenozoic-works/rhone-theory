/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Arbitrarily close relative prime pairs -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

theorem exists_close_prime_pair (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧
      (q : ℝ) - (p : ℝ) < ε * (p : ℝ) := by
  classical
  by_contra h
  push Not at h
  let e : ℕ ≃o {p : ℕ // p.Prime} :=
    @Nat.Subtype.orderIsoOfNat {p : ℕ | p.Prime} Nat.infinite_setOfPred_prime.to_subtype
  let P : ℕ → ℕ := fun n => e n
  have hmono : StrictMono P := by
    intro i j hij
    exact e.strictMono hij
  have hp (n : ℕ) : (P n).Prime := (e n).property
  have hpos (n : ℕ) : (0 : ℝ) < P n := by
    exact_mod_cast (hp n).pos
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hratio : (1 : ℝ) / (1 + ε) < 1 := (div_lt_one hε1).2 (by linarith)
  have hs : Summable (fun n : ℕ => (1 : ℝ) / P n) := by
    apply summable_of_ratio_norm_eventually_le hratio
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    have hgap := h (P n) (P (n + 1)) (hp n) (hp (n + 1))
      (hn.trans (hmono.id_le n)) (hmono (Nat.lt_succ_self n))
    have hgrowth : (1 + ε) * (P n : ℝ) ≤ (P (n + 1) : ℝ) := by
      nlinarith
    rw [Real.norm_of_nonneg (one_div_pos.mpr (hpos (n + 1))).le,
      Real.norm_of_nonneg (one_div_pos.mpr (hpos n)).le]
    calc
      (1 : ℝ) / P (n + 1) ≤ 1 / ((1 + ε) * (P n : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos hε1 (hpos n)) hgrowth
      _ = (1 / (1 + ε)) * (1 / (P n : ℝ)) := by rw [one_div_mul_one_div]
  apply Nat.Primes.not_summable_one_div
  exact e.toEquiv.summable_iff.mp hs

theorem exists_prime_pair_mul_gap_lt (N M : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ M < p ∧ p < q ∧ N * (q - p) < p := by
  obtain ⟨p, q, hp, hq, hM, hpq, hgap⟩ :=
    exists_close_prime_pair (1 / ((N : ℝ) + 1)) (by positivity) (M + 1)
  refine ⟨p, q, hp, hq, by omega, hpq, ?_⟩
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hgap' : ((N : ℝ) + 1) * ((q : ℝ) - p) < p := by
    have hh := (mul_lt_mul_iff_right₀ hN).2 hgap
    field_simp at hh
    nlinarith
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hdiff : (0 : ℝ) < (q : ℝ) - p := sub_pos.mpr hpqR
  have hsmall : (N : ℝ) * ((q : ℝ) - p) < p := by nlinarith
  exact_mod_cast (show (N : ℝ) * ((q - p : ℕ) : ℝ) < p by
    simpa [Nat.cast_sub hpq.le] using hsmall)

end Rhone.Algebra.DiagonalObstruction
