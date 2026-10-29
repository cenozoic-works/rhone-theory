/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-! # The generator of the neutral Wright–Fisher diffusion -/

@[expose] public section

namespace Rhone.Diffusion

open Polynomial Finset

noncomputable def wfGenerator (f : ℝ → ℝ) (x : ℝ) : ℝ := x * (1 - x) / 2 * deriv (deriv f) x

def polynomialFunctions : Set (ℝ → ℝ) := Set.range fun (p : ℝ[X]) (x : ℝ) => p.eval x

theorem wfGenerator_eval (p : ℝ[X]) (x : ℝ) :
    wfGenerator (fun y => p.eval y) x = x * (1 - x) / 2 * (derivative (derivative p)).eval x := by
  have h1 : deriv (fun y => p.eval y) = fun y => (derivative p).eval y :=
    funext fun y => p.deriv
  rw [wfGenerator, h1, Polynomial.deriv]

theorem exists_second_difference_bound (p : ℝ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ h : ℝ, |h| ≤ 1 →
      |p.eval (x + h) + p.eval (x - h) - 2 * p.eval x
        - h ^ 2 * (derivative (derivative p)).eval x| ≤ K * |h| ^ 3 := by
  obtain ⟨d, hd⟩ : ∃ d, d = p.natDegree + 3 := ⟨_, rfl⟩
  have hbound : ∀ k, ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |(hasseDeriv k p).eval x| ≤ M :=
    fun k => by
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
        ((hasseDeriv k p).continuousOn (s := Set.Icc (0 : ℝ) 1))
      exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩
  choose M hM using hbound
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ k ∈ range d, |M k| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨2 * d * B, by positivity, fun x hx h hh => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun k => (hasseDeriv k p).eval x := ⟨_, rfl⟩
  have hexp : ∀ t : ℝ, p.eval (x + t) = ∑ k ∈ range d, c k * t ^ k := fun t => by
    rw [add_comm, ← taylor_eval,
      eval_eq_sum_range' (n := d) (by rw [natDegree_taylor]; omega)]
    simp only [taylor_coeff, hc]
  have hc0 : p.eval x = c 0 := by simp [hc]
  have h2 : (derivative (derivative p)).eval x = 2 * c 2 := by
    have h := congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := 2)) p
    simp only [Nat.factorial, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq, LinearMap.smul_apply] at h
    rw [← h, hc]
    simp
  have s1 : ∑ k ∈ range d, (if k = 0 then 2 * c 0 else 0) = 2 * c 0 := by
    rw [Finset.sum_ite_eq']
    simp [show 0 < d by omega]
  have s2 : ∑ k ∈ range d, (if k = 2 then 2 * c 2 * h ^ 2 else 0) = 2 * c 2 * h ^ 2 := by
    rw [Finset.sum_ite_eq']
    simp [show 2 < d by omega]
  have key : p.eval (x + h) + p.eval (x - h) - 2 * p.eval x
      - h ^ 2 * (derivative (derivative p)).eval x =
      ∑ k ∈ range d, (c k * (h ^ k + (-h) ^ k) -
        ((if k = 0 then 2 * c 0 else 0) + (if k = 2 then 2 * c 2 * h ^ 2 else 0))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, s1, s2, sub_eq_add_neg x h, hexp h,
      hexp (-h), h2, hc0, ← Finset.sum_add_distrib]
    have h3 : ∑ k ∈ range d, c k * (h ^ k + (-h) ^ k) =
        ∑ k ∈ range d, (c k * h ^ k + c k * (-h) ^ k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [h3]
    ring
  have hterm : ∀ k ∈ range d, |c k * (h ^ k + (-h) ^ k) -
      ((if k = 0 then 2 * c 0 else 0) + (if k = 2 then 2 * c 2 * h ^ 2 else 0))| ≤
      2 * B * |h| ^ 3 := by
    intro k hk
    have hnn : 0 ≤ 2 * B * |h| ^ 3 := by positivity
    rcases k with _ | _ | _ | k
    · have e : c 0 * (h ^ 0 + (-h) ^ 0) -
          ((if (0 : ℕ) = 0 then 2 * c 0 else 0) + (if (0 : ℕ) = 2 then 2 * c 2 * h ^ 2 else 0))
          = 0 := by
        simp only [pow_zero, ↓reduceIte, OfNat.zero_ne_ofNat, add_zero]
        ring
      rw [e, abs_zero]
      exact hnn
    · have e : c (0 + 1) * (h ^ (0 + 1) + (-h) ^ (0 + 1)) -
          ((if (0 + 1 : ℕ) = 0 then 2 * c 0 else 0) +
            (if (0 + 1 : ℕ) = 2 then 2 * c 2 * h ^ 2 else 0)) = 0 := by
        simp
      rw [e, abs_zero]
      exact hnn
    · have e : c (0 + 1 + 1) * (h ^ (0 + 1 + 1) + (-h) ^ (0 + 1 + 1)) -
          ((if (0 + 1 + 1 : ℕ) = 0 then 2 * c 0 else 0) +
            (if (0 + 1 + 1 : ℕ) = 2 then 2 * c 2 * h ^ 2 else 0)) = 0 := by
        simp only [zero_add, Nat.reduceAdd, OfNat.ofNat_ne_zero, ↓reduceIte, neg_pow_two]
        ring
      rw [e, abs_zero]
      exact hnn
    · have e0 : ¬(k + 1 + 1 + 1 = 0) := by omega
      have e2 : ¬(k + 1 + 1 + 1 = 2) := by omega
      simp only [e0, e2, ↓reduceIte, add_zero, sub_zero]
      rw [abs_mul]
      have hcB : |c (k + 1 + 1 + 1)| ≤ B := by
        have h1 : |c (k + 1 + 1 + 1)| ≤ M (k + 1 + 1 + 1) := by
          rw [hc]
          exact hM _ x hx
        have h2' : |M (k + 1 + 1 + 1)| ≤ B := by
          rw [hB]
          exact Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) hk
        exact h1.trans ((le_abs_self _).trans h2')
      have hpow : |h| ^ (k + 1 + 1 + 1) ≤ |h| ^ 3 :=
        pow_le_pow_of_le_one (abs_nonneg h) hh (by omega)
      have hs : |h ^ (k + 1 + 1 + 1) + (-h) ^ (k + 1 + 1 + 1)| ≤ 2 * |h| ^ 3 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_pow, abs_pow, abs_neg]
        linarith
      calc |c (k + 1 + 1 + 1)| * |h ^ (k + 1 + 1 + 1) + (-h) ^ (k + 1 + 1 + 1)|
          ≤ B * (2 * |h| ^ 3) := mul_le_mul hcB hs (abs_nonneg _) hB0
        _ = 2 * B * |h| ^ 3 := by ring
  rw [key]
  calc |∑ k ∈ range d, (c k * (h ^ k + (-h) ^ k) -
        ((if k = 0 then 2 * c 0 else 0) + (if k = 2 then 2 * c 2 * h ^ 2 else 0)))|
      ≤ ∑ k ∈ range d, |c k * (h ^ k + (-h) ^ k) -
        ((if k = 0 then 2 * c 0 else 0) + (if k = 2 then 2 * c 2 * h ^ 2 else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range d, 2 * B * |h| ^ 3 := Finset.sum_le_sum hterm
    _ = 2 * d * B * |h| ^ 3 := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        ring

end Rhone.Diffusion
