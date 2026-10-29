/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! # Coefficient extraction as a fixed linear functional on values -/

@[expose] public section

namespace Rhone.Probability.InfiniteAllelesLimit

open Finset Polynomial

noncomputable def exWeight {ι : Type*} [DecidableEq ι] (s : Finset ι) (xs : ι → ℝ) (d : ℕ)
    (k : ι) : ℝ := (Lagrange.basis s xs k).coeff d

theorem sum_exWeight_eval {ι : Type*} [DecidableEq ι] {s : Finset ι} {xs : ι → ℝ}
    (hinj : Set.InjOn xs s) (d : ℕ) (p : Polynomial ℝ) (hdeg : p.degree < s.card) :
    (∑ k ∈ s, exWeight s xs d k * p.eval (xs k)) = p.coeff d := by
  have hp := congrArg (fun q : Polynomial ℝ => q.coeff d) (Lagrange.eq_interpolate hinj hdeg)
  rw [hp, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_C_mul, exWeight]; ring

theorem sum_monomial_coeff {ι : Type*} (s : Finset ι) (c : ι → ℝ) (e : ι → ℕ) (D : ℕ) :
    (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ (e i)).coeff D
      = ∑ i ∈ s, if D = e i then c i else 0 := by
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> ring

theorem degree_sum_monomial_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (e : ι → ℕ) (N : ℕ)
    (h : ∀ i ∈ s, e i ≤ N) :
    (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ (e i)).degree ≤ (N : WithBot ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
  refine (Polynomial.degree_C_mul_X_pow_le (e i) (c i)).trans ?_
  exact_mod_cast h i hi

noncomputable def xnode (m n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (((k : ℕ) : ℝ) + 1) / (((m : ℝ) + 1) * ((n : ℝ) + 2))

variable {m n : ℕ} {k : Fin (n + 1)}

theorem xnode_den_pos (m n : ℕ) : (0 : ℝ) < ((m : ℝ) + 1) * ((n : ℝ) + 2) := by positivity

theorem xnode_pos : 0 < xnode m n k := by
  rw [xnode]
  have h1 : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
  exact div_pos h1 (xnode_den_pos m n)

theorem xnode_nonneg : 0 ≤ xnode m n k := xnode_pos.le

theorem mul_xnode_le_one : (m : ℝ) * xnode m n k ≤ 1 := by
  have hden := xnode_den_pos m n
  have hk : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : ((k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.1 k.isLt
    linarith
  rw [xnode, mul_div_assoc', div_le_one hden]
  nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]

theorem xnode_injOn :
    Set.InjOn (xnode m n) ↑(Finset.univ : Finset (Fin (n + 1))) := by
  intro a _ b _ hab
  have hden : ((m : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := (xnode_den_pos m n).ne'
  rw [xnode, xnode, div_eq_div_iff hden hden] at hab
  have h : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
    have := mul_right_cancel₀ hden hab
    linarith
  exact Fin.ext (by exact_mod_cast h)

theorem sum_exWeight_xnode (m d : ℕ) (p : Polynomial ℝ) (hdeg : p.degree ≤ (n : WithBot ℕ)) :
    (∑ k : Fin (n + 1), exWeight Finset.univ (xnode m n) d k * p.eval (xnode m n k))
      = p.coeff d := by
  refine sum_exWeight_eval xnode_injOn d p (lt_of_le_of_lt hdeg ?_)
  rw [Finset.card_univ, Fintype.card_fin]
  exact_mod_cast Nat.lt_succ_self n

end Rhone.Probability.InfiniteAllelesLimit
