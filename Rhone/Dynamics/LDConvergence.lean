/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MultialleleLD
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
/-!
# Convergence of the deterministic multiallele recombination iteration

Source: burger2000, ch. 2. -/
@[expose] public section
namespace Rhone.Dynamics
open Finset MultialleleLD
namespace LDConvergence

/-- Source: burger2000, ch. 2. -/
private theorem iterate_distribution {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (c : ℝ) (hx : ∀ a b, 0 ≤ x a b)
    (ht : ∑ a, ∑ b, x a b = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t : ℕ) :
    (∀ a b, 0 ≤ ((recombine c)^[t] x) a b) ∧
      (∑ a, ∑ b, ((recombine c)^[t] x) a b = 1) := by
  induction t with
  | zero => simpa using And.intro hx ht
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact recombine_preserves_distribution c _ ih.1 hc0 hc1 ih.2

/-- Source: burger2000, ch. 2. -/
private theorem iterate_row {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (c : ℝ) (hx : ∀ a b, 0 ≤ x a b)
    (ht : ∑ a, ∑ b, x a b = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t : ℕ) (a : A) :
    row ((recombine c)^[t] x) a =
      row x a := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', row_recombine c _
      (iterate_distribution x c hx ht hc0 hc1 t).2, ih]

/-- Source: burger2000, ch. 2. -/
private theorem iterate_col {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (c : ℝ) (hx : ∀ a b, 0 ≤ x a b)
    (ht : ∑ a, ∑ b, x a b = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (t : ℕ) (b : B) :
    col ((recombine c)^[t] x) b =
      col x b := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', col_recombine c _
      (iterate_distribution x c hx ht hc0 hc1 t).2, ih]

/-- Source: burger2000, ch. 2. -/
private theorem iterate_entry {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (c : ℝ) (hx : ∀ a b, 0 ≤ x a b)
    (ht : ∑ a, ∑ b, x a b = 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (t : ℕ) (a : A) (b : B) :
    ((recombine c)^[t] x) a b =
      (1-c)^t * ld x a b +
        row x a * col x b := by
  have h := ld_iterate c x ht t a b
  unfold ld at h
  rw [iterate_row x c hx ht hc0 hc1 t a, iterate_col x c hx ht hc0 hc1 t b] at h
  unfold ld
  linarith

end LDConvergence

/-- Source: burger2000, ch. 2. -/
theorem multiallele_recombination_converges
    {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (c : ℝ)
    (hx : ∀ a b, 0 ≤ x a b) (ht : ∑ a, ∑ b, x a b = 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto (fun t : ℕ =>
      ((Rhone.Dynamics.MultialleleLD.recombine c)^[t] x)) Filter.atTop
      (nhds (fun a b => Rhone.Dynamics.MultialleleLD.row x a *
        Rhone.Dynamics.MultialleleLD.col x b)) := by
  have hpow : Filter.Tendsto (fun t : ℕ => (1-c)^t) Filter.atTop (nhds (0:ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hc1) (by linarith)
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  simp only [LDConvergence.iterate_entry x c hx ht (le_of_lt hc0) hc1]
  simpa using (hpow.mul_const (ld x a b)).add_const (row x a * col x b)

end Rhone.Dynamics
