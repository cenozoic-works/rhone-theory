/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeTipSites.Channel
public import Mathlib.LinearAlgebra.Span.Defs

/-! # Finite rectangular Laplace spans, with degree bookkeeping and integral testing -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.ThreeTipSites

def mode (c : ℝ) (i j : ℕ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-c * ((i : ℝ) * t.1 + (j : ℝ) * t.2))

def grid (c : ℝ) (a b : ℕ) : Submodule ℝ ((ℝ × ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ i ≤ a, ∃ j ≤ b, f = mode c i j}

lemma mode_mem (c : ℝ) {a b i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) :
    mode c i j ∈ grid c a b := Submodule.subset_span ⟨i, hi, j, hj, rfl⟩

lemma mode_zero (c : ℝ) : mode c 0 0 = 1 := by
  ext t
  simp [mode]

lemma one_mem (c : ℝ) (a b : ℕ) : (1 : (ℝ × ℝ) → ℝ) ∈ grid c a b := by
  rw [← mode_zero c]
  exact mode_mem c (Nat.zero_le a) (Nat.zero_le b)

lemma constant_mem (c r : ℝ) (a b : ℕ) : (fun _ : ℝ × ℝ => r) ∈ grid c a b := by
  convert (grid c a b).smul_mem r (one_mem c a b) using 1
  ext t
  simp

lemma grid_mono (c : ℝ) {a b d e : ℕ} (ha : a ≤ d) (hb : b ≤ e) :
    grid c a b ≤ grid c d e := by
  apply Submodule.span_le.mpr
  rintro f ⟨i, hi, j, hj, rfl⟩
  exact mode_mem c (hi.trans ha) (hj.trans hb)

lemma mode_mul (c : ℝ) (i j p q : ℕ) :
    mode c i j * mode c p q = mode c (i + p) (j + q) := by
  ext t
  simp only [Pi.mul_apply, mode, ← Real.exp_add, Nat.cast_add]
  congr 1
  ring

lemma grid_mul {c : ℝ} {a b d e : ℕ} {f g : (ℝ × ℝ) → ℝ}
    (hf : f ∈ grid c a b) (hg : g ∈ grid c d e) :
    f * g ∈ grid c (a + d) (b + e) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨i, hi, j, hj, rfl⟩
    induction hg using Submodule.span_induction with
    | mem g hg =>
      rcases hg with ⟨p, hp, q, hq, rfl⟩
      rw [mode_mul]
      exact mode_mem c (Nat.add_le_add hi hp) (Nat.add_le_add hj hq)
    | zero => simp only [mul_zero, Submodule.zero_mem]
    | add x y _ _ hx hy =>
      simpa only [mul_add] using (grid c (a + d) (b + e)).add_mem hx hy
    | smul r x _ hx =>
      simpa only [mul_smul_comm] using (grid c (a + d) (b + e)).smul_mem r hx
  | zero => simp only [zero_mul, Submodule.zero_mem]
  | add x y _ _ hx hy =>
    simpa only [add_mul] using (grid c (a + d) (b + e)).add_mem hx hy
  | smul r x _ hx =>
    simpa only [smul_mul_assoc] using (grid c (a + d) (b + e)).smul_mem r hx

lemma grid_prod {ι : Type*} {c : ℝ} {a b : ℕ} (s : Finset ι)
    (f : ι → (ℝ × ℝ) → ℝ) (hf : ∀ i ∈ s, f i ∈ grid c a b) :
    (∏ i ∈ s, f i) ∈ grid c (a * s.card) (b * s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem c 0 0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hm := grid_mul (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hm

lemma mode_integrable {c : ℝ} (hc : 0 ≤ c) (i j : ℕ)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    Integrable (mode c i j) μ := by
  refine Integrable.of_bound (by unfold mode; fun_prop) 1 ?_
  filter_upwards [hμ] with t ht
  change ‖Real.exp (-c * ((i : ℝ) * t.1 + (j : ℝ) * t.2))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ (i : ℝ) * t.1 + (j : ℝ) * t.2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg i) ht.1)
      (mul_nonneg (Nat.cast_nonneg j) ht.2)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) h

lemma grid_integrable {c : ℝ} (hc : 0 ≤ c) {a b : ℕ}
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ)
    {f : (ℝ × ℝ) → ℝ} (hf : f ∈ grid c a b) : Integrable f μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨i, _, j, _, rfl⟩
    exact mode_integrable hc i j hμ
  | zero => exact integrable_zero _ _ _
  | add f g _ _ hf hg => exact hf.add hg
  | smul r f _ hf => exact hf.smul r

theorem integral_eq_of_grid {c : ℝ} (hc : 0 ≤ c) {a b : ℕ}
    {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hm : ∀ i ≤ a, ∀ j ≤ b, ∫ t, mode c i j t ∂μ = ∫ t, mode c i j t ∂ν)
    {f : (ℝ × ℝ) → ℝ} (hf : f ∈ grid c a b) : ∫ t, f t ∂μ = ∫ t, f t ∂ν := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨i, hi, j, hj, rfl⟩
    exact hm i hi j hj
  | zero => simp
  | add f g hfg hgg hf hg =>
    simp only [Pi.add_apply, integral_add (grid_integrable hc hμ hfg)
      (grid_integrable hc hμ hgg), integral_add (grid_integrable hc hν hfg)
      (grid_integrable hc hν hgg), hf, hg]
  | smul r f _ hf => simp only [Pi.smul_apply, integral_smul, hf]

end Rhone.Statistics.ThreeTipSites
