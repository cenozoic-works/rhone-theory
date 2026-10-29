/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Assortative mating by genotype

Source: crow_kimura1970, sec. 4.6, p. 144. -/

@[expose] public section

namespace Rhone.Dynamics.Assortative

open Filter Topology

noncomputable def assortFreq (g : ℝ × ℝ × ℝ) : ℝ := g.1 + g.2.1 / 2

/-- Source: crow_kimura1970, sec. 4.6, p. 144. -/
noncomputable def assortStep (α : ℝ) (g : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((1 - α) * assortFreq g ^ 2 + α * (g.1 + g.2.1 / 4),
    (1 - α) * (2 * assortFreq g * (1 - assortFreq g)) + α * (g.2.1 / 2),
    (1 - α) * (1 - assortFreq g) ^ 2 + α * (g.2.2 + g.2.1 / 4))

noncomputable def assortOrbit (α : ℝ) (g0 : ℝ × ℝ × ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => g0
  | t + 1 => assortStep α (assortOrbit α g0 t)

noncomputable def assortHetFixed (α p : ℝ) : ℝ := 4 * p * (1 - p) * (1 - α) / (2 - α)

theorem assortStep_total (α : ℝ) {g : ℝ × ℝ × ℝ} (h : g.1 + g.2.1 + g.2.2 = 1) :
    (assortStep α g).1 + (assortStep α g).2.1 + (assortStep α g).2.2 = 1 := by
  simp only [assortStep, assortFreq]
  have : g.2.2 = 1 - g.1 - g.2.1 := by linarith
  rw [this]
  ring

theorem assortStep_freq (α : ℝ) (g : ℝ × ℝ × ℝ) :
    assortFreq (assortStep α g) = assortFreq g := by
  simp only [assortStep, assortFreq]
  ring

theorem assortOrbit_freq (α : ℝ) (g0 : ℝ × ℝ × ℝ) (t : ℕ) :
    assortFreq (assortOrbit α g0 t) = assortFreq g0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [assortOrbit, assortStep_freq, ih]

theorem assortOrbit_total (α : ℝ) {g0 : ℝ × ℝ × ℝ} (h : g0.1 + g0.2.1 + g0.2.2 = 1) (t : ℕ) :
    (assortOrbit α g0 t).1 + (assortOrbit α g0 t).2.1 + (assortOrbit α g0 t).2.2 = 1 := by
  induction t with
  | zero => exact h
  | succ t ih => exact assortStep_total α ih

theorem assortStep_nonneg {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {g : ℝ × ℝ × ℝ}
    (hD : 0 ≤ g.1) (hH : 0 ≤ g.2.1) (hR : 0 ≤ g.2.2) (hs : g.1 + g.2.1 + g.2.2 = 1) :
    0 ≤ (assortStep α g).1 ∧ 0 ≤ (assortStep α g).2.1 ∧ 0 ≤ (assortStep α g).2.2 := by
  have hp0 : 0 ≤ assortFreq g := by unfold assortFreq; positivity
  have hp1 : 0 ≤ 1 - assortFreq g := by unfold assortFreq; linarith
  have h1a : 0 ≤ 1 - α := by linarith
  simp only [assortStep]
  refine ⟨?_, ?_, ?_⟩ <;> positivity

theorem assortOrbit_nonneg {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {g0 : ℝ × ℝ × ℝ}
    (hD : 0 ≤ g0.1) (hH : 0 ≤ g0.2.1) (hR : 0 ≤ g0.2.2) (hs : g0.1 + g0.2.1 + g0.2.2 = 1)
    (t : ℕ) :
    0 ≤ (assortOrbit α g0 t).1 ∧ 0 ≤ (assortOrbit α g0 t).2.1 ∧
      0 ≤ (assortOrbit α g0 t).2.2 := by
  induction t with
  | zero => exact ⟨hD, hH, hR⟩
  | succ t ih =>
    exact assortStep_nonneg h0 h1 ih.1 ih.2.1 ih.2.2 (assortOrbit_total α hs t)

theorem assortOrbit_het_succ (α : ℝ) (g0 : ℝ × ℝ × ℝ) (t : ℕ) :
    (assortOrbit α g0 (t + 1)).2.1 =
      (1 - α) * (2 * assortFreq g0 * (1 - assortFreq g0)) +
        (α / 2) * (assortOrbit α g0 t).2.1 := by
  rw [assortOrbit]
  simp only [assortStep]
  rw [assortOrbit_freq]
  ring

theorem assortHetFixed_fixed {α : ℝ} (p : ℝ) (hα : α ≠ 2) :
    (1 - α) * (2 * p * (1 - p)) + (α / 2) * assortHetFixed α p = assortHetFixed α p := by
  have : 2 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  unfold assortHetFixed
  field_simp
  ring

theorem assortOrbit_het {α : ℝ} (g0 : ℝ × ℝ × ℝ) (hα : α ≠ 2) (t : ℕ) :
    (assortOrbit α g0 t).2.1 = assortHetFixed α (assortFreq g0) +
      (α / 2) ^ t * (g0.2.1 - assortHetFixed α (assortFreq g0)) := by
  have hfix := assortHetFixed_fixed (assortFreq g0) hα
  induction t with
  | zero => simp [assortOrbit]
  | succ t ih =>
    rw [assortOrbit_het_succ, ih, pow_succ]
    linear_combination hfix

theorem assortHetFixed_eq {α : ℝ} (p : ℝ) (hα : α ≠ 2) :
    assortHetFixed α p = 2 * p * (1 - p) * (1 - α / (2 - α)) := by
  have : 2 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  unfold assortHetFixed
  field_simp
  ring

theorem tendsto_assortOrbit_het {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (g0 : ℝ × ℝ × ℝ) :
    Tendsto (fun t => (assortOrbit α g0 t).2.1) atTop
      (𝓝 (assortHetFixed α (assortFreq g0))) := by
  have hα : α ≠ 2 := by intro h; linarith
  have hpow : Tendsto (fun t : ℕ => (α / 2) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith)
  have h := (hpow.mul_const (g0.2.1 - assortHetFixed α (assortFreq g0))).const_add
    (assortHetFixed α (assortFreq g0))
  simp only [zero_mul, add_zero] at h
  exact h.congr (fun t => (assortOrbit_het g0 hα t).symm)

theorem tendsto_assortOrbit_hom {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (g0 : ℝ × ℝ × ℝ) :
    Tendsto (fun t => (assortOrbit α g0 t).1) atTop
      (𝓝 (assortFreq g0 - assortHetFixed α (assortFreq g0) / 2)) := by
  have h := ((tendsto_assortOrbit_het h0 h1 g0).div_const 2).const_sub (assortFreq g0)
  refine h.congr (fun t => ?_)
  have := assortOrbit_freq α g0 t
  unfold assortFreq at this ⊢
  linarith

end Rhone.Dynamics.Assortative
