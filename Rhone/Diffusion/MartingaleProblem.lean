/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.Generator
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The martingale problem on continuous real paths

Source: ethier_kurtz1986, ch. 4, sec. 3. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Polynomial
open scoped NNReal BoundedContinuousFunction

/-- Source: ethier_kurtz1986, ch. 4, sec. 3. -/
structure IsMartingaleSolution (A : (ℝ → ℝ) → ℝ → ℝ) (D : Set (ℝ → ℝ)) (K : Set ℝ) (x : ℝ)
    (P : Measure C(ℝ≥0, ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  start : ∀ᵐ w ∂P, w 0 = x
  mem : ∀ᵐ w ∂P, ∀ t, w t ∈ K
  martingale : ∀ f ∈ D, ∀ s t : ℝ≥0, s ≤ t → ∀ (k : ℕ) (r : Fin k → ℝ≥0), (∀ j, r j ≤ s) →
    ∀ h : (Fin k → ℝ) →ᵇ ℝ,
      ∫ w, (f (w t) - f (w s) - ∫ u in (s : ℝ)..t, A f (w u.toNNReal)) * h (fun j => w (r j)) ∂P
        = 0

/-- Source: ethier_kurtz1986, ch. 10, sec. 1. -/
def IsWrightFisherDiffusionLaw (x : ℝ) (P : Measure C(ℝ≥0, ℝ)) : Prop :=
  IsMartingaleSolution wfGenerator polynomialFunctions (Set.Icc 0 1) x P

theorem IsMartingaleSolution.start_mem {A : (ℝ → ℝ) → ℝ → ℝ} {D : Set (ℝ → ℝ)} {K : Set ℝ}
    {x : ℝ} {P : Measure C(ℝ≥0, ℝ)} (h : IsMartingaleSolution A D K x P) : x ∈ K := by
  have := h.isProbabilityMeasure
  obtain ⟨w, hw0, hwK⟩ := (h.start.and h.mem).exists
  exact hw0 ▸ hwK 0

theorem isWrightFisherDiffusionLaw_dirac_zero :
    IsWrightFisherDiffusionLaw 0 (Measure.dirac (ContinuousMap.const ℝ≥0 (0 : ℝ))) where
  isProbabilityMeasure := inferInstance
  start := by simp
  mem := by simp
  martingale := by
    rintro f ⟨p, rfl⟩ s t - k r - h
    simp [wfGenerator]

theorem not_isWrightFisherDiffusionLaw_dirac_half :
    ¬ IsWrightFisherDiffusionLaw (1 / 2)
      (Measure.dirac (ContinuousMap.const ℝ≥0 (1 / 2 : ℝ))) := by
  intro h
  have hm := h.martingale (fun y => (X ^ 2 : ℝ[X]).eval y) ⟨X ^ 2, rfl⟩ 0 1 zero_le_one 0
    Fin.elim0 (fun j => j.elim0) (BoundedContinuousFunction.const _ 1)
  have hgen : ∀ y : ℝ, wfGenerator (fun y => (X ^ 2 : ℝ[X]).eval y) y = y * (1 - y) := by
    intro y
    rw [wfGenerator_eval]
    simp
    ring
  simp only [hgen] at hm
  simp at hm
  norm_num at hm

end Rhone.Diffusion
