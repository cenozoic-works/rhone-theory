/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateChain
public import Rhone.MarkovChain.HittingTime
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.ProductMeasure

/-! # The jump-and-hold path of a continuous-time chain -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

theorem lintegral_ofReal_expMeasure_one : ∫⁻ t, ENNReal.ofReal t ∂expMeasure 1 = 1 := by
  have hpt : ∀ t : ℝ, gammaPDF 1 1 t * ENNReal.ofReal t = gammaPDF 2 1 t := by
    intro t
    rw [gammaPDF_eq, gammaPDF_eq]
    by_cases ht : 0 ≤ t
    · simp only [ht, ↓reduceIte]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h21 : (2 : ℝ) - 1 = 1 := by norm_num
      simp [Real.Gamma_one, h21]
      ring
    · simp [ht, ENNReal.ofReal_of_nonpos (not_le.1 ht).le]
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hm ENNReal.measurable_ofReal]
  simp only [Pi.mul_apply, hpt]
  exact lintegral_gammaPDF_eq_one two_pos one_pos

noncomputable def clockLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => expMeasure 1

instance : IsProbabilityMeasure clockLaw := by
  rw [clockLaw]
  infer_instance

theorem lintegral_ofReal_clockLaw (k : ℕ) : ∫⁻ e, ENNReal.ofReal (e k) ∂clockLaw = 1 := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) k
  rw [← lintegral_ofReal_expMeasure_one, ← h,
    lintegral_map ENNReal.measurable_ofReal (measurable_pi_apply k)]
  rfl

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in
noncomputable def holdTime (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) : ℝ := p.2 k / R.rate (p.1 k)

omit [DecidableEq S] in
noncomputable def jumpTime (p : (ℕ → S) × (ℕ → ℝ)) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, R.holdTime p k

noncomputable def costBefore (A : Finset S) (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  ∑' k, if p.1 k ∈ A then 0 else ENNReal.ofReal (c (p.1 k) * R.holdTime p k)

noncomputable def timeBefore (A : Finset S) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  R.costBefore A (fun _ => 1) p

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def jumpHoldLaw (x : S) : Measure ((ℕ → S) × (ℕ → ℝ)) :=
  (R.jumpChain.pathLaw x).prod clockLaw

instance (x : S) : IsProbabilityMeasure (R.jumpHoldLaw x) := by
  rw [jumpHoldLaw]
  infer_instance

variable {R} {A : Finset S}

theorem lintegral_costBefore (hA : R.jumpChain.IsAbsorbingSet A) (hR : R.jumpChain.Reaches A)
    {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (x : S) :
    ∫⁻ p, R.costBefore A c p ∂R.jumpHoldLaw x = ENNReal.ofReal (R.expectedCost A c x) := by
  set φ : S → ℝ≥0∞ := fun y => if y ∈ A then 0 else ENNReal.ofReal (c y / R.rate y) with hφ
  have hterm : ∀ (k : ℕ) (p : (ℕ → S) × (ℕ → ℝ)),
      (if p.1 k ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal (c (p.1 k) * R.holdTime p k)) =
        φ (p.1 k) * ENNReal.ofReal (p.2 k) := by
    intro k p
    by_cases hp : p.1 k ∈ A
    · simp [hφ, hp]
    · simp only [hφ, hp, ↓reduceIte, holdTime]
      rw [← ENNReal.ofReal_mul (div_nonneg (hc _) (R.rate_nonneg _))]
      congr 1
      ring
  have hmφ : ∀ k : ℕ, Measurable fun ω : ℕ → S => φ (ω k) := fun k =>
    (Measurable.of_discrete (f := φ)).comp (measurable_pi_apply k)
  have hme : ∀ k : ℕ, Measurable fun e : ℕ → ℝ => ENNReal.ofReal (e k) := fun k =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply k)
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun p : (ℕ → S) × (ℕ → ℝ) => φ (p.1 k) * ENNReal.ofReal (p.2 k)) (R.jumpHoldLaw x) :=
    fun k => (((hmφ k).comp measurable_fst).mul ((hme k).comp measurable_snd)).aemeasurable
  have hk : ∀ k : ℕ, ∫⁻ p : (ℕ → S) × (ℕ → ℝ), φ (p.1 k) * ENNReal.ofReal (p.2 k)
      ∂R.jumpHoldLaw x = ∫⁻ ω, φ (ω k) ∂R.jumpChain.pathLaw x := by
    intro k
    rw [jumpHoldLaw, lintegral_prod_mul (hmφ k).aemeasurable (hme k).aemeasurable,
      lintegral_ofReal_clockLaw, mul_one]
  unfold costBefore
  simp only [hterm]
  rw [lintegral_tsum hmeas]
  simp only [hk]
  rw [← lintegral_tsum fun k => (hmφ k).aemeasurable]
  exact FinChain.lintegral_pathCost hA hR
    (fun y => div_nonneg (hc y) (R.rate_nonneg y)) x

theorem lintegral_timeBefore (hA : R.jumpChain.IsAbsorbingSet A) (hR : R.jumpChain.Reaches A)
    (x : S) :
    ∫⁻ p, R.timeBefore A p ∂R.jumpHoldLaw x = ENNReal.ofReal (R.expectedTime A x) :=
  lintegral_costBefore hA hR (fun _ => zero_le_one) x

end RateChain

end Rhone.MarkovChain
