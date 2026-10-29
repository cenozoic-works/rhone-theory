/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.Moments
public import Rhone.Statistics.LocalizedBetting.Budget

/-! # Fixed-sample localized test, with exact source-centred score and margin -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest ThreeSiteRobustness
open Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

def localizes {N : ℕ} (s : Fin 5 → ℝ) (f : Fin 5 → X → ℝ) (eps : ℝ)
    (z : Fin N → X) : Prop :=
  ∀ i : Fin 3, |sampleMean (f (i.castLE (by decide))) z - s (i.castLE (by decide))| ≤ eps

def factor (s : Fin 5 → ℝ) (f : Fin 5 → X → ℝ) (eta eps : ℝ) (x : X) : ℝ :=
  1 + eta * (contrast s (fun i => f i x) + (scoreVector s - 401520 * eps ^ 2))

def rejects {N : ℕ} (s : Fin 5 → ℝ) (f : Fin 5 → X → ℝ) (eta eps : ℝ)
    (z : Fin N → X) : Prop :=
  localizes s f eps z ∧ 20 ≤ productWealth (factor s f eta eps) z

theorem uniform_null_size (P : Law X) (s : Fin 5 → ℝ) (f : Fin 5 → X → ℝ)
    (hb : ∀ i x, -1 / 3 ≤ f i x ∧ f i x ≤ 1) {eta : ℝ} (heta : 0 ≤ eta)
    (hf : ∀ x, 0 ≤ factor s f eta (1 / 100000) x)
    (hnull : scoreVector (fun i => rejection P (f i)) ≤ 0)
    {N : ℕ} (hN : 72000000000 ≤ N) :
    probability (iid P N) (rejects s f eta (1 / 100000)) ≤ (1 : ℝ) / 20 := by
  let v : Fin 5 → ℝ := fun i => rejection P (f i)
  let near : Prop := |v 0 - s 0| ≤ 2 * (1 / 100000) ∧ |v 2 - s 2| ≤ 2 * (1 / 100000)
  apply localized_size P N (factor s f eta (1 / 100000))
    (localizes s f (1 / 100000)) near hf
  · intro hn
    have hm := local_null_margin s v (by norm_num : (0 : ℝ) ≤ 1 / 100000) hn.1 hn.2 hnull
    change rejection P (fun x => 1 + eta * (contrast s (fun i => f i x) +
      (scoreVector s - 401520 * (1 / 100000) ^ 2))) ≤ 1
    rw [affine_factor_mean, contrast_expectation]
    have h := mul_nonpos_of_nonneg_of_nonpos heta hm
    dsimp [v] at h
    linarith
  · intro hn
    have hsome : ∃ i : Fin 3,
        2 * (1 / 100000 : ℝ) < |v (i.castLE (by decide)) - s (i.castLE (by decide))| := by
      by_cases h0 : |v 0 - s 0| ≤ 2 * (1 / 100000)
      · exact ⟨2, lt_of_not_ge (fun h2 => hn ⟨h0, h2⟩)⟩
      · exact ⟨0, lt_of_not_ge h0⟩
    obtain ⟨i, hi⟩ := hsome
    have hsub : ∀ z : Fin N → X, localizes s f (1 / 100000) z →
        ∃ j : Fin 3, (1 / 100000 : ℝ) ≤
          |sampleMean (f (j.castLE (by decide))) z - rejection P (f (j.castLE (by decide)))| := by
      intro z hz
      refine ⟨i, ?_⟩
      have htriangle := abs_sub_le (v (i.castLE (by decide)))
        (sampleMean (f (i.castLE (by decide))) z) (s (i.castLE (by decide)))
      rw [abs_sub_comm (v (i.castLE (by decide)))
        (sampleMean (f (i.castLE (by decide))) z)] at htriangle
      have hloc := hz i
      dsimp [v] at *
      linarith
    have ht := range_four_thirds_concentration P (fun j : Fin 3 => f (j.castLE (by decide)))
      (fun j x => hb _ x) (show 0 < N by omega) (by norm_num : (0 : ℝ) ≤ 1 / 100000)
    norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at ht
    have h := (probability_mono _ hsub).trans ht
    have he := localization_budget hN
    linarith

end Rhone.Statistics.LocalizedBetting
