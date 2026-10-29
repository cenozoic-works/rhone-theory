/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GammaFeatureInterpolation

/-! # Fin-indexed positive weights and rates for literal finite-phase constructors -/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Rhone.Statistics.Identifiability.ErlangApproximation

theorem eventually_indexed_erlang_match {d : ℕ} (s : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, ∃ J : ℕ, 0 < J ∧ J ≤ d + 1 ∧
      ∃ w r : Fin J → ℝ, (∀ j, 0 < w j) ∧ (∀ j, 0 < r j) ∧
        ∑ j, w j = 1 ∧
        ∀ i, ∑ j, w j * (r j / (r j + s i)) ^ (n + 2) = a / (a + s i) := by
  classical
  filter_upwards [eventually_exponential_rate_match s hs ha] with n hn
  obtain ⟨t, w, r, hne, hc, hw, hr, hsum, heq⟩ := hn
  let J := Fintype.card t
  let e : Fin J ≃ t := (Fintype.equivFin t).symm
  have hJ : J = t.card := Fintype.card_coe t
  have hsum_eq (f : (Fin d → ℝ) → ℝ) : (∑ j : Fin J, f (e j)) = ∑ y ∈ t, f y := by
    rw [← Finset.sum_coe_sort t f]
    exact e.sum_comp (fun y : t => f y)
  refine ⟨J, ?_, ?_, (fun j => w (e j)), (fun j => r (e j)),
    (fun j => hw _ (e j).property), (fun j => hr _ (e j).property), ?_, ?_⟩
  · rw [hJ]
    exact Finset.card_pos.mpr hne
  · rwa [hJ]
  · rw [hsum_eq]
    exact hsum
  · intro i
    exact (hsum_eq (fun y => w y * (r y / (r y + s i)) ^ (n + 2))).trans (heq i)

end Rhone.Statistics.Identifiability.ErlangApproximation
