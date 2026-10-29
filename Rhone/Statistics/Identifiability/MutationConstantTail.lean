/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationPulseKernel
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Canonical infinite-horizon payoff for a constant discounted finite generator -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology

namespace Rhone.Statistics.Identifiability.MutationConstantTail
open MutationPulseKernel

noncomputable def survival (δ r k t : ℝ) : Fin 5 → ℝ :=
  NormedSpace.exp (t • B δ r k) *ᵥ (fun _ => 1)

noncomputable def tailPayoff (δ r k : ℝ) (i : Fin 5) : ℝ :=
  ⨅ t : ℝ, survival δ r k (max t 0) i

theorem survival_nonneg {δ r k t : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (i : Fin 5) : 0 ≤ survival δ r k t i := by
  simp only [survival, Matrix.mulVec, dotProduct, mul_one]
  exact Finset.sum_nonneg fun j _ => exp_B_nonneg hδ hr ht i j

theorem survival_le_one {δ r k t : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (ht : 0 ≤ t) (i : Fin 5) : survival δ r k t i ≤ 1 :=
  exp_B_row_le_one hδ hr hk ht i

@[simp] theorem survival_zero (δ r k : ℝ) : survival δ r k 0 = fun _ => 1 := by
  simp [survival]

@[simp] theorem survival_absorbing (δ r k t : ℝ) : survival δ r k t 4 = 1 := by
  simp only [survival, Matrix.mulVec, dotProduct, exp_B_absorbing_row, mul_one]
  simp [Matrix.one_apply]

theorem survival_add (δ r k s t : ℝ) :
    survival δ r k (s + t) = NormedSpace.exp (s • B δ r k) *ᵥ survival δ r k t := by
  unfold survival
  rw [add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl (B δ r k)).smul_left s).smul_right t), Matrix.mulVec_mulVec]

theorem survival_antitoneOn {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (i : Fin 5) : AntitoneOn (fun t => survival δ r k t i) (Set.Ici 0) := by
  intro s hs t _ hst
  have ht : 0 ≤ t - s := sub_nonneg.mpr hst
  have he : t = s + (t - s) := by ring
  change survival δ r k t i ≤ survival δ r k s i
  rw [he, survival_add]
  exact mulVec_mono (NormedSpace.exp (s • B δ r k)) (exp_B_nonneg hδ hr hs)
    (fun j => survival_le_one hδ hr hk ht j) i

theorem survival_clipped_bddBelow {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (i : Fin 5) : BddBelow (Set.range (fun t : ℝ => survival δ r k (max t 0) i)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact survival_nonneg hδ hr (le_max_right t 0) i

theorem tailPayoff_nonneg {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (i : Fin 5) : 0 ≤ tailPayoff δ r k i := by
  exact le_ciInf fun t => survival_nonneg hδ hr (le_max_right t 0) i

theorem tailPayoff_le_one {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (i : Fin 5) : tailPayoff δ r k i ≤ 1 := by
  have h := ciInf_le (survival_clipped_bddBelow (k := k) hδ hr i) (0 : ℝ)
  simpa [tailPayoff] using h

@[simp] theorem tailPayoff_absorbing (δ r k : ℝ) : tailPayoff δ r k 4 = 1 := by
  simp [tailPayoff]

theorem tailPayoff_admissible {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) :
    (∀ i, 0 ≤ tailPayoff δ r k i) ∧ (∀ i, tailPayoff δ r k i ≤ 1) ∧
      tailPayoff δ r k 4 = 1 :=
  ⟨tailPayoff_nonneg hδ hr, tailPayoff_le_one hδ hr, tailPayoff_absorbing δ r k⟩

theorem survival_tendsto_tailPayoff {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (i : Fin 5) :
    Filter.Tendsto (fun t : ℝ => survival δ r k t i) Filter.atTop
      (𝓝 (tailPayoff δ r k i)) := by
  have hanti : Antitone (fun t : ℝ => survival δ r k (max t 0) i) := by
    intro s t hst
    exact survival_antitoneOn hδ hr hk i (le_max_right s 0) (le_max_right t 0)
      (max_le_max_right 0 hst)
  have hlim := tendsto_atTop_ciInf hanti (survival_clipped_bddBelow (k := k) hδ hr i)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp [max_eq_left ht]

theorem survival_tendsto_tailPayoff_vector {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hk : 0 ≤ k) :
    Filter.Tendsto (survival δ r k) Filter.atTop (𝓝 (tailPayoff δ r k)) := by
  exact tendsto_pi_nhds.mpr (survival_tendsto_tailPayoff hδ hr hk)

theorem tailPayoff_harmonic {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (s : ℝ) :
    NormedSpace.exp (s • B δ r k) *ᵥ tailPayoff δ r k = tailPayoff δ r k := by
  have hlim := survival_tendsto_tailPayoff_vector hδ hr hk
  have hc : Continuous (fun v : Fin 5 → ℝ => NormedSpace.exp (s • B δ r k) *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hl := hc.continuousAt.tendsto.comp hlim
  have hshift : Filter.Tendsto (fun t : ℝ => s + t) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr fun b => ?_
    filter_upwards [Filter.eventually_ge_atTop (b - s)] with t ht
    linarith
  have hr' := hlim.comp hshift
  have heq : (fun t : ℝ => NormedSpace.exp (s • B δ r k) *ᵥ survival δ r k t) =
      fun t : ℝ => survival δ r k (s + t) := by
    funext t
    exact (survival_add δ r k s t).symm
  change Filter.Tendsto (fun t : ℝ => NormedSpace.exp (s • B δ r k) *ᵥ survival δ r k t)
    Filter.atTop (𝓝 (NormedSpace.exp (s • B δ r k) *ᵥ tailPayoff δ r k)) at hl
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr'

end Rhone.Statistics.Identifiability.MutationConstantTail
