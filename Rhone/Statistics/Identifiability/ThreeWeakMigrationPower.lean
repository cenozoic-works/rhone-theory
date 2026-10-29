/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeNoMigrationOverlap

/-! # Exact identifiability has no uniform finite-sample power as migration tends to zero -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeNoMigration

lemma weight_positive (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) : 0 < weight k c q := by
  unfold weight MarkovChain.Identifiability.totalMigration
  positivity

lemma weight_lt_one (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) : weight k c q < 1 := by
  have hm : 0 < MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  unfold weight
  apply (div_lt_one (mul_pos (by linarith) (by linarith))).mpr
  nlinarith [mul_pos hc hm, sq_nonneg (MarkovChain.Identifiability.totalMigration k q)]

lemma weight_zero (k : ℕ) {c : ℝ} (hc : 0 < c) : weight k c 0 = 1 := by
  simp [weight, MarkovChain.Identifiability.totalMigration, pow_two, hc.ne']

lemma weight_continuousAt_zero (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (weight k c) 0 := by
  unfold weight
  apply continuousAt_const.div
  · unfold MarkovChain.Identifiability.totalMigration
    fun_prop
  · simp [MarkovChain.Identifiability.totalMigration, hc.ne']

lemma weight_power_tendsto (k : ℕ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun q => (weight k c q) ^ N) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have ht : Tendsto (fun q => (weight k c q) ^ N)
      (𝓝 (0 : ℝ)) (𝓝 ((weight k c 0) ^ N)) := by
    convert! ((weight_continuousAt_zero k hc).pow N).tendsto using 1
  have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
  simpa only [weight_zero k hc, one_pow] using ht.mono_left hle

theorem no_uniform_iid_power (k : ℕ) {c : ℝ} (hc : 0 < c) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, 0 < q ∧ ∀ A : Set (Fin N → ℝ × ℝ), MeasurableSet A →
      1 - ε < (FinitePanelSampling.iidLaw (PanThreeSample.law (fun _ => c)) N).real A +
        (1 - (FinitePanelSampling.iidLaw (IslandThreeTimes.law k c q) N).real A) := by
  have hnear := (weight_power_tendsto k hc N).eventually
    (Ioi_mem_nhds (show 1 - ε < (1 : ℝ) by linarith))
  have hpos : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q := self_mem_nhdsWithin
  obtain ⟨q, hq, hw⟩ := (hpos.and hnear).exists
  exact ⟨q, hq, fun A hA => hw.trans_le (genealogy_iid_error_sum_lower_bound k hc hq N hA)⟩

theorem necessary_genealogy_sample_size (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (N : ℕ) {A : Set (Fin N → ℝ × ℝ)}
    (hA : MeasurableSet A) {α β : ℝ}
    (hα : (FinitePanelSampling.iidLaw (PanThreeSample.law (fun _ => c)) N).real A ≤ α)
    (hβ : 1 - (FinitePanelSampling.iidLaw (IslandThreeTimes.law k c q) N).real A ≤ β) :
    Real.log (α + β) / Real.log (weight k c q) ≤ (N : ℝ) := by
  have hnecessary : (weight k c q) ^ N ≤ α + β := by
    linarith [genealogy_iid_error_sum_lower_bound k hc hq N hA]
  have hw := weight_positive k hc hq.le
  have hlog := Real.log_le_log (pow_pos hw N) hnecessary
  rw [Real.log_pow] at hlog
  exact (div_le_iff_of_neg (Real.log_neg hw (weight_lt_one k hc hq))).mpr hlog

lemma weight_linear_lower_bound (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    1 - 3 * MarkovChain.Identifiability.totalMigration k q / c ≤ weight k c q := by
  have hm : 0 ≤ MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  have hden : 0 < (c + MarkovChain.Identifiability.totalMigration k q) *
      (c + 2 * MarkovChain.Identifiability.totalMigration k q) := by positivity
  have he : 1 - 3 * MarkovChain.Identifiability.totalMigration k q / c =
      (c - 3 * MarkovChain.Identifiability.totalMigration k q) / c := by
    field_simp
  rw [he, weight]
  apply (div_le_div_iff₀ hc hden).mpr
  nlinarith [mul_nonneg hc.le (sq_nonneg (MarkovChain.Identifiability.totalMigration k q)),
    mul_nonneg hm (sq_nonneg (MarkovChain.Identifiability.totalMigration k q))]

lemma weight_power_linear_lower_bound (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (N : ℕ) :
    1 - (N : ℝ) * (3 * MarkovChain.Identifiability.totalMigration k q / c) ≤ (weight k c q) ^ N :=
        by
  have hw := weight_nonnegative k hc.le hq
  calc
    _ = 1 + (N : ℝ) * ((1 - 3 * MarkovChain.Identifiability.totalMigration k q / c) - 1) := by ring
    _ ≤ 1 + (N : ℝ) * (weight k c q - 1) := by
      gcongr
      exact weight_linear_lower_bound k hc hq
    _ ≤ _ := one_add_mul_sub_le_pow (by linarith : -1 ≤ weight k c q) N

theorem necessary_randomized_sample_size_linear (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (N : ℕ) (f : (Fin N → ℝ × ℝ) → ℝ)
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {α β : ℝ}
    (hα : (∫ x, f x ∂FinitePanelSampling.iidLaw (PanThreeSample.law (fun _ => c)) N) ≤ α)
    (hβ : (∫ x, (1 - f x) ∂FinitePanelSampling.iidLaw (IslandThreeTimes.law k c q) N) ≤ β) :
    (1 - α - β) * c / (3 * MarkovChain.Identifiability.totalMigration k q) ≤ (N : ℝ) := by
  have h1 := genealogy_iid_randomized_error_sum_lower_bound k hc hq N f hf hb
  have h2 := weight_power_linear_lower_bound k hc hq.le N
  have h : 1 - (α + β) ≤ (N : ℝ) * (3 * MarkovChain.Identifiability.totalMigration k q / c) := by
    linarith
  have hm : 0 < MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  apply (div_le_iff₀ (mul_pos (by norm_num) hm)).mpr
  calc
    (1 - α - β) * c = (1 - (α + β)) * c := by ring
    _ ≤ (N : ℝ) * (3 * MarkovChain.Identifiability.totalMigration k q / c) * c :=
        mul_le_mul_of_nonneg_right h hc.le
    _ = (N : ℝ) * (3 * MarkovChain.Identifiability.totalMigration k q) := by field_simp

end Rhone.Statistics.Identifiability.ThreeNoMigration
