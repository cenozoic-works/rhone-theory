/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Process
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # A drift criterion for discrete-time Markov processes in extended nonnegative reals -/
@[expose] public section

namespace Rhone.MarkovChain.IntervalProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem pathLaw_lintegral_eval_succ {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) (x : S) (n : ℕ)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ ω, ∫⁻ y, f y ∂P.step (ω n) ∂P.pathLaw x := by
  have h1 : ∫⁻ ω, f (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ y, f y ∂(P.pathLaw x).map (fun ω => ω (n + 1)) :=
    (lintegral_map hf (measurable_pi_apply (n + 1))).symm
  rw [h1, P.map_eval_succ,
    Measure.lintegral_bind (Kernel.measurable _).aemeasurable hf.aemeasurable,
    lintegral_map hf.lintegral_kernel (measurable_pi_apply n)]

theorem pathLaw_drift_le {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) {V c : S → ℝ≥0∞}
    (hV : Measurable V) (hc : Measurable c)
    (h : ∀ s, ∫⁻ y, V y ∂P.step s + c s ≤ V s) (x : S) (n : ℕ) :
    ∫⁻ ω, V (ω n) ∂P.pathLaw x +
      ∑ k ∈ Finset.range n, ∫⁻ ω, c (ω k) ∂P.pathLaw x ≤ V x := by
  induction n with
  | zero =>
    have h0 : ∫⁻ ω, V (ω 0) ∂P.pathLaw x = V x := by
      have hm := lintegral_map (μ := P.pathLaw x) hV (measurable_pi_apply 0)
      rw [P.map_eval_zero, lintegral_dirac' _ hV] at hm
      exact hm.symm
    simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, pathLaw_lintegral_eval_succ P x n hV]
    calc
      ∫⁻ ω, ∫⁻ y, V y ∂P.step (ω n) ∂P.pathLaw x +
          (∑ k ∈ Finset.range n, ∫⁻ ω, c (ω k) ∂P.pathLaw x +
            ∫⁻ ω, c (ω n) ∂P.pathLaw x) =
          ∫⁻ ω, (∫⁻ y, V y ∂P.step (ω n) + c (ω n)) ∂P.pathLaw x +
            ∑ k ∈ Finset.range n, ∫⁻ ω, c (ω k) ∂P.pathLaw x := by
        have hadd := lintegral_add_right (μ := P.pathLaw x)
          (fun ω : ℕ → S => ∫⁻ y, V y ∂P.step (ω n))
          (g := fun ω : ℕ → S => c (ω n)) (hc.comp (measurable_pi_apply n))
        rw [hadd]
        ring
      _ ≤ ∫⁻ ω, V (ω n) ∂P.pathLaw x +
            ∑ k ∈ Finset.range n, ∫⁻ ω, c (ω k) ∂P.pathLaw x :=
        add_le_add (lintegral_mono fun ω => h (ω n)) le_rfl
      _ ≤ V x := ih

theorem pathLaw_tsum_measure_le_of_drift {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) {V : S → ℝ≥0∞} (hV : Measurable V)
    {A : Set S} (hA : MeasurableSet A)
    (h : ∀ s, ∫⁻ y, V y ∂P.step s + A.indicator 1 s ≤ V s) (x : S) :
    ∑' k, P.pathLaw x {ω | ω k ∈ A} ≤ V x := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have hc : Measurable (A.indicator (1 : S → ℝ≥0∞)) := measurable_one.indicator hA
  have h1 := pathLaw_drift_le P hV hc h x n
  have h2 : ∀ k, ∫⁻ ω, A.indicator (1 : S → ℝ≥0∞) (ω k) ∂P.pathLaw x =
      P.pathLaw x {ω | ω k ∈ A} := by
    intro k
    have hm := lintegral_map (μ := P.pathLaw x) hc (measurable_pi_apply k)
    rw [lintegral_indicator_one hA,
      Measure.map_apply (measurable_pi_apply k) hA] at hm
    exact hm.symm
  simp only [h2] at h1
  exact le_trans le_add_self h1

theorem pathLaw_ae_exists_notMem_of_drift {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) {V : S → ℝ≥0∞} (hV : Measurable V)
    {A : Set S} (hA : MeasurableSet A)
    (h : ∀ s, ∫⁻ y, V y ∂P.step s + A.indicator 1 s ≤ V s)
    (x : S) (hx : V x ≠ ⊤) :
    ∀ᵐ ω ∂P.pathLaw x, ∃ K, ∀ k, K ≤ k → ω k ∉ A := by
  have hs : ∑' k, P.pathLaw x {ω | ω k ∈ A} ≠ ∞ :=
    ne_top_of_le_ne_top hx (pathLaw_tsum_measure_le_of_drift P hV hA h x)
  filter_upwards [ae_eventually_notMem hs] with ω hω
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hω
  exact ⟨K, fun k hk => hK k hk⟩

end Rhone.MarkovChain.IntervalProcess
