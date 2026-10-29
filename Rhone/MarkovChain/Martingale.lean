/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Hitting
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.HittingTime

/-! # Martingales from harmonic functions and optional stopping -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {h : S → ℝ}

theorem IsHarmonic.martingale (hh : C.IsHarmonic h) (x : S) :
    Martingale (fun n (ω : ℕ → S) => h (ω n)) (Filtration.piLE (X := fun _ : ℕ => S))
      (C.pathLaw x) := by
  refine martingale_of_setIntegral_eq_succ (fun n => ?_) (fun n => C.integrable_eval h n x)
    fun n B hB => ?_
  · exact ((Measurable.of_discrete (f := h)).comp
      (DiscreteProcess.measurable_eval_piLE (S := S) n)).stronglyMeasurable
  · rw [C.setIntegral_eval_succ x n h hB, hh]

private theorem IsHarmonic.le_integral_stoppedProcess (hh : C.IsHarmonic h)
    (x : S) {τ : (ℕ → S) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ) (N : ℕ) :
    h x ≤ ∫ ω, stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω ∂C.pathLaw x := by
  classical
  have hsub := ((hh.martingale x).submartingale).stoppedProcess hτ
  have hle := hsub.setIntegral_le (Nat.zero_le N) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hle
  have h0 : ∫ ω, stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ 0 ω ∂C.pathLaw x = h x := by
    have : stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ 0 = fun ω => h (ω 0) := by
      funext ω
      exact stoppedProcess_eq_of_le (by simp)
    rw [this, C.integral_eval 0 h x, expectN_zero]
  rwa [h0] at hle

theorem IsHarmonic.integral_stoppedProcess (hh : C.IsHarmonic h) (x : S)
    {τ : (ℕ → S) → WithTop ℕ} (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ)
    (N : ℕ) :
    ∫ ω, stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω ∂C.pathLaw x = h x := by
  have hneg : C.IsHarmonic (-h) := by
    have := (C.isHarmonic_const 0).sub hh
    simpa [Pi.neg_def, Pi.sub_def] using this
  have h1 := hh.le_integral_stoppedProcess x hτ N
  have h2 := hneg.le_integral_stoppedProcess x hτ N
  have e : (fun ω => stoppedProcess (fun n (ω : ℕ → S) => (-h) (ω n)) τ N ω) =
      fun ω => -stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω := rfl
  rw [e, integral_neg] at h2
  simp only [Pi.neg_apply] at h2
  linarith

theorem IsHarmonic.integral_stoppedValue (hh : C.IsHarmonic h) (x : S)
    {τ : (ℕ → S) → WithTop ℕ} (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S)) τ)
    (hfin : ∀ᵐ ω ∂C.pathLaw x, τ ω ≠ ⊤) :
    ∫ ω, stoppedValue (fun n (ω : ℕ → S) => h (ω n)) τ ω ∂C.pathLaw x = h x := by
  have hsub := ((hh.martingale x).submartingale).stoppedProcess hτ
  have hbound : ∀ N, ∀ᵐ ω ∂C.pathLaw x,
      ‖stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω‖ ≤ ∑ z, |h z| := fun N =>
    Eventually.of_forall fun ω => (Real.norm_eq_abs _).le.trans
      (Finset.single_le_sum (f := fun z => |h z|) (fun _ _ => abs_nonneg _) (mem_univ _))
  have hlim : ∀ᵐ ω ∂C.pathLaw x,
      Tendsto (fun N => stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω) atTop
        (𝓝 (stoppedValue (fun n (ω : ℕ → S) => h (ω n)) τ ω)) := by
    filter_upwards [hfin] with ω hω
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hω
    refine tendsto_atTop_of_eventually_const (i₀ := k) fun N hN => ?_
    exact stoppedProcess_eq_of_ge (by rw [← hk]; exact_mod_cast hN)
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => ∑ z, |h z|)
    (fun N => (hsub.integrable N).aestronglyMeasurable) (integrable_const _) hbound hlim
  have hconst : (fun N => ∫ ω, stoppedProcess (fun n (ω : ℕ → S) => h (ω n)) τ N ω
      ∂C.pathLaw x) = fun _ => h x := funext fun N => hh.integral_stoppedProcess x hτ N
  rw [hconst] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem IsHarmonic.integral_stoppedValue_hitting [DecidableEq S] (hh : C.IsHarmonic h)
    {A : Finset S} (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∫ ω, stoppedValue (fun n (ω : ℕ → S) => h (ω n))
      (hittingAfter (fun n (ω : ℕ → S) => ω n) (A : Set S) 0) ω ∂C.pathLaw x = h x := by
  refine hh.integral_stoppedValue x ?_ ?_
  · exact Adapted.isStoppingTime_hittingAfter
      (fun n => DiscreteProcess.measurable_eval_piLE (S := S) n) MeasurableSet.of_discrete
  · filter_upwards [ae_exists_mem hA hR x] with ω ⟨n, hn⟩ htop
    exact (hittingAfter_eq_top_iff.1 htop) n (Nat.zero_le n) (by simpa using hn)

end Rhone.MarkovChain.FinChain
