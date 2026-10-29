/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTime.Measurable

/-! # The real-time absorption law equals the sampling kernel -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTime

open Finset MeasureTheory ProbabilityTheory TwoLocusGenealogy TypedAncestralChain
  BranchLengthMoments ContinuousTimeGenealogy

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
  {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

theorem absorbing_bad_output (E : Set (TS n KA KB)) :
    Absorbing θA θB ρ {t | t.st.1 = ∅ ∧ t ∉ E} := by
  intro t ht
  exact absorbing_absorbed t ht.1

theorem ae_jump_hit_iff_terminal (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hw : WF s.st.1)
    (E : Set (TS n KA KB)) (hE : ∀ t ∈ E, t.st.1 = ∅) :
    ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s),
      (∃ k, ω k ∈ E) ↔ ω (absTime ω) ∈ E := by
  filter_upwards [ae_lt_absTime_iff h hθA hθB hw,
    ae_stay h (absorbing_bad_output E) s] with ω hω hstay
  constructor
  · rintro ⟨k, hk⟩
    have hfirst : (ω (absTime ω)).st.1 = ∅ := by
      by_contra hn
      have := (hω (absTime ω)).mpr hn
      exact (lt_irrefl _ this)
    have hle : absTime ω ≤ k := Nat.sInf_le (hE _ hk)
    by_contra hbad
    exact (stay_le (E := {t : TS n KA KB | t.st.1 = ∅ ∧ t ∉ E})
      hstay hle ⟨hfirst, hbad⟩).2 hk
  · intro ht
    exact ⟨absTime ω, ht⟩

theorem ae_process_hit_iff_jump_hit (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hw : WF s.st.1)
    (E : Set (TS n KA KB)) (hE : ∀ t ∈ E, t.st.1 = ∅) :
    ∀ᵐ z ∂(ctLaw θA θB ρ πA πB h s),
      (∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E) ↔ ∃ k, z.1 k ∈ E := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := argTrajT θA θB ρ πA πB h s) (ν := clocks)).ae
      (ae_jump_hit_iff_terminal h hθA hθB hw E hE)
  filter_upwards [hp] with z hz
  constructor
  · rintro ⟨t, _, ht⟩
    exact process_mem_implies_jump_mem z E ht
  · intro hk
    exact terminal_mem_implies_process_mem z E (hz.mp hk)

theorem measure_process_hit_eq_jump_hit (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hw : WF s.st.1)
    (E : Set (TS n KA KB)) (hE : ∀ t ∈ E, t.st.1 = ∅) :
    ctLaw θA θB ρ πA πB h s {z | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E}
      = argTrajT θA θB ρ πA πB h s {ω | ∃ k, ω k ∈ E} := by
  have heq : {z : CtPath n KA KB | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E}
      =ᵐ[ctLaw θA θB ρ πA πB h s] {z : CtPath n KA KB | ∃ k, z.1 k ∈ E} := by
    filter_upwards [ae_process_hit_iff_jump_hit h hθA hθB hw E hE] with z hz
    exact propext hz
  rw [measure_congr heq]
  have hset : {z : CtPath n KA KB | ∃ k, z.1 k ∈ E}
      = {ω | ∃ k, ω k ∈ E} ×ˢ Set.univ := by ext z; simp
  rw [ctLaw, hset, Measure.prod_prod, measure_univ, mul_one]

theorem measure_process_hit_eq_hitProb (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB}
    (hs : WFT s.st) (hf : Fits σA σB s.st) :
    ctLaw θA θB ρ πA πB h s
      {z | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ TFin σA σB}
      = ENNReal.ofReal (hitProb σA σB θA θB ρ πA πB s.st.1) := by
  rw [measure_process_hit_eq_jump_hit h hθA hθB hs.wf (TFin σA σB) (fun _ ht => ht.1)]
  exact measure_hit_ever_eq_hitProb h hθA hθB hs hf

theorem measure_process_hit_init_eq_q (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) :
    ctLaw θA θB ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)
      {z | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ TFin σA σB}
      = ENNReal.ofReal (LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB h.rho
        (cSample σA σB)) := by
  calc _ = argTrajT θA θB ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)
        {ω | ∃ k, ω k ∈ TFin σA σB} :=
      measure_process_hit_eq_jump_hit h hθA hθB
        (s := (⟨initT n KA KB⟩ : TS n KA KB)) initT_wft.wf (TFin σA σB)
        (fun _ ht => ht.1)
    _ = _ := measure_hit_ever_initT h hθA hθB

theorem measure_process_absorbed_eq_one (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hw : WF s.st.1) :
    ctLaw θA θB ρ πA πB h s
      {z | ∃ t : ℝ, 0 ≤ t ∧ (process θA θB ρ z t).st.1 = ∅} = 1 := by
  calc _ = argTrajT θA θB ρ πA πB h s {ω | ∃ k, (ω k).st.1 = ∅} :=
      measure_process_hit_eq_jump_hit h hθA hθB hw {t | t.st.1 = ∅} (fun _ ht => ht)
    _ = 1 := measure_absorbed_ever h hθA hθB hw

theorem ae_process_absorbed_forever (h : Adm θA θB ρ πA πB)
    (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hw : WF s.st.1) :
    ∀ᵐ z ∂(ctLaw θA θB ρ πA πB h s), ∃ τ : ℝ, 0 ≤ τ ∧
      ∀ t : ℝ, τ ≤ t → (process θA θB ρ z t).st.1 = ∅ := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := argTrajT θA θB ρ πA πB h s) (ν := clocks)).ae
    (ae_lt_absTime_iff h hθA hθB hw)
  filter_upwards [hp] with z hz
  refine ⟨arrival θA θB ρ z (absTime z.1), arrival_nonneg _ _, fun t ht => ?_⟩
  rw [process_after_absorption z ht]
  by_contra hn
  exact lt_irrefl _ ((hz (absTime z.1)).mpr hn)

end Rhone.Coalescent.ContinuousTime
