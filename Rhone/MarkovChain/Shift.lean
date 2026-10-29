/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.LumpingTrajectory

/-! # The Markov property in shift form, for finite chains -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset

namespace DiscreteProcess

variable {S : Type*} [MeasurableSpace S] (P : DiscreteProcess S)

omit P in
theorem measurable_shift (n : ℕ) : Measurable fun (ω : ℕ → S) (k : ℕ) => ω (n + k) :=
  measurable_pi_iff.2 fun k => measurable_pi_apply (n + k)

theorem map_shift_of_one
    (h1 : ∀ y, (P.pathLaw y).map (fun ω k => ω (1 + k)) = (P.step y).bind P.traj)
    (x : S) (n : ℕ) :
    (P.pathLaw x).map (fun ω k => ω (n + k)) =
      ((P.pathLaw x).map (fun ω => ω n)).bind P.traj := by
  induction n with
  | zero =>
    rw [map_eval_zero, Measure.dirac_bind (Kernel.measurable _)]
    have h : (fun (ω : ℕ → S) (k : ℕ) => ω (0 + k)) = id := by
      funext ω k
      simp
    rw [h, Measure.map_id]
    rfl
  | succ n ih =>
    have hcomp : (fun (ω : ℕ → S) (k : ℕ) => ω (n + 1 + k)) =
        (fun ω k => ω (1 + k)) ∘ fun ω k => ω (n + k) := by
      funext ω k
      simp [Nat.add_assoc]
    have hk : P.traj.map (fun ω k => ω (1 + k)) = P.traj ∘ₖ P.step := by
      ext y : 1
      rw [Kernel.map_apply _ (measurable_shift 1), Kernel.comp_apply]
      exact h1 y
    rw [hcomp, ← Measure.map_map (measurable_shift 1) (measurable_shift n), ih, map_eval_succ]
    change (P.traj ∘ₘ (P.pathLaw x).map fun ω => ω n).map (fun ω k => ω (1 + k)) =
      P.traj ∘ₘ (P.step ∘ₘ (P.pathLaw x).map fun ω => ω n)
    rw [Measure.map_comp _ _ (measurable_shift 1), hk, Measure.comp_assoc]

end DiscreteProcess

namespace FinChain

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

omit [Fintype S] [DecidableEq S] in
theorem measurableSet_cylinder_eq (z : ℕ → S) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | ∀ i ≤ n, ω i = z i} := by
  have h : {ω : ℕ → S | ∀ i ≤ n, ω i = z i} =
      ⋂ i, ⋂ (_ : i ≤ n), (fun ω : ℕ → S => ω i) ⁻¹' {z i} := by
    ext ω
    simp
  rw [h]
  exact .iInter fun i => .iInter fun _ => measurable_pi_apply i (measurableSet_singleton _)

omit [DecidableEq S] in
theorem map_shift_one (y : S) :
    (C.pathLaw y).map (fun ω k => ω (1 + k)) = (C.kernel y).bind C.toProcess.traj := by
  classical
  have hprob : IsProbabilityMeasure ((C.kernel y).bind C.toProcess.traj) := by
    infer_instance
  have hofReal : ∀ (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ] (s : Set (ℕ → S)),
      μ s = ENNReal.ofReal (μ.real s) := fun μ _ s =>
    (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
  refine measure_ext_of_cylinder fun n z => ?_
  have hs := measurableSet_cylinder_eq z n
  set z' : ℕ → S := fun i => Nat.casesOn i y z with hz'
  have hE : (C.pathLaw y) {ω : ℕ → S | ω 0 = y}ᶜ = 0 := by
    have hm : MeasurableSet {ω : ℕ → S | ω 0 = y} := by
      change MeasurableSet ((fun ω : ℕ → S => ω 0) ⁻¹' {y})
      exact measurable_pi_apply 0 (measurableSet_singleton y)
    rw [prob_compl_eq_zero_iff hm]
    have h := congrArg (fun μ : Measure S => μ {y}) (C.toProcess.map_eval_zero y)
    simp only [Measure.dirac_apply' _ (measurableSet_singleton y), Set.indicator_of_mem,
      Set.mem_singleton_iff, Pi.one_apply] at h
    rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton y)] at h
    exact h
  have hset : {ω : ℕ → S | ∀ i ≤ n + 1, ω i = z' i} =
      (fun (ω : ℕ → S) (k : ℕ) => ω (1 + k)) ⁻¹' {ω | ∀ i ≤ n, ω i = z i} ∩ {ω | ω 0 = y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, h 0 (Nat.zero_le _)⟩
      have := h (i + 1) (Nat.succ_le_succ hi)
      rw [Nat.add_comm 1 i]
      exact this
    · rintro ⟨h1, h2⟩ i hi
      rcases i with _ | i
      · exact h2
      · have := h1 i (Nat.le_of_succ_le_succ hi)
        rw [Nat.add_comm 1 i] at this
        exact this
  have hL : (C.pathLaw y).map (fun ω k => ω (1 + k)) {ω | ∀ i ≤ n, ω i = z i} =
      ENNReal.ofReal (C.P y (z 0) * ∏ i ∈ range n, C.P (z i) (z (i + 1))) := by
    rw [Measure.map_apply (DiscreteProcess.measurable_shift 1) hs,
      ← measure_inter_conull hE, ← hset, hofReal, pathLaw_real_cylinder C y z' (n + 1),
      Finset.prod_range_succ']
    simp [hz', mul_comm]
  have hR : ((C.kernel y).bind C.toProcess.traj) {ω | ∀ i ≤ n, ω i = z i} =
      ENNReal.ofReal (C.P y (z 0) * ∏ i ∈ range n, C.P (z i) (z (i + 1))) := by
    rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_fintype,
      Finset.sum_eq_single (z 0)]
    · change (C.pathLaw (z 0)) _ * _ = _
      rw [hofReal, pathLaw_real_cylinder C (z 0) z n, kernel_apply_singleton,
        ← ENNReal.ofReal_mul (by
          rw [← pathLaw_real_cylinder C (z 0) z n]
          exact measureReal_nonneg)]
      congr 1
      simp [mul_comm]
    · intro w _ hw
      change (C.pathLaw w) _ * _ = 0
      rw [hofReal, pathLaw_real_cylinder C w z n]
      simp [hw]
    · exact fun h => (h (mem_univ _)).elim
  rw [hL, hR]

omit [DecidableEq S] in
theorem map_shift (x : S) (n : ℕ) :
    (C.pathLaw x).map (fun ω k => ω (n + k)) =
      ((C.pathLaw x).map (fun ω => ω n)).bind C.toProcess.traj :=
  C.toProcess.map_shift_of_one C.map_shift_one x n

theorem pathLaw_real_shift (x : S) (n : ℕ) {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    (C.pathLaw x).real {ω | (fun k => ω (n + k)) ∈ B} =
      ∑ y, C.stepN n x y * (C.pathLaw y).real B := by
  have h := congrArg (fun μ : Measure (ℕ → S) => μ B) (C.map_shift x n)
  simp only [Measure.map_apply (DiscreteProcess.measurable_shift n) hB] at h
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), lintegral_fintype] at h
  simp only [map_eval_singleton] at h
  rw [measureReal_def]
  change ((C.pathLaw x) ((fun (ω : ℕ → S) (k : ℕ) => ω (n + k)) ⁻¹' B)).toReal = _
  rw [h, ENNReal.toReal_sum fun y _ => ENNReal.mul_ne_top (measure_ne_top _ _)
    ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (C.stepN_nonneg n x y), mul_comm]
  rfl

end FinChain

end Rhone.MarkovChain
