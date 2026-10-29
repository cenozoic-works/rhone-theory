/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Absorption
public import Rhone.MarkovChain.Process
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # The trajectory law of a finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem sum_ofReal_P (x : S) : ∑ y, ENNReal.ofReal (C.P x y) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => C.nonneg x y, C.row_sum, ENNReal.ofReal_one]

noncomputable def stepPMF (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (C.P x y)) (C.sum_ofReal_P x)

noncomputable def kernel : Kernel S S where
  toFun x := (C.stepPMF x).toMeasure
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel C.kernel :=
  ⟨fun x => by change IsProbabilityMeasure (C.stepPMF x).toMeasure; infer_instance⟩

omit [DecidableEq S] in
theorem kernel_apply_singleton (x y : S) : C.kernel x {y} = ENNReal.ofReal (C.P x y) := by
  change (C.stepPMF x).toMeasure {y} = _
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rfl

omit [DecidableEq S] in
theorem kernel_real_singleton (x y : S) : (C.kernel x).real {y} = C.P x y := by
  rw [measureReal_def, kernel_apply_singleton, ENNReal.toReal_ofReal (C.nonneg x y)]

omit [DecidableEq S] in
theorem integral_kernel (f : S → ℝ) (x : S) : ∫ y, f y ∂C.kernel x = C.expect f x := by
  rw [integral_fintype Integrable.of_finite, expect_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [kernel_real_singleton, smul_eq_mul]

noncomputable def toProcess : DiscreteProcess S := ⟨C.kernel⟩

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := C.toProcess.pathLaw x

instance (x : S) : IsProbabilityMeasure (C.pathLaw x) := by
  rw [pathLaw]
  infer_instance

theorem map_eval_singleton (n : ℕ) (x y : S) :
    (C.pathLaw x).map (fun ω => ω n) {y} = ENNReal.ofReal (C.stepN n x y) := by
  induction n generalizing y with
  | zero =>
    rw [pathLaw, DiscreteProcess.map_eval_zero, Measure.dirac_apply' _ MeasurableSet.of_discrete,
      stepN_zero, Matrix.one_apply]
    by_cases h : x = y <;> simp [h]
  | succ n ih =>
    rw [pathLaw, DiscreteProcess.map_eval_succ,
      Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _), lintegral_fintype]
    change ∑ z, C.kernel z {y} * (C.pathLaw x).map (fun ω => ω n) {z} = _
    simp only [kernel_apply_singleton, ih]
    rw [stepN_succ', Matrix.mul_apply, ENNReal.ofReal_sum_of_nonneg fun z _ =>
      mul_nonneg (C.stepN_nonneg n x z) (C.nonneg z y)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ENNReal.ofReal_mul (C.stepN_nonneg n x z), mul_comm]

theorem pathLaw_real_eval (n : ℕ) (x y : S) :
    (C.pathLaw x).real {ω | ω n = y} = C.stepN n x y := by
  have h := C.map_eval_singleton n x y
  rw [Measure.map_apply (measurable_pi_apply n) MeasurableSet.of_discrete] at h
  have hset : {ω : ℕ → S | ω n = y} = (fun ω => ω n) ⁻¹' {y} := rfl
  rw [measureReal_def, hset, h, ENNReal.toReal_ofReal (C.stepN_nonneg n x y)]

theorem pathLaw_real_eval_mem (n : ℕ) (x : S) (A : Finset S) :
    (C.pathLaw x).real {ω | ω n ∈ A} = ∑ a ∈ A, C.stepN n x a := by
  have hset : {ω : ℕ → S | ω n ∈ A} = ⋃ a ∈ A, (fun ω : ℕ → S => ω n) ⁻¹' {a} := by
    ext ω
    simp
  rw [hset, measureReal_biUnion_finset
    (fun a _ b _ hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb))
    (fun a _ => (measurable_pi_apply n) (MeasurableSet.of_discrete (s := {a})))]
  exact Finset.sum_congr rfl fun a _ => C.pathLaw_real_eval n x a

theorem pathLaw_real_eval_notMem (n : ℕ) (x : S) (A : Finset S) :
    (C.pathLaw x).real {ω | ω n ∉ A} = C.survival A n x := by
  have h := C.pathLaw_real_eval_mem n x Aᶜ
  simpa [survival] using h

omit [DecidableEq S] in
theorem integrable_eval (f : S → ℝ) (n : ℕ) (x : S) :
    Integrable (fun ω : ℕ → S => f (ω n)) (C.pathLaw x) :=
  Integrable.of_bound
    ((Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)).aestronglyMeasurable
    (∑ z, |f z|) (Filter.Eventually.of_forall fun ω => (Real.norm_eq_abs _).le.trans
      (Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _) (mem_univ (ω n))))

theorem integral_eval (n : ℕ) (f : S → ℝ) (x : S) :
    ∫ ω, f (ω n) ∂C.pathLaw x = C.expectN n f x := by
  have hmap : ∫ ω, f (ω n) ∂C.pathLaw x = ∫ y, f y ∂(C.pathLaw x).map (fun ω => ω n) :=
    (integral_map (measurable_pi_apply n).aemeasurable
      (Measurable.of_discrete (f := f)).aestronglyMeasurable).symm
  rw [hmap, integral_fintype Integrable.of_finite, expectN_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [measureReal_def, map_eval_singleton, ENNReal.toReal_ofReal (C.stepN_nonneg n x y),
    smul_eq_mul]

omit [DecidableEq S] in
theorem setIntegral_eval_succ (x : S) (n : ℕ) (g : S → ℝ) {B : Set (ℕ → S)}
    (hB : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B) :
    ∫ ω in B, g (ω (n + 1)) ∂C.pathLaw x = ∫ ω in B, C.expect g (ω n) ∂C.pathLaw x := by
  have hM : ∀ y, |g y| ≤ ∑ z, |g z| := fun y =>
    Finset.single_le_sum (f := fun z => |g z|) (fun z _ => abs_nonneg _) (mem_univ y)
  rw [pathLaw, C.toProcess.setIntegral_eval_succ x n Measurable.of_discrete hM hB]
  exact setIntegral_congr_fun ((Filtration.piLE.le n) B hB) fun ω _ => C.integral_kernel g (ω n)

end Rhone.MarkovChain.FinChain
