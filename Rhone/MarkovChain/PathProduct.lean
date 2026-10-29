/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Shift

/-! # Expectation of a product of functions of the first states of a finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
noncomputable def pathProduct : (N : ℕ) → (Fin N → S → ℝ) → S → ℝ
  | 0, _, _ => 1
  | N + 1, f, x => f 0 x * ∑ y, C.P x y * pathProduct N (fun k => f k.succ) y

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem pathProduct_zero (f : Fin 0 → S → ℝ) (x : S) : C.pathProduct 0 f x = 1 := rfl

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem pathProduct_succ (N : ℕ) (f : Fin (N + 1) → S → ℝ) (x : S) :
    C.pathProduct (N + 1) f x =
      f 0 x * ∑ y, C.P x y * C.pathProduct N (fun k => f k.succ) y := rfl

omit [DecidableEq S] in
theorem ae_eval_zero (x : S) : ∀ᵐ ω ∂C.pathLaw x, ω 0 = x := by
  have hm : MeasurableSet {y : S | y = x} := measurableSet_singleton x
  have h : ∀ᵐ y ∂(C.pathLaw x).map (fun ω => ω 0), y = x := by
    rw [show (C.pathLaw x).map (fun ω => ω 0) = Measure.dirac x from
      C.toProcess.map_eval_zero x]
    exact (ae_dirac_iff hm).2 rfl
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hm).1 h

omit [DecidableEq S] in
theorem integral_prod_eval (N : ℕ) (f : Fin N → S → ℝ) (x : S) :
    ∫ ω, ∏ k : Fin N, f k (ω k) ∂C.pathLaw x = C.pathProduct N f x := by
  induction N generalizing x with
  | zero => simp [pathProduct]
  | succ N ih =>
    set G : (ℕ → S) → ℝ := fun ω' => ∏ k : Fin N, f k.succ (ω' k) with hG
    have hGm : Measurable G :=
      Finset.measurable_prod _ fun k _ =>
        (Measurable.of_discrete (f := f k.succ)).comp (measurable_pi_apply (k : ℕ))
    have hGb : ∀ ω', ‖G ω'‖ ≤ ∏ k : Fin N, ∑ s, |f k.succ s| := by
      intro ω'
      rw [hG, Real.norm_eq_abs, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ =>
        Finset.single_le_sum (f := fun s => |f k.succ s|) (fun s _ => abs_nonneg _)
          (mem_univ (ω' k))
    have hGi : ∀ μ : Measure (ℕ → S), IsFiniteMeasure μ → Integrable G μ := fun μ _ =>
      Integrable.of_bound hGm.aestronglyMeasurable _ (ae_of_all _ hGb)
    have h1 : ∫ ω, ∏ k : Fin (N + 1), f k (ω k) ∂C.pathLaw x =
        ∫ ω, f 0 x * G (fun k => ω (1 + k)) ∂C.pathLaw x := by
      apply integral_congr_ae
      filter_upwards [C.ae_eval_zero x] with ω hω
      rw [Fin.prod_univ_succ, hG]
      congr 1
      · rw [Fin.val_zero, hω]
      · refine Finset.prod_congr rfl fun k _ => ?_
        rw [Fin.val_succ, Nat.add_comm]
    have h2 : ∫ ω, G (fun k => ω (1 + k)) ∂C.pathLaw x =
        ∫ ω', G ω' ∂(C.pathLaw x).map (fun ω k => ω (1 + k)) :=
      (integral_map (DiscreteProcess.measurable_shift 1).aemeasurable
        hGm.aestronglyMeasurable).symm
    have h3 : (C.pathLaw x).map (fun ω k => ω (1 + k)) =
        (C.toProcess.traj ∘ₖ C.kernel) x := by
      rw [Kernel.comp_apply]
      exact C.map_shift_one x
    have h4 : ∫ ω', G ω' ∂(C.toProcess.traj ∘ₖ C.kernel) x =
        ∫ y, ∫ ω', G ω' ∂C.toProcess.traj y ∂C.kernel x :=
      Kernel.integral_comp (hGi _ inferInstance)
    have h5 : ∀ y, ∫ ω', G ω' ∂C.toProcess.traj y = C.pathProduct N (fun k => f k.succ) y :=
      fun y => ih (fun k => f k.succ) y
    rw [h1, integral_const_mul, h2, h3, h4, integral_congr_ae (ae_of_all _ h5),
      integral_kernel, expect_apply, pathProduct_succ]

end Rhone.MarkovChain.FinChain
