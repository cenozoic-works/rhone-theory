/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # Discrete-time Markov processes and their trajectory laws -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset Preorder

structure DiscreteProcess (S : Type*) [MeasurableSpace S] where
  step : Kernel S S
  [isMarkov : IsMarkovKernel step]

namespace DiscreteProcess

variable {S : Type*} [MeasurableSpace S] (P : DiscreteProcess S)

instance : IsMarkovKernel P.step := P.isMarkov

noncomputable def stepSeq (m : ℕ) : Kernel ((_ : Iic m) → S) S :=
  P.step.comap (fun x => x ⟨m, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (m : ℕ) : IsMarkovKernel (P.stepSeq m) := by
  rw [stepSeq]
  infer_instance

noncomputable def traj : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) P.stepSeq 0).comap (fun x _ => x)
    (measurable_pi_iff.2 fun _ => measurable_id)

instance : IsMarkovKernel P.traj := by
  rw [traj]
  infer_instance

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

instance (x : S) : IsProbabilityMeasure (P.pathLaw x) := by
  rw [pathLaw]
  infer_instance

noncomputable def law (μ₀ : Measure S) : Measure (ℕ → S) := μ₀.bind P.traj

theorem pathLaw_eq (x : S) :
    P.pathLaw x = Kernel.traj (X := fun _ => S) P.stepSeq 0 (fun _ => x) := rfl

theorem law_dirac (x : S) : P.law (Measure.dirac x) = P.pathLaw x := by
  rw [law, pathLaw, Measure.dirac_bind (Kernel.measurable _)]

private noncomputable def evalKer (n : ℕ) : Kernel ((_ : Iic 0) → S) S :=
  (Kernel.partialTraj (X := fun _ => S) P.stepSeq 0 n).map (fun y => y ⟨n, mem_Iic.2 le_rfl⟩)

private theorem map_eval_eq (n : ℕ) (x : S) :
    (P.pathLaw x).map (fun ω => ω n) = P.evalKer n (fun _ => x) := by
  rw [evalKer, Kernel.map_apply _ (measurable_pi_apply _), pathLaw_eq,
    ← Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => S) (κ := P.stepSeq) 0 n]
  exact (Measure.map_map (measurable_pi_apply (⟨n, mem_Iic.2 le_rfl⟩ : Iic n))
    (measurable_frestrictLe (X := fun _ : ℕ => S) n)).symm

private theorem evalKer_succ (n : ℕ) : P.evalKer (n + 1) = P.step ∘ₖ P.evalKer n := by
  rw [evalKer, evalKer,
    ← Kernel.partialTraj_comp_partialTraj (X := fun _ => S) (κ := P.stepSeq) (Nat.zero_le n)
      (Nat.le_succ n),
    Kernel.map_comp, Kernel.map_partialTraj_succ_self, stepSeq]
  exact (Kernel.comp_map _ _ (measurable_pi_apply (⟨n, mem_Iic.2 le_rfl⟩ : Iic n))).symm

theorem map_eval_zero (x : S) : (P.pathLaw x).map (fun ω => ω 0) = Measure.dirac x := by
  rw [map_eval_eq, evalKer, Kernel.map_apply _ (measurable_pi_apply _), Kernel.partialTraj_self,
    Kernel.id_apply]
  exact Measure.map_dirac' (measurable_pi_apply _) _

theorem map_eval_succ (n : ℕ) (x : S) :
    (P.pathLaw x).map (fun ω => ω (n + 1)) = ((P.pathLaw x).map (fun ω => ω n)).bind P.step := by
  rw [map_eval_eq, map_eval_eq, evalKer_succ, Kernel.comp_apply]

theorem measurable_eval_piLE (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] (fun ω : ℕ → S => ω n) := by
  have h : (fun ω : ℕ → S => ω n) =
      (fun y : (_ : Set.Iic n) → S => y ⟨n, Set.mem_Iic.2 le_rfl⟩) ∘
        restrictLe (π := fun _ : ℕ => S) n := rfl
  rw [h]
  exact (measurable_pi_apply _).comp (comap_measurable _)

theorem condExp_eval_succ (x : S) (n : ℕ) {g : S → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) :
    (P.pathLaw x)[fun ω => g (ω (n + 1)) | Filtration.piLE n] =ᵐ[P.pathLaw x]
      fun ω => ∫ y, g y ∂P.step (ω n) := by
  have hint : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (P.pathLaw x) :=
    Integrable.of_bound (hg.comp (measurable_pi_apply _)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa using hM (ω (n + 1)))
  have h := Kernel.condExp_traj (X := fun _ : ℕ => S) (κ := P.stepSeq) (Nat.zero_le n)
    (x₀ := fun _ => x) hint
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  have hmap := Kernel.map_traj_succ_self (X := fun _ : ℕ => S) (κ := P.stepSeq) (a := n)
  have h2 : (Kernel.traj (X := fun _ : ℕ => S) P.stepSeq n
      (frestrictLe (π := fun _ : ℕ => S) n ω)).map (fun y => y (n + 1)) = P.step (ω n) := by
    rw [← Kernel.map_apply _ (measurable_pi_apply _), hmap, stepSeq,
      Kernel.comap_apply]
    rfl
  change ∫ y : ℕ → S, g (y (n + 1)) ∂_ = ∫ y, g y ∂P.step (ω n)
  rw [← h2, integral_map (measurable_pi_apply _).aemeasurable hg.aestronglyMeasurable]

theorem setIntegral_eval_succ (x : S) (n : ℕ) {g : S → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) {B : Set (ℕ → S)}
    (hB : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B) :
    ∫ ω in B, g (ω (n + 1)) ∂P.pathLaw x = ∫ ω in B, ∫ y, g y ∂P.step (ω n) ∂P.pathLaw x := by
  have hint : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (P.pathLaw x) :=
    Integrable.of_bound (hg.comp (measurable_pi_apply _)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa using hM (ω (n + 1)))
  rw [← setIntegral_condExp (Filtration.piLE.le n) hint hB]
  exact setIntegral_congr_ae ((Filtration.piLE.le n) B hB)
    ((P.condExp_eval_succ x n hg hM).mono fun ω h _ => h)

end DiscreteProcess

end Rhone.MarkovChain
