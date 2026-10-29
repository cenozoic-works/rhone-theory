/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.KernelT

/-! # Finite-dimensional distributions of the trajectory measure -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory
open Preorder

variable {n KA KB : ℕ} (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)

noncomputable def mstep : ℕ → (TS n KA KB → ℝ) → TS n KA KB → ℝ
  | 0, g, s => g s
  | N + 1, g, s => ∑ t, transS θA θB ρ πA πB s t * mstep N g t

@[simp] theorem mstep_zero (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB 0 g s = g s := rfl

theorem mstep_succ (N : ℕ) (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB (N + 1) g s
      = ∑ t, transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N g t := rfl

variable {θA θB ρ πA πB}

theorem mstep_nonneg (h : Adm θA θB ρ πA πB) (N : ℕ) {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (s : TS n KA KB) : 0 ≤ mstep θA θB ρ πA πB N g s := by
  induction N generalizing s with
  | zero => exact hg s
  | succ N ih =>
    exact Finset.sum_nonneg fun t _ =>
      mul_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t) (ih t)

theorem mstep_mono (h : Adm θA θB ρ πA πB) (N : ℕ) {g₁ g₂ : TS n KA KB → ℝ}
    (hg : ∀ t, g₁ t ≤ g₂ t) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N g₁ s ≤ mstep θA θB ρ πA πB N g₂ s := by
  induction N generalizing s with
  | zero => exact hg s
  | succ N ih =>
    exact Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (ih t) (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t)

theorem mstep_succ' (N : ℕ) (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB (N + 1) g s
      = mstep θA θB ρ πA πB N (mstep θA θB ρ πA πB 1 g) s := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ θA θB ρ πA πB (N + 1) g s,
      mstep_succ θA θB ρ πA πB N (mstep θA θB ρ πA πB 1 g) s]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]

noncomputable def stepKer (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (N : ℕ) :
    Kernel ((_i : Finset.Iic 0) → TS n KA KB) (TS n KA KB) :=
  (Kernel.partialTraj (X := fun _ => TS n KA KB) (argSeqT θA θB ρ πA πB h) 0 N).map
    (fun y => y ⟨N, Finset.mem_Iic.2 le_rfl⟩)

theorem map_eval_traj (h : Adm θA θB ρ πA πB) (N : ℕ)
    (x : (_i : Finset.Iic 0) → TS n KA KB) :
    Measure.map (fun ω : (_ : ℕ) → TS n KA KB => ω N)
        (Kernel.traj (argSeqT θA θB ρ πA πB h) 0 x)
      = stepKer θA θB ρ πA πB h N x := by
  rw [stepKer, Kernel.map_apply _ (measurable_pi_apply _),
    ← Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => TS n KA KB)
      (κ := argSeqT θA θB ρ πA πB h) 0 N x]
  exact (Measure.map_map
    (measurable_pi_apply (⟨N, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic N))
    (measurable_frestrictLe (X := fun _ : ℕ => TS n KA KB) N)).symm

theorem stepKer_zero (h : Adm θA θB ρ πA πB) (x : (_i : Finset.Iic 0) → TS n KA KB) :
    stepKer θA θB ρ πA πB h 0 x = Measure.dirac (x ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
  rw [stepKer, Kernel.map_apply _ (measurable_pi_apply _), Kernel.partialTraj_self,
    Kernel.id_apply]
  exact Measure.map_dirac' (measurable_pi_apply _) x

theorem stepKer_succ (h : Adm θA θB ρ πA πB) (N : ℕ) :
    stepKer (n := n) θA θB ρ πA πB h (N + 1)
      = (argKernelT θA θB ρ πA πB h) ∘ₖ (stepKer θA θB ρ πA πB h N) := by
  rw [stepKer, stepKer,
    ← Kernel.partialTraj_comp_partialTraj (X := fun _ => TS n KA KB)
      (κ := argSeqT θA θB ρ πA πB h) (Nat.zero_le N) (Nat.le_succ N),
    Kernel.map_comp, Kernel.map_partialTraj_succ_self, argSeqT,
    ← Kernel.comp_map _ _ Measurable.of_discrete]

theorem lintegral_stepKer (h : Adm θA θB ρ πA πB) (N : ℕ) {g : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (x : (_i : Finset.Iic 0) → TS n KA KB) :
    (∫⁻ u, ENNReal.ofReal (g u) ∂(stepKer θA θB ρ πA πB h N x))
      = ENNReal.ofReal (mstep θA θB ρ πA πB N g (x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) := by
  induction N generalizing g with
  | zero => rw [stepKer_zero, lintegral_dirac, mstep_zero]
  | succ N ih =>
    have hstep : ∀ v : TS n KA KB,
        (∫⁻ u, ENNReal.ofReal (g u) ∂(argKernelT θA θB ρ πA πB h v))
          = ENNReal.ofReal (mstep θA θB ρ πA πB 1 g v) := by
      intro v
      rw [lintegral_fintype, mstep_succ]
      simp only [mstep_zero]
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ =>
        mul_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB v t) (hg t))]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [argKernelT_singleton, ENNReal.ofReal_mul
        (transS_nonneg h.thA h.thB h.rho h.piA h.piB v t), mul_comm]
    have hnn : ∀ t : TS n KA KB, 0 ≤ mstep θA θB ρ πA πB 1 g t :=
      fun t => mstep_nonneg h 1 hg t
    rw [stepKer_succ, Kernel.comp_apply, Measure.lintegral_bind
      (Kernel.aemeasurable _) (Measurable.of_discrete).aemeasurable]
    calc (∫⁻ v, ∫⁻ u, ENNReal.ofReal (g u) ∂(argKernelT θA θB ρ πA πB h v)
            ∂(stepKer θA θB ρ πA πB h N x))
        = ∫⁻ v, ENNReal.ofReal (mstep θA θB ρ πA πB 1 g v)
            ∂(stepKer θA θB ρ πA πB h N x) := lintegral_congr fun v => hstep v
      _ = ENNReal.ofReal (mstep θA θB ρ πA πB N (mstep θA θB ρ πA πB 1 g)
            (x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) := ih hnn
      _ = ENNReal.ofReal (mstep θA θB ρ πA πB (N + 1) g
            (x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) := by rw [mstep_succ']

theorem lintegral_argTrajT (h : Adm θA θB ρ πA πB) (N : ℕ) {g : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (s : TS n KA KB) :
    (∫⁻ ω, ENNReal.ofReal (g (ω N)) ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (mstep θA θB ρ πA πB N g s) := by
  have hmap := lintegral_map
    (μ := Kernel.traj (argSeqT θA θB ρ πA πB h) 0 (fun _ : Finset.Iic 0 => s))
    (f := fun u : TS n KA KB => ENNReal.ofReal (g u))
    (g := fun ω : (_ : ℕ) → TS n KA KB => ω N) Measurable.of_discrete (measurable_pi_apply _)
  rw [argTrajT, ← hmap, map_eval_traj h N (fun _ => s), lintegral_stepKer h N hg]

end Rhone.Coalescent.TypedAncestralChain
