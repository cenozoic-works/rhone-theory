/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.BranchLengthMoments.Branch

/-! # The shift (Markov) step for `Kernel.traj`, and two-time expectations -/

@[expose] public section

namespace Rhone.Coalescent.SecondMoments

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory
open ProbabilityTheory Preorder
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem lintegral_argKernelT (h : Adm θA θB ρ πA πB) {u : TS n KA KB → ℝ}
    (hu : ∀ t, 0 ≤ u t) (v : TS n KA KB) :
    (∫⁻ t, ENNReal.ofReal (u t) ∂(argKernelT θA θB ρ πA πB h v))
      = ENNReal.ofReal (mstep θA θB ρ πA πB 1 u v) := by
  rw [lintegral_fintype, mstep_succ]
  simp only [mstep_zero]
  rw [ENNReal.ofReal_sum_of_nonneg fun t _ =>
    mul_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB v t) (hu t)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [argKernelT_singleton, ENNReal.ofReal_mul
    (transS_nonneg h.thA h.thB h.rho h.piA h.piB v t), mul_comm]

noncomputable def pathKer (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (a b : ℕ) :
    Kernel ((_i : Finset.Iic a) → TS n KA KB) ((_i : Finset.Iic b) → TS n KA KB) :=
  Kernel.partialTraj (X := fun _ : ℕ => TS n KA KB) (argSeqT θA θB ρ πA πB h) a b

instance isMarkovKernel_pathKer (h : Adm θA θB ρ πA πB) (a b : ℕ) :
    IsMarkovKernel (pathKer (n := n) θA θB ρ πA πB h a b) := by
  rw [pathKer]
  infer_instance

theorem pathKer_succ_eq_comp (h : Adm θA θB ρ πA πB) (N : ℕ) :
    pathKer (n := n) θA θB ρ πA πB h 0 (N + 1)
      = (pathKer θA θB ρ πA πB h N (N + 1)) ∘ₖ (pathKer θA θB ρ πA πB h 0 N) :=
  Kernel.partialTraj_succ_eq_comp (Nat.zero_le N)

theorem map_frestrictLe_argTrajT (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    Measure.map (frestrictLe (π := fun _ : ℕ => TS n KA KB) N)
        (argTrajT θA θB ρ πA πB h s)
      = pathKer θA θB ρ πA πB h 0 N (fun _ => s) := by
  rw [argTrajT, pathKer, Kernel.traj_map_frestrictLe_apply]

theorem lintegral_frestrictLe (h : Adm θA θB ρ πA πB) (N : ℕ)
    (Φ : ((_i : Finset.Iic N) → TS n KA KB) → ℝ≥0∞) (s : TS n KA KB) :
    (∫⁻ ω, Φ (frestrictLe (π := fun _ : ℕ => TS n KA KB) N ω)
        ∂(argTrajT θA θB ρ πA πB h s))
      = ∫⁻ z, Φ z ∂(pathKer θA θB ρ πA πB h 0 N (fun _ => s)) := by
  rw [← map_frestrictLe_argTrajT h N s,
    lintegral_map (measurable_of_countable Φ)
      (measurable_frestrictLe (X := fun _ : ℕ => TS n KA KB) N)]

theorem ae_pathKer_succ (h : Adm θA θB ρ πA πB) (N : ℕ)
    (z : (_i : Finset.Iic N) → TS n KA KB) :
    ∀ᵐ z' ∂(pathKer θA θB ρ πA πB h N (N + 1) z),
      frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ N) z' = z := by
  have hker : (Kernel.partialTraj (X := fun _ : ℕ => TS n KA KB)
        (argSeqT θA θB ρ πA πB h) N (N + 1)).map
        (frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ N)) = Kernel.id := by
    rw [Kernel.partialTraj_map_frestrictLe₂, Kernel.partialTraj_self]
  have hmap : Measure.map (frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ N))
      (pathKer θA θB ρ πA πB h N (N + 1) z) = Measure.dirac z := by
    rw [pathKer, ← Kernel.map_apply _
      (measurable_frestrictLe₂ (X := fun _ : ℕ => TS n KA KB) (Nat.le_succ N)), hker,
      Kernel.id_apply]
  have hset : {z' : (_i : Finset.Iic (N + 1)) → TS n KA KB |
        ¬ frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ N) z' = z}
      = (frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ N)) ⁻¹' {z}ᶜ := rfl
  rw [MeasureTheory.ae_iff, hset,
    ← Measure.map_apply (measurable_frestrictLe₂ (X := fun _ : ℕ => TS n KA KB) (Nat.le_succ N))
      (measurableSet_singleton z).compl, hmap]
  simp

theorem map_last_pathKer_succ (h : Adm θA θB ρ πA πB) (N : ℕ)
    (z : (_i : Finset.Iic N) → TS n KA KB) :
    Measure.map
        (fun z' : (_i : Finset.Iic (N + 1)) → TS n KA KB =>
          z' ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩)
        (pathKer θA θB ρ πA πB h N (N + 1) z)
      = argKernelT θA θB ρ πA πB h (z ⟨N, Finset.mem_Iic.2 le_rfl⟩) := by
  rw [pathKer, ← Kernel.map_apply _ (measurable_pi_apply _),
    Kernel.map_partialTraj_succ_self, argSeqT, Kernel.comap_apply]

theorem lintegral_pathKer_succ_pair (h : Adm θA θB ρ πA πB) {j N : ℕ} (hjN : j ≤ N)
    {g u : TS n KA KB → ℝ} (hu : ∀ t, 0 ≤ u t)
    (z : (_i : Finset.Iic N) → TS n KA KB) :
    (∫⁻ z', ENNReal.ofReal (g (z' ⟨j, Finset.mem_Iic.2 (hjN.trans (Nat.le_succ N))⟩))
        * ENNReal.ofReal (u (z' ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩))
        ∂(pathKer θA θB ρ πA πB h N (N + 1) z))
      = ENNReal.ofReal (g (z ⟨j, Finset.mem_Iic.2 hjN⟩))
        * ENNReal.ofReal (mstep θA θB ρ πA πB 1 u (z ⟨N, Finset.mem_Iic.2 le_rfl⟩)) := by
  have hfrozen : (∫⁻ z',
        ENNReal.ofReal (g (z' ⟨j, Finset.mem_Iic.2 (hjN.trans (Nat.le_succ N))⟩))
        * ENNReal.ofReal (u (z' ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩))
        ∂(pathKer θA θB ρ πA πB h N (N + 1) z))
      = ∫⁻ z', ENNReal.ofReal (g (z ⟨j, Finset.mem_Iic.2 hjN⟩))
        * ENNReal.ofReal (u (z' ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩))
        ∂(pathKer θA θB ρ πA πB h N (N + 1) z) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pathKer_succ h N z] with z' hz'
    have hj : z' ⟨j, Finset.mem_Iic.2 (hjN.trans (Nat.le_succ N))⟩
        = z ⟨j, Finset.mem_Iic.2 hjN⟩ := congrFun hz' ⟨j, Finset.mem_Iic.2 hjN⟩
    rw [hj]
  have hlast : (∫⁻ z', ENNReal.ofReal (u (z' ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩))
        ∂(pathKer θA θB ρ πA πB h N (N + 1) z))
      = ENNReal.ofReal (mstep θA θB ρ πA πB 1 u (z ⟨N, Finset.mem_Iic.2 le_rfl⟩)) := by
    rw [← lintegral_argKernelT h hu, ← map_last_pathKer_succ h N z,
      lintegral_map Measurable.of_discrete (measurable_pi_apply _)]
  rw [hfrozen, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlast]

theorem lintegral_pair_succ (h : Adm θA θB ρ πA πB) {j N : ℕ} (hjN : j ≤ N)
    {g u : TS n KA KB → ℝ} (hu : ∀ t, 0 ≤ u t) (s : TS n KA KB) :
    (∫⁻ ω, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω (N + 1)))
        ∂(argTrajT θA θB ρ πA πB h s))
      = ∫⁻ ω, ENNReal.ofReal (g (ω j))
          * ENNReal.ofReal (mstep θA θB ρ πA πB 1 u (ω N)) ∂(argTrajT θA θB ρ πA πB h s) := by
  set Φ₁ : ((_i : Finset.Iic (N + 1)) → TS n KA KB) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (g (z ⟨j, Finset.mem_Iic.2 (hjN.trans (Nat.le_succ N))⟩))
      * ENNReal.ofReal (u (z ⟨N + 1, Finset.mem_Iic.2 le_rfl⟩)) with hΦ₁
  set Φ₂ : ((_i : Finset.Iic N) → TS n KA KB) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (g (z ⟨j, Finset.mem_Iic.2 hjN⟩))
      * ENNReal.ofReal (mstep θA θB ρ πA πB 1 u (z ⟨N, Finset.mem_Iic.2 le_rfl⟩)) with hΦ₂
  calc (∫⁻ ω, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω (N + 1)))
          ∂(argTrajT θA θB ρ πA πB h s))
      = ∫⁻ ω, Φ₁ (frestrictLe (π := fun _ : ℕ => TS n KA KB) (N + 1) ω)
          ∂(argTrajT θA θB ρ πA πB h s) := lintegral_congr fun _ => rfl
    _ = ∫⁻ z, Φ₁ z ∂(pathKer θA θB ρ πA πB h 0 (N + 1) (fun _ => s)) :=
        lintegral_frestrictLe h (N + 1) Φ₁ s
    _ = ∫⁻ z, Φ₂ z ∂(pathKer θA θB ρ πA πB h 0 N (fun _ => s)) := by
        rw [pathKer_succ_eq_comp h N, Kernel.comp_apply,
          Measure.lintegral_bind (Kernel.aemeasurable _)
            (measurable_of_countable Φ₁).aemeasurable]
        exact lintegral_congr fun z => lintegral_pathKer_succ_pair h hjN hu z
    _ = ∫⁻ ω, Φ₂ (frestrictLe (π := fun _ : ℕ => TS n KA KB) N ω)
          ∂(argTrajT θA θB ρ πA πB h s) := (lintegral_frestrictLe h N Φ₂ s).symm
    _ = ∫⁻ ω, ENNReal.ofReal (g (ω j))
          * ENNReal.ofReal (mstep θA θB ρ πA πB 1 u (ω N))
          ∂(argTrajT θA θB ρ πA πB h s) := lintegral_congr fun _ => rfl

theorem lintegral_two_time (h : Adm θA θB ρ πA πB) (j m : ℕ)
    {g u : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) (hu : ∀ t, 0 ≤ u t) (s : TS n KA KB) :
    (∫⁻ ω, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω (j + m)))
        ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (mstep θA θB ρ πA πB j
          (fun x => g x * mstep θA θB ρ πA πB m u x) s) := by
  induction m generalizing u with
  | zero =>
    simp only [Nat.add_zero, mstep_zero]
    rw [← lintegral_argTrajT h j (g := fun x => g x * u x)
      (fun t => mul_nonneg (hg t) (hu t)) s]
    exact lintegral_congr fun ω => (ENNReal.ofReal_mul (hg (ω j))).symm
  | succ m ih =>
    have hsucc : j + (m + 1) = (j + m) + 1 := rfl
    rw [hsucc, lintegral_pair_succ h (Nat.le_add_right j m) hu s,
      ih (u := mstep θA θB ρ πA πB 1 u) (mstep_nonneg h 1 hu)]
    refine congrArg ENNReal.ofReal (congrArg (fun f => mstep θA θB ρ πA πB j f s) ?_)
    funext x
    rw [mstep_succ']

noncomputable def pk (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ)
    (s t : TS n KA KB) : ℝ :=
  mstep θA θB ρ πA πB N (fun x => if x = t then 1 else 0) s

theorem pk_nonneg (h : Adm θA θB ρ πA πB) (N : ℕ) (s t : TS n KA KB) :
    0 ≤ pk θA θB ρ πA πB N s t := by
  refine mstep_nonneg h N (fun x => ?_) s
  split_ifs <;> norm_num

theorem mstep_zero_fun (N : ℕ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (fun _ => (0 : ℝ)) s = 0 := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ]
    exact Finset.sum_eq_zero fun t _ => by rw [ih t, mul_zero]

theorem mstep_eq_sum_pk (N : ℕ) (f : TS n KA KB → ℝ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N f s = ∑ t, pk θA θB ρ πA πB N s t * f t := by
  induction N generalizing s with
  | zero =>
    rw [mstep_zero]
    have hval : ∀ t : TS n KA KB,
        pk θA θB ρ πA πB 0 s t * f t = if s = t then f t else 0 := by
      intro t
      rw [pk, mstep_zero]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun t _ => hval t,
      Finset.sum_ite_eq (Finset.univ : Finset (TS n KA KB)) s f, ite_eq_left (Finset.mem_univ s)]
  | succ N ih =>
    rw [mstep_succ]
    have hin : ∀ v : TS n KA KB, transS θA θB ρ πA πB s v * mstep θA θB ρ πA πB N f v
        = ∑ t, transS θA θB ρ πA πB s v * (pk θA θB ρ πA πB N v t * f t) := by
      intro v
      rw [ih v, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun v _ => hin v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pk, mstep_succ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => by rw [pk]; ring

theorem pk_eq_zero_of_closed {C : TS n KA KB → Prop} (hC : Closed θA θB ρ πA πB C) (N : ℕ)
    {s t : TS n KA KB} (hs : C s) (ht : ¬ C t) : pk θA θB ρ πA πB N s t = 0 := by
  have hcongr : pk θA θB ρ πA πB N s t = mstep θA θB ρ πA πB N (fun _ => (0 : ℝ)) s := by
    refine mstep_congr_closed hC (fun x hx => ?_) N hs
    exact ite_eq_right fun (hc : x = t) => ht (hc ▸ hx)
  rw [hcongr, mstep_zero_fun]

end Rhone.Coalescent.SecondMoments
