/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Path

/-! # The target set, and the fact that the chain never leaves it -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory
open Preorder

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

def TFin (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) : Set (TS n KA KB) :=
  {t | t.st.1 = ∅ ∧ Fits σA σB t.st}

noncomputable def indT (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (t : TS n KA KB) : ℝ :=
  if t.st.1 = ∅ ∧ Fits σA σB t.st then 1 else 0

theorem indT_nonneg (t : TS n KA KB) : 0 ≤ indT σA σB t := by
  rw [indT]; split_ifs <;> norm_num

theorem dtotS_nonpos_of_mem {t : TS n KA KB} (ht : t ∈ TFin σA σB) :
    ¬ 0 < dtotS θA θB ρ t := by
  have h0 : dtotS θA θB ρ t = 0 := by rw [dtotS, ht.1, dtot_empty]
  rw [h0]
  exact lt_irrefl 0

theorem hitS_succ_eq_sum (N : ℕ) (s : TS n KA KB) :
    hitS σA σB θA θB ρ πA πB (N + 1) s
      = ∑ t : TS n KA KB, transS θA θB ρ πA πB s t * hitS σA σB θA θB ρ πA πB N t := by
  rw [hitS, hitNT_succ_eq_sum N s.st]
  exact (Fintype.sum_equiv (TS.equivTSt (n := n) (KA := KA) (KB := KB))
    (fun t => transS θA θB ρ πA πB s t * hitS σA σB θA θB ρ πA πB N t)
    (fun u => transT θA θB ρ πA πB s.st u * hitNT σA σB θA θB ρ πA πB N u)
    (fun _ => rfl)).symm

theorem hitS_zero (s : TS n KA KB) :
    hitS σA σB θA θB ρ πA πB 0 s = indT σA σB s := rfl

theorem mstep_indT (N : ℕ) (s : TS n KA KB) :
    mstep θA θB ρ πA πB N (indT σA σB) s = hitS σA σB θA θB ρ πA πB N s := by
  induction N generalizing s with
  | zero => rw [mstep_zero, hitS_zero]
  | succ N ih =>
    rw [mstep_succ, hitS_succ_eq_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [ih t]

theorem measure_eval_mem (h : Adm θA θB ρ πA πB) (N : ℕ) (s : TS n KA KB) :
    argTrajT θA θB ρ πA πB h s {ω | ω N ∈ TFin σA σB}
      = ENNReal.ofReal (hitS σA σB θA θB ρ πA πB N s) := by
  have hms : MeasurableSet {ω : (_ : ℕ) → TS n KA KB | ω N ∈ TFin σA σB} :=
    (measurable_pi_apply N) MeasurableSet.of_discrete
  have hfun : (fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (indT σA σB (ω N)))
      = Set.indicator {ω : (_ : ℕ) → TS n KA KB | ω N ∈ TFin σA σB} 1 := by
    funext ω
    by_cases hc : ω N ∈ TFin σA σB
    · have hc2 : ω ∈ {ω : (_ : ℕ) → TS n KA KB | ω N ∈ TFin σA σB} := hc
      have hc3 : (ω N).st.1 = ∅ ∧ Fits σA σB (ω N).st := hc
      rw [Set.indicator_of_mem hc2, Pi.one_apply, indT, ite_eq_left hc3, ENNReal.ofReal_one]
    · have hc2 : ω ∉ {ω : (_ : ℕ) → TS n KA KB | ω N ∈ TFin σA σB} := hc
      have hc3 : ¬ ((ω N).st.1 = ∅ ∧ Fits σA σB (ω N).st) := hc
      rw [Set.indicator_of_notMem hc2, indT, ite_eq_right hc3, ENNReal.ofReal_zero]
  rw [← mstep_indT N s, ← lintegral_argTrajT h N (fun t => indT_nonneg t) s, hfun,
    lintegral_indicator_one hms]

section Absorbing

variable (h : Adm θA θB ρ πA πB)

theorem map_partialTraj_last (j : ℕ) (z : (i : Finset.Iic j) → TS n KA KB) :
    Measure.map (fun y : (i : Finset.Iic (j + 1)) → TS n KA KB =>
        y ⟨j + 1, Finset.mem_Iic.2 le_rfl⟩)
        (Kernel.partialTraj (X := fun _ => TS n KA KB) (argSeqT θA θB ρ πA πB h) j (j + 1) z)
      = argKernelT θA θB ρ πA πB h (z ⟨j, Finset.mem_Iic.2 le_rfl⟩) := by
  have hmap := Kernel.map_partialTraj_succ_self (X := fun _ : ℕ => TS n KA KB)
    (κ := argSeqT θA θB ρ πA πB h) j
  have hz := congrArg (fun k : Kernel ((i : Finset.Iic j) → TS n KA KB) (TS n KA KB) => k z) hmap
  simpa [Kernel.map_apply _ (measurable_pi_apply _), argSeqT, Kernel.comap_apply] using hz

def Absorbing (θA θB ρ : ℝ) (E : Set (TS n KA KB)) : Prop :=
  ∀ t ∈ E, ¬ 0 < dtotS θA θB ρ t

theorem absorbing_TFin : Absorbing θA θB ρ (TFin σA σB) :=
  fun _ ht => dtotS_nonpos_of_mem ht

theorem absorbing_absorbed :
    Absorbing θA θB ρ {t : TS n KA KB | t.st.1 = ∅} := by
  intro t ht
  have h0 : dtotS θA θB ρ t = 0 := by rw [dtotS, ht, dtot_empty]
  rw [h0]
  exact lt_irrefl 0

theorem measure_escape_zero {E : Set (TS n KA KB)} (hE : Absorbing θA θB ρ E) (j : ℕ)
    (s : TS n KA KB) :
    argTrajT θA θB ρ πA πB h s
        {ω | ω j ∈ E ∧ ω (j + 1) ∉ E} = 0 := by
  set S : Set ((i : Finset.Iic (j + 1)) → TS n KA KB) :=
    {y | y ⟨j, Finset.mem_Iic.2 (Nat.le_succ j)⟩ ∈ E
      ∧ y ⟨j + 1, Finset.mem_Iic.2 le_rfl⟩ ∉ E} with hSdef
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet ((fun y : (i : Finset.Iic (j + 1)) → TS n KA KB =>
        y ⟨j, Finset.mem_Iic.2 (Nat.le_succ j)⟩) ⁻¹' E) :=
      (measurable_pi_apply _) MeasurableSet.of_discrete
    have h2 : MeasurableSet ((fun y : (i : Finset.Iic (j + 1)) → TS n KA KB =>
        y ⟨j + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' (E)ᶜ) :=
      (measurable_pi_apply _) MeasurableSet.of_discrete.compl
    exact h1.inter h2
  have hinner : ∀ z : (i : Finset.Iic j) → TS n KA KB,
      (Kernel.partialTraj (X := fun _ => TS n KA KB)
        (argSeqT θA θB ρ πA πB h) j (j + 1) z) S = 0 := by
    intro z
    by_cases hz : z ⟨j, Finset.mem_Iic.2 le_rfl⟩ ∈ E
    · have hsub : S ⊆ (fun y : (i : Finset.Iic (j + 1)) → TS n KA KB =>
          y ⟨j + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' (E)ᶜ := fun y hy => hy.2
      refine measure_mono_null hsub ?_
      rw [← Measure.map_apply (measurable_pi_apply _) MeasurableSet.of_discrete.compl,
        map_partialTraj_last h j z,
        argKernelT_of_nonpos h (hE _ hz),
        Measure.dirac_apply' _ MeasurableSet.of_discrete.compl]
      have hnc : z ⟨j, Finset.mem_Iic.2 le_rfl⟩ ∉ (E)ᶜ := not_not_intro hz
      rw [Set.indicator_of_notMem hnc]
    · have hsub : S ⊆ (frestrictLe₂ (π := fun _ : ℕ => TS n KA KB) (Nat.le_succ j)) ⁻¹' {z}ᶜ := by
        intro y hy hc
        have heq : y ⟨j, Finset.mem_Iic.2 (Nat.le_succ j)⟩ = z ⟨j, Finset.mem_Iic.2 le_rfl⟩ :=
          congrFun (Set.mem_singleton_iff.1 hc) ⟨j, Finset.mem_Iic.2 le_rfl⟩
        exact hz (heq ▸ hy.1)
      have hmeas : MeasurableSet ({z}ᶜ : Set ((i : Finset.Iic j) → TS n KA KB)) :=
        (measurableSet_singleton z).compl
      refine measure_mono_null hsub ?_
      rw [← Measure.map_apply (μ := Kernel.partialTraj (X := fun _ => TS n KA KB)
          (argSeqT θA θB ρ πA πB h) j (j + 1) z)
          (measurable_frestrictLe₂ (Nat.le_succ j)) hmeas,
        Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => TS n KA KB)
          (κ := argSeqT θA θB ρ πA πB h) z (Nat.le_succ j),
        Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_apply' _ hmeas]
      have hnc : z ∉ ({z}ᶜ : Set ((i : Finset.Iic j) → TS n KA KB)) := by simp
      rw [Set.indicator_of_notMem hnc]
  have hev : {ω : (_ : ℕ) → TS n KA KB | ω j ∈ E ∧ ω (j + 1) ∉ E}
      = (frestrictLe (π := fun _ : ℕ => TS n KA KB) (j + 1)) ⁻¹' S := rfl
  rw [argTrajT, hev, ← Measure.map_apply (measurable_frestrictLe _) hSm,
    Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => TS n KA KB)
      (κ := argSeqT θA θB ρ πA πB h) 0 (j + 1) (fun _ => s),
    ← Kernel.partialTraj_comp_partialTraj (X := fun _ => TS n KA KB)
      (κ := argSeqT θA θB ρ πA πB h) (Nat.zero_le j) (Nat.le_succ j),
    Kernel.comp_apply' _ _ _ hSm]
  simp only [hinner]
  exact lintegral_zero

end Absorbing

end Rhone.Coalescent.TypedAncestralChain
