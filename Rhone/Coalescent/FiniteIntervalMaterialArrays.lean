/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialState
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.FunProp

/-! # Measurability on dynamic finite-array representations -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess

theorem measurable_sigma_of_fibers {ι : Type*} {β : ι → Type*} {γ : Type*}
    [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ i, Measurable (f ∘ Sigma.mk i)) : Measurable f := by
  rw [measurable_iff_le_map]
  change _ ≤ (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)).map f
  rw [MeasurableSpace.map_iInf]
  apply le_iInf
  intro i
  rw [MeasurableSpace.map_comp]
  exact (hf i).le_map

theorem hullHi_measurable : Measurable hullHi := by
  apply measurable_sigma_of_fibers
  intro k
  change Measurable (fun a : Fin (k+1) → ℝ × ℝ =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => if (a i).1 < (a i).2 then (a i).2 else 0))
  have hf : ∀ i : Fin (k+1), Measurable
      (fun a : Fin (k+1) → ℝ × ℝ => if (a i).1 < (a i).2 then (a i).2 else 0) := by
    intro i
    have hl : Measurable (fun a : Fin (k+1) → ℝ × ℝ => (a i).1) :=
      (measurable_pi_apply i).fst
    have hu : Measurable (fun a : Fin (k+1) → ℝ × ℝ => (a i).2) :=
      (measurable_pi_apply i).snd
    exact hu.piecewise (measurableSet_lt hl hu) measurable_const
  convert Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hf i) using 1
  ext a
  simp

theorem hullLo_measurable : Measurable hullLo := by
  apply measurable_sigma_of_fibers
  intro k
  change Measurable (fun a : Fin (k+1) → ℝ × ℝ =>
    Finset.univ.inf' Finset.univ_nonempty
      (fun i => if (a i).1 < (a i).2 then (a i).1 else 1))
  have hf : ∀ i : Fin (k+1), Measurable
      (fun a : Fin (k+1) → ℝ × ℝ => if (a i).1 < (a i).2 then (a i).1 else 1) := by
    intro i
    have hl : Measurable (fun a : Fin (k+1) → ℝ × ℝ => (a i).1) :=
      (measurable_pi_apply i).fst
    have hu : Measurable (fun a : Fin (k+1) → ℝ × ℝ => (a i).2) :=
      (measurable_pi_apply i).snd
    exact hl.piecewise (measurableSet_lt hl hu) measurable_const
  have hh : Measurable (Finset.univ.inf' Finset.univ_nonempty
      (fun (i : Fin (k+1)) (a : Fin (k+1) → ℝ × ℝ) =>
        if (a i).1 < (a i).2 then (a i).1 else 1)) :=
    Finset.inf'_induction Finset.univ_nonempty _
      (fun _ hf _ hg => hf.inf hg) (fun i _ => hf i)
  convert hh using 1
  ext a
  simp

theorem hullLength_measurable : Measurable hullLength := by
  exact measurable_const.max (hullHi_measurable.sub hullLo_measurable)

end Rhone.Coalescent.IntervalProcess
