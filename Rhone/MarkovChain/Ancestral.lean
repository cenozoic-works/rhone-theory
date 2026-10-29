/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedHitting
public import Rhone.MarkovChain.JumpHold
public import Mathlib.Order.Partition.Finpartition

/-! # Ancestral processes on set partitions -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

instance instMeasurableSpaceFinpartition {β : Type*} [Lattice β] [OrderBot β] (a : β) :
    MeasurableSpace (Finpartition a) := ⊤

instance instDiscreteMeasurableSpaceFinpartition {β : Type*} [Lattice β] [OrderBot β] (a : β) :
    DiscreteMeasurableSpace (Finpartition a) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

structure AncestralProcess (α : Type*) [Fintype α] [DecidableEq α] extends
    RateChain (Finpartition (univ : Finset α)) where
  coarsens : ∀ π σ, π ≠ σ → Q π σ ≠ 0 → π ≤ σ

namespace AncestralProcess

variable {α : Type*} [Fintype α] [DecidableEq α] (X : AncestralProcess α)
  {π σ : Finpartition (univ : Finset α)}

theorem le_of_Q_ne_zero (h : X.Q π σ ≠ 0) : π ≤ σ := by
  by_cases hπ : π = σ
  · exact hπ.le
  · exact X.coarsens π σ hπ h

theorem card_parts_le_of_Q_ne_zero (h : X.Q π σ ≠ 0) : σ.parts.card ≤ π.parts.card :=
  Finpartition.card_mono (X.le_of_Q_ne_zero h)

theorem le_of_jumpChain_P_ne_zero (h : X.toRateChain.jumpChain.P π σ ≠ 0) : π ≤ σ := by
  by_cases hπ : π = σ
  · exact hπ.le
  · refine X.coarsens π σ hπ fun hQ => h ?_
    simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hπ, hQ]

open Classical in
noncomputable def upperSet (τ : Finpartition (univ : Finset α)) :
    Finset (Finpartition (univ : Finset α)) :=
  univ.filter fun σ => τ ≤ σ

@[simp]
theorem mem_upperSet {τ : Finpartition (univ : Finset α)} : σ ∈ upperSet τ ↔ τ ≤ σ := by
  simp [upperSet]

theorem isClosedSet_upperSet (τ : Finpartition (univ : Finset α)) :
    X.toRateChain.jumpChain.IsClosedSet (upperSet τ) := by
  intro π hπ σ hσ
  by_contra h
  exact hσ (mem_upperSet.2 ((mem_upperSet.1 hπ).trans (X.le_of_jumpChain_P_ne_zero h)))

theorem ae_monotone (π : Finpartition (univ : Finset α)) :
    ∀ᵐ ω ∂X.toRateChain.jumpChain.pathLaw π, Monotone ω := by
  have h : ∀ᵐ ω ∂X.toRateChain.jumpChain.pathLaw π,
      ∀ τ : Finpartition (univ : Finset α), ∀ n, ω n ∈ upperSet τ → ω (n + 1) ∈ upperSet τ :=
    ae_all_iff.2 fun τ => (X.isClosedSet_upperSet τ).ae_stays_mem π
  filter_upwards [h] with ω hω
  exact monotone_nat_of_le_succ fun n =>
    mem_upperSet.1 (hω (ω n) n (mem_upperSet.2 le_rfl))

end AncestralProcess

end Rhone.MarkovChain
