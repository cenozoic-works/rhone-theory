/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Assortative
public import Rhone.Dynamics.AssortativeMating
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable assortative mating equals the specification

Source: crow_kimura1970, sec. 4.6, p. 144. -/

@[expose] public section
namespace Rhone.Computation.Assortative
open Filter Topology

def toReal (g : Rat × Rat × Rat) : ℝ × ℝ × ℝ := ((g.1 : ℝ), (g.2.1 : ℝ), (g.2.2 : ℝ))

theorem assortFreq_cast (g : Rat × Rat × Rat) :
    ((assortFreq g : Rat) : ℝ) = Rhone.Dynamics.Assortative.assortFreq (toReal g) := by
  unfold assortFreq Rhone.Dynamics.Assortative.assortFreq toReal
  push_cast
  rfl

theorem assortStep_cast (α : Rat) (g : Rat × Rat × Rat) :
    toReal (assortStep α g) = Rhone.Dynamics.Assortative.assortStep (α : ℝ) (toReal g) := by
  have h := assortFreq_cast g
  simp only [assortStep, Rhone.Dynamics.Assortative.assortStep, toReal] at h ⊢
  rw [← h]
  push_cast
  rfl

theorem assortOrbit_cast (α : Rat) (g0 : Rat × Rat × Rat) (t : Nat) :
    toReal (assortOrbit α g0 t) =
      Rhone.Dynamics.Assortative.assortOrbit (α : ℝ) (toReal g0) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [assortOrbit, assortStep_cast, ih, Rhone.Dynamics.Assortative.assortOrbit]

theorem assortHetFixed_cast (α p : Rat) :
    ((assortHetFixed α p : Rat) : ℝ) =
      Rhone.Dynamics.Assortative.assortHetFixed (α : ℝ) (p : ℝ) := by
  unfold assortHetFixed Rhone.Dynamics.Assortative.assortHetFixed
  push_cast
  rfl

theorem assortFreq_orbit (α : Rat) (g0 : Rat × Rat × Rat) (t : Nat) :
    assortFreq (assortOrbit α g0 t) = assortFreq g0 := by
  apply Rat.cast_injective (α := ℝ)
  rw [assortFreq_cast, assortFreq_cast, assortOrbit_cast]
  exact Rhone.Dynamics.Assortative.assortOrbit_freq (α : ℝ) (toReal g0) t

theorem assortOrbit_total (α : Rat) (g0 : Rat × Rat × Rat) (h : g0.1 + g0.2.1 + g0.2.2 = 1)
    (t : Nat) :
    (assortOrbit α g0 t).1 + (assortOrbit α g0 t).2.1 + (assortOrbit α g0 t).2.2 = 1 := by
  apply Rat.cast_injective (α := ℝ)
  have h' : (toReal g0).1 + (toReal g0).2.1 + (toReal g0).2.2 = 1 := by
    simp only [toReal]
    exact_mod_cast h
  have key := Rhone.Dynamics.Assortative.assortOrbit_total (α : ℝ) h' t
  rw [← assortOrbit_cast] at key
  simp only [toReal] at key
  push_cast
  exact_mod_cast key

theorem assortOrbit_het (α : Rat) (g0 : Rat × Rat × Rat) (hα : α ≠ 2) (t : Nat) :
    (assortOrbit α g0 t).2.1 = hetClosed α g0 t := by
  apply Rat.cast_injective (α := ℝ)
  have hα' : (α : ℝ) ≠ 2 := by exact_mod_cast hα
  have key := Rhone.Dynamics.Assortative.assortOrbit_het (toReal g0) hα' t
  have e : (((assortOrbit α g0 t).2.1 : Rat) : ℝ) =
      (Rhone.Dynamics.Assortative.assortOrbit (α : ℝ) (toReal g0) t).2.1 := by
    rw [← assortOrbit_cast]; rfl
  rw [e, key, hetClosed, ← assortFreq_cast, ← assortHetFixed_cast]
  push_cast
  rfl

theorem assortOrbit_het_tendsto (α : Rat) (g0 : Rat × Rat × Rat) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Tendsto (fun t => (((assortOrbit α g0 t).2.1 : Rat) : ℝ)) atTop
      (𝓝 ((assortHetFixed α (assortFreq g0) : Rat) : ℝ)) := by
  have key := Rhone.Dynamics.Assortative.tendsto_assortOrbit_het (α := (α : ℝ))
    (by exact_mod_cast h0) (by exact_mod_cast h1) (toReal g0)
  rw [assortHetFixed_cast, assortFreq_cast]
  refine key.congr (fun t => ?_)
  have e : (((assortOrbit α g0 t).2.1 : Rat) : ℝ) =
      (Rhone.Dynamics.Assortative.assortOrbit (α : ℝ) (toReal g0) t).2.1 := by
    rw [← assortOrbit_cast]; rfl
  exact e.symm

theorem assortOrbit_hom_tendsto (α : Rat) (g0 : Rat × Rat × Rat) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Tendsto (fun t => (((assortOrbit α g0 t).1 : Rat) : ℝ)) atTop
      (𝓝 (((assortFreq g0 - assortHetFixed α (assortFreq g0) / 2 : Rat) : ℝ))) := by
  have key := Rhone.Dynamics.Assortative.tendsto_assortOrbit_hom (α := (α : ℝ))
    (by exact_mod_cast h0) (by exact_mod_cast h1) (toReal g0)
  have hl : (((assortFreq g0 - assortHetFixed α (assortFreq g0) / 2 : Rat) : ℝ)) =
      Rhone.Dynamics.Assortative.assortFreq (toReal g0) -
        Rhone.Dynamics.Assortative.assortHetFixed (α : ℝ)
          (Rhone.Dynamics.Assortative.assortFreq (toReal g0)) / 2 := by
    push_cast
    rw [assortFreq_cast, assortHetFixed_cast, assortFreq_cast]
  rw [hl]
  refine key.congr (fun t => ?_)
  have e : (((assortOrbit α g0 t).1 : Rat) : ℝ) =
      (Rhone.Dynamics.Assortative.assortOrbit (α : ℝ) (toReal g0) t).1 := by
    rw [← assortOrbit_cast]; rfl
  exact e.symm

end Rhone.Computation.Assortative
