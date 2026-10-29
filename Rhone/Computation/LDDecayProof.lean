/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.LDDecay
public import Rhone.Dynamics.LDDecay
public import Rhone.Dynamics.LDMeasures
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable LD decay equals the specification

Source: robbins1918, eq. (5), p. 377; lewontin_kojima1960, eq. (3), p. 459; lewontin1964, p. 50. -/

@[expose] public section
namespace Rhone.Computation.LDDecay
open Rhone.Dynamics

def toReal (g : Gametes) : Rhone.Dynamics.Gametes ℝ where
  x11 := (g.x11 : ℝ)
  x12 := (g.x12 : ℝ)
  x21 := (g.x21 : ℝ)
  x22 := (g.x22 : ℝ)

def toSpec (g : Gametes) : Rhone.Dynamics.Gametes Rat where
  x11 := g.x11
  x12 := g.x12
  x21 := g.x21
  x22 := g.x22

theorem toReal_recombine (r : Rat) (g : Gametes) :
    toReal (Gametes.recombine r g) = Rhone.Dynamics.Gametes.recombine (r : ℝ) (toReal g) := by
  simp only [toReal, Gametes.recombine, Gametes.pA, Gametes.pB, Gametes.pA', Gametes.pB',
    Rhone.Dynamics.Gametes.recombine, Rhone.Dynamics.Gametes.pA, Rhone.Dynamics.Gametes.pB,
    Rhone.Dynamics.Gametes.pA', Rhone.Dynamics.Gametes.pB']
  congr 1 <;> push_cast <;> rfl

theorem toReal_recombineN (r : Rat) (g : Gametes) (t : Nat) :
    toReal (Gametes.recombineN r g t) =
      (Rhone.Dynamics.Gametes.recombine (r : ℝ))^[t] (toReal g) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Gametes.recombineN, toReal_recombine, ih, Function.iterate_succ_apply']

theorem D_cast (g : Gametes) : ((g.D : Rat) : ℝ) = (toReal g).D := by
  simp only [Gametes.D, toReal, Rhone.Dynamics.Gametes.D]
  push_cast
  rfl

theorem total_cast (g : Gametes) : ((g.total : Rat) : ℝ) = (toReal g).total := by
  simp only [Gametes.total, toReal, Rhone.Dynamics.Gametes.total]
  push_cast
  rfl

theorem D_recombineN_cast (r : Rat) (g : Gametes) (t : Nat) :
    (((Gametes.recombineN r g t).D : Rat) : ℝ) =
      ((Rhone.Dynamics.Gametes.recombine (r : ℝ))^[t] (toReal g)).D := by
  rw [D_cast, toReal_recombineN]

theorem D_decay (r : Rat) (g : Gametes) (hg : g.total = 1) (t : Nat) :
    (Gametes.recombineN r g t).D = dClosedForm r g.D t ∧
      (((Gametes.recombineN r g t).D : Rat) : ℝ) = (1 - (r : ℝ)) ^ t * (toReal g).D := by
  have hg' : (toReal g).total = 1 := by
    rw [← total_cast, hg]; simp
  have key := Rhone.Dynamics.Gametes.D_iterate (g := toReal g) (r : ℝ) hg' t
  have hcast : (((Gametes.recombineN r g t).D : Rat) : ℝ) = (1 - (r : ℝ)) ^ t * (toReal g).D := by
    rw [D_recombineN_cast, key]
  refine ⟨?_, hcast⟩
  apply Rat.cast_injective (α := ℝ)
  rw [hcast, dClosedForm, Rat.cast_mul, Rat.cast_pow, D_cast]
  push_cast
  rfl

theorem D_decay_rat (r : Rat) (g : Gametes) (hg : g.total = 1) (t : Nat) :
    ((Rhone.Dynamics.Gametes.recombine r)^[t] (toSpec g)).D = dClosedForm r g.D t := by
  have h := Rhone.Dynamics.Gametes.D_iterate (g := toSpec g) r hg t
  rw [h]
  rfl

theorem pA_pB_recombineN (r : Rat) (g : Gametes) (hg : g.total = 1) (t : Nat) :
    (Gametes.recombineN r g t).pA = g.pA ∧ (Gametes.recombineN r g t).pB = g.pB ∧
      (Gametes.recombineN r g t).total = 1 := by
  induction t with
  | zero => exact ⟨rfl, rfl, hg⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e : Gametes.recombine r (Gametes.recombineN r g t) = Gametes.recombineN r g (t + 1) :=
      rfl
    have s := toSpec (Gametes.recombineN r g t)
    have hA := Rhone.Dynamics.Gametes.recombine_pA (g := toSpec (Gametes.recombineN r g t)) r h3
    have hB := Rhone.Dynamics.Gametes.recombine_pB (g := toSpec (Gametes.recombineN r g t)) r h3
    have hT := Rhone.Dynamics.Gametes.total_recombine (g := toSpec (Gametes.recombineN r g t)) r h3
    rw [← e]
    exact ⟨hA.trans h1, hB.trans h2, hT⟩

theorem dMax_eq (pA pB D : Rat) : dMax pA pB D = Rhone.Dynamics.Gametes.dMax pA pB D := by
  unfold dMax Rhone.Dynamics.Gametes.dMax
  simp only [min_def]

theorem lewontinD'_eq (pA pB D : Rat) :
    lewontinD' pA pB D = Rhone.Dynamics.Gametes.lewontinD' pA pB D := by
  unfold lewontinD' Rhone.Dynamics.Gametes.lewontinD'
  rw [dMax_eq]

theorem rSq_eq (pA pB D : Rat) :
    rSq pA pB D = Rhone.Dynamics.Gametes.rSq pA pB D := rfl

theorem lewontinD'_decay (r : Rat) (g : Gametes) (hr1 : r ≤ 1) (hg : g.total = 1) (t : Nat) :
    lewontinD' g.pA g.pB (Gametes.recombineN r g t).D = (1 - r) ^ t * lewontinD' g.pA g.pB g.D := by
  rw [(D_decay r g hg t).1, dClosedForm, lewontinD'_eq, lewontinD'_eq]
  exact Rhone.Dynamics.Gametes.lewontinD'_mul (pow_nonneg (sub_nonneg.mpr hr1) t)

theorem rSq_decay (r : Rat) (g : Gametes) (hg : g.total = 1) (t : Nat) :
    rSq g.pA g.pB (Gametes.recombineN r g t).D = (1 - r) ^ (2 * t) * rSq g.pA g.pB g.D := by
  rw [(D_decay r g hg t).1, dClosedForm]
  simp only [rSq, pow_mul', mul_pow, mul_div_assoc]

end Rhone.Computation.LDDecay
