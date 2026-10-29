/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialMarked

/-! # A concrete common-noise marked update, including real times and cuts -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess

noncomputable def chooseByRate {α : Type*} (rate : α → ℝ) : List α → ℝ → Option α
  | [], _ => none
  | a :: rest, u => if u < rate a then some a else chooseByRate rate rest (u-rate a)

noncomputable def selectedAction (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    Option (ActionIndex s) := by
  classical
  exact chooseByRate (fun a => (candidateRate mode R s a : ℝ))
    Finset.univ.toList (u 0 * (totalRate mode R s : ℝ))

def atTime (t : ℝ) (s : State) : State := (t, s.2)

noncomputable def sampleStep (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    State × EventRecord := by
  classical
  exact if s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0 then (s, (s.1, .inl ())) else
    let t := s.1 - Real.log (u 1) / (totalRate mode R s : ℝ)
    match selectedAction mode R s u with
    | none => (s, (s.1, .inl ()))
    | some (.inl ij) =>
        (atTime t (coalSuccessor s ij.1 ij.2),
          (t, .inr (.inl (ij.1.val, ij.2.val))))
    | some (.inr i) =>
        let x := hullLo (s.2.2.2 i).2 + hullLength (s.2.2.2 i).2 * u 2
        (atTime t (splitSuccessor s i x), (t, .inr (.inr (i.val, x))))

end Rhone.Coalescent.IntervalProcess
