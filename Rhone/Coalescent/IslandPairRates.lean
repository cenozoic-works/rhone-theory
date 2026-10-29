/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.RateChain
public import Mathlib.Data.Fintype.BigOperators

/-! # Labelled symmetric two-lineage island generator -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset

abbrev State (d : Nat) := Option (Fin d × Fin d)

noncomputable def destinationRate (d : Nat) (m : Real) : Real := m / (d - 1 : Nat)

noncomputable def eventRate (d : Nat) (m c : Real) : State d → State d → Real
  | none, _ => 0
  | some (a,b), none => if a = b then c else 0
  | some (a,b), some (x,y) =>
      (if b = y ∧ a ≠ x then destinationRate d m else 0) +
      (if a = x ∧ b ≠ y then destinationRate d m else 0)

noncomputable def generator (d : Nat) (m c : Real) (s t : State d) : Real :=
  eventRate d m c s t - if s = t then ∑ y, eventRate d m c s y else 0

theorem eventRate_self (d : Nat) (m c : Real) (s : State d) :
    eventRate d m c s s = 0 := by
  cases s with
  | none => rfl
  | some p => rcases p with ⟨a,b⟩; simp [eventRate]

theorem eventRate_nonneg (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (s t : State d) : 0 ≤ eventRate d m c s t := by
  have hk : 0 ≤ destinationRate d m := div_nonneg hm (Nat.cast_nonneg _)
  cases s with
  | none => exact le_rfl
  | some p =>
    rcases p with ⟨a,b⟩
    cases t with
    | none => simp only [eventRate]; split_ifs <;> first | exact hc | exact le_rfl
    | some q =>
      rcases q with ⟨x,y⟩
      simp only [eventRate]
      exact add_nonneg (by split_ifs <;> first | exact hk | exact le_rfl)
        (by split_ifs <;> first | exact hk | exact le_rfl)

theorem generator_row_sum (d : Nat) (m c : Real) (s : State d) :
    ∑ t, generator d m c s t = 0 := by
  simp [generator, sum_sub_distrib]

noncomputable def chain (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    Rhone.MarkovChain.RateChain (State d) where
  Q := generator d m c
  off_diag_nonneg s t hst := by
    simp only [generator, hst, ↓reduceIte, sub_zero]
    exact eventRate_nonneg d m c hm hc s t
  row_sum := generator_row_sum d m c

theorem rate_none (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (chain d m c hm hc).rate none = 0 := by
  simp [Rhone.MarkovChain.RateChain.rate, chain, generator, eventRate]

theorem none_absorbing (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (chain d m c hm hc).jumpChain.IsAbsorbing none :=
  Rhone.MarkovChain.RateChain.jumpChain_isAbsorbing (rate_none d m c hm hc)

end Rhone.Coalescent.IslandPair
