/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProbability

/-! # Finite-law transport; no observations are assumed independent here -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def pushforward (P : Law X) (f : X → Y) : Law Y := by
  classical
  exact {
    mass := fun y => ∑ x, if f x = y then P.mass x else 0
    nonneg := fun y => Finset.sum_nonneg (fun x _ => by
      split_ifs <;> first | exact P.nonneg x | exact le_rfl)
    total := by rw [Finset.sum_comm]; simpa using P.total }

theorem expectation_pushforward (P : Law X) (f : X → Y) (g : Y → ℝ) :
    rejection (pushforward P f) g = rejection P (fun x => g (f x)) := by
  classical
  unfold rejection pushforward
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem probability_pushforward (P : Law X) (f : X → Y) (A : Y → Prop) :
    probability (pushforward P f) A = probability P (fun x => A (f x)) := by
  classical
  have h := expectation_pushforward P f (fun y => if A y then 1 else 0)
  simpa only [rejection, probability, mul_ite, mul_one, mul_zero] using h

end Rhone.Statistics.DependentPairedTest
