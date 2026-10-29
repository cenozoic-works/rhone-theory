/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Pushforward

/-! # Exact iid transport to a finite feature alphabet -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem iid_pushforward_mass (P : Law X) (N : ℕ) (f : X → Y) (y : Fin N → Y) :
    (pushforward (iid P N) (fun x i => f (x i))).mass y =
      (iid (pushforward P f) N).mass y := by
  classical
  simp only [pushforward, iid]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun h i)]
  · simp only [ite_eq_right h]
    symm
    have hn : ∃ i, f (x i) ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem iid_expectation_transport (P : Law X) (N : ℕ) (f : X → Y)
    (g : (Fin N → Y) → ℝ) :
    rejection (iid P N) (fun x => g (fun i => f (x i))) =
      rejection (iid (pushforward P f) N) g := by
  rw [← expectation_pushforward]
  unfold rejection
  simp_rw [iid_pushforward_mass]

theorem iid_probability_transport (P : Law X) (N : ℕ) (f : X → Y)
    (A : (Fin N → Y) → Prop) :
    probability (iid P N) (fun x => A (fun i => f (x i))) =
      probability (iid (pushforward P f) N) A := by
  rw [← probability_pushforward]
  unfold probability
  simp_rw [iid_pushforward_mass]

end Rhone.Statistics.DependentPairedTest
