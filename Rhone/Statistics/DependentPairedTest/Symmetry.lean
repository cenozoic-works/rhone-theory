/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Statistic

/-! # Sign-cancellation proof for the self-normalized null rule -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

noncomputable def flipCoordinate (N : ℕ) (e : X ≃ X) (i : Fin N) :
    (Fin N → X) ≃ (Fin N → X) :=
  Equiv.piCongrRight (fun j => if j = i then e else Equiv.refl X)

theorem flip_mass (P : Law X) (N : ℕ) (e : X ≃ X)
    (he : ∀ x, P.mass (e x) = P.mass x) (i : Fin N) (x : Fin N → X) :
    (iid P N).mass (flipCoordinate N e i x) = (iid P N).mass x := by
  change (∏ j, P.mass (flipCoordinate N e i x j)) = ∏ j, P.mass (x j)
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i <;> simp [flipCoordinate, Equiv.piCongrRight, hji, he]

omit [Fintype X] in
theorem flip_square (N : ℕ) (e : X ≃ X) (f : X → ℝ)
    (he : ∀ x, f (e x) = -f x) (i : Fin N) (x : Fin N → X) :
    squareStatistic (fun j => f (flipCoordinate N e i x j)) =
      squareStatistic (fun j => f (x j)) := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i <;> simp [flipCoordinate, Equiv.piCongrRight, hji, he]

theorem cross_ratio_zero (P : Law X) (N : ℕ) (e : X ≃ X) (f : X → ℝ)
    (hP : ∀ x, P.mass (e x) = P.mass x) (hf : ∀ x, f (e x) = -f x)
    (i j : Fin N) (hij : i ≠ j) :
    rejection (iid P N) (fun x => f (x i) * f (x j) /
      squareStatistic (fun k => f (x k))) = 0 := by
  have h := (flipCoordinate N e i).sum_comp (fun x =>
    (iid P N).mass x * (f (x i) * f (x j) / squareStatistic (fun k => f (x k))))
  have heq : ∀ x : Fin N → X,
      (iid P N).mass (flipCoordinate N e i x) *
        (f (flipCoordinate N e i x i) * f (flipCoordinate N e i x j) /
          squareStatistic (fun k => f (flipCoordinate N e i x k))) =
      -((iid P N).mass x * (f (x i) * f (x j) /
          squareStatistic (fun k => f (x k)))) := by
    intro x
    rw [flip_mass P N e hP, flip_square N e f hf]
    simp [flipCoordinate, Equiv.piCongrRight, Ne.symm hij, hf, neg_div, mul_neg]
  simp_rw [heq] at h
  rw [Finset.sum_neg_distrib] at h
  unfold rejection
  linarith

end Rhone.Statistics.DependentPairedTest
