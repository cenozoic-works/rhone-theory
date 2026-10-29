/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Statistic

/-! # Copied fair-sign counterexample with exact across-replicate dependence -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget

noncomputable def fairSign : Law Bool where
  mass := fun _ => 1/2
  nonneg := fun _ => by norm_num
  total := by simp

noncomputable def copiedSign (N : ℕ) (b : Bool) : Fin N → ℝ :=
  fun _ => if b then 1 else -1

theorem copied_sign_mean_zero (N : ℕ) (i : Fin N) :
    rejection fairSign (fun b => copiedSign N b i) = 0 := by
  simp [rejection, fairSign, copiedSign]

theorem copied_sign_rejects {N : ℕ} (hN : 20 ≤ N) (b : Bool) :
    Rejects (copiedSign N b) := by
  have hn : (20 : ℝ) ≤ N := by exact_mod_cast hN
  cases b <;> simp [Rejects, sumStatistic, squareStatistic, copiedSign]
  all_goals constructor <;> nlinarith

theorem copied_sign_rejection_probability {N : ℕ} (hN : 20 ≤ N) :
    probability fairSign (fun b => Rejects (copiedSign N b)) = 1 := by
  classical
  simp only [probability, copied_sign_rejects hN, ite_true]
  exact fairSign.total

end Rhone.Statistics.DependentPairedTest
