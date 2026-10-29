/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Converse.Reduced

/-! # Numeric check values for the reduced `t = 0` recursion -/

@[expose] public section

namespace Rhone.Probability.Converse

open Finset LinearAlgebra.Recursion

example : Gcoef (2 : ℝ) ![1 / 2, 1 / 2] ![2, 0] 0 = -1 / 2 := by
  norm_num [Gcoef, Fin.sum_univ_two]

example : Gcoef (3 : ℝ) ![1 / 2, 1 / 2] ![2, 0] 0 = -3 / 5 := by
  norm_num [Gcoef, Fin.sum_univ_two]

example : Phi (2 : ℝ) ![1 / 2, 1 / 2] ![2, 0] = -1 := by
  norm_num [Phi, Gcoef, Fin.sum_univ_two]

example : Phi (3 : ℝ) ![1 / 2, 1 / 2] ![2, 0] = -6 / 5 := by
  norm_num [Phi, Gcoef, Fin.sum_univ_two]

example : ((∑ k, (![2, 0] : Fin 2 → ℕ) k : ℕ) : ℝ)
      * (((∑ k, (![2, 0] : Fin 2 → ℕ) k : ℕ) : ℝ) - 1)
    - uu (2 : ℝ) (∑ k, (![2, 0] : Fin 2 → ℕ) k)
      * ∑ i, ((![2, 0] : Fin 2 → ℕ) i : ℝ) * (((![2, 0] : Fin 2 → ℕ) i : ℝ) - 1)
          / ((2 : ℝ) * (![1 / 2, 1 / 2] : Fin 2 → ℝ) i + ((![2, 0] : Fin 2 → ℕ) i : ℝ) - 1)
    = -1 := by
  norm_num [uu, Fin.sum_univ_two]

example : uu (2 : ℝ) 2 = 3 := by norm_num [uu]

example : uu (3 : ℝ) 2 = 4 := by norm_num [uu]

example : qOne (2 : ℝ) ![1 / 2, 1 / 2] ![2, 0] = 1 / 3 := by
  norm_num [qOne, rising, Fin.prod_univ_two, Fin.sum_univ_two, Finset.prod_range_succ]

example : qOne (3 : ℝ) ![1 / 2, 1 / 2] ![2, 0] = 5 / 16 := by
  norm_num [qOne, rising, Fin.prod_univ_two, Fin.sum_univ_two, Finset.prod_range_succ]

example : (2 * uu (2 : ℝ) 2 + 2 * uu (3 : ℝ) 2) * (12 / 35)
    = 4 * (-1 : ℝ) * (-6 / 5) := by
  norm_num [uu]

example : (1 / 3 : ℝ) * (5 / 16) * (12 / 35) = 1 / 28 := by norm_num

example : Mono (![2, 0] : Fin 2 → ℕ) := ⟨0, by decide⟩

example : mu (![2, 0] : Fin 2 → ℕ) + mu (![2, 0] : Fin 2 → ℕ) = 2 := by decide

end Rhone.Probability.Converse
