/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.PIM
public import Rhone.MarkovChain.Biallelic.Recursion

/-! # A biallelic pair needs no general mutation matrix — for the *unkilled* form too -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion Biallelic

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem piOf_pos {u12 u21 : F} (h12 : 0 < u12) (h21 : 0 < u21) (i : Fin 2) :
    0 < piOf u12 u21 i := by
  have hpos : 0 < u12 + u21 := by linarith
  have key : ∀ i : Fin 2, 0 < piOf u12 u21 i := by
    rw [Fin.forall_fin_two, piOf_zero, piOf_one]
    exact ⟨div_pos h21 hpos, div_pos h12 hpos⟩
  exact key i

theorem biallelic_isSolutionGen_iff {a12 a21 b12 b21 ρ : F}
    (ha12 : 0 < a12) (ha21 : 0 < a21) (hb12 : 0 < b12) (hb21 : 0 < b21) (hρ : 0 ≤ ρ)
    (q : Config 2 2 → F) :
    IsSolutionGen (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21)
        (jump (thetaOf a12 a21) (rate2 a12 a21)) (jump (thetaOf b12 b21) (rate2 b12 b21)) q
      ↔ IsSolution (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21) q := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hsA : a12 + a21 ≠ 0 := by positivity
  have hsB : b12 + b21 ≠ 0 := by positivity
  rw [jump_rate2 h2 hsA, jump_rate2 h2 hsB]
  exact isSolutionGen_iff (thetaOf_pos ha12.le ha21.le hsA) (thetaOf_pos hb12.le hb21.le hsB) hρ
    (piOf_pos ha12 ha21) (piOf_pos hb12 hb21) (sum_piOf hsA) (sum_piOf hsB) q

theorem biallelic_eq_q {a12 a21 b12 b21 ρ : F}
    (ha12 : 0 < a12) (ha21 : 0 < a21) (hb12 : 0 < b12) (hb21 : 0 < b21) (hρ : 0 ≤ ρ)
    {q' : Config 2 2 → F}
    (hq : IsSolutionGen (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21)
      (jump (thetaOf a12 a21) (rate2 a12 a21)) (jump (thetaOf b12 b21) (rate2 b12 b21)) q') :
    q' = LinearAlgebra.Recursion.q (πA := piOf a12 a21) (πB := piOf b12 b21)
      (thetaOf_pos ha12.le ha21.le (by positivity))
      (thetaOf_pos hb12.le hb21.le (by positivity)) hρ :=
  LinearAlgebra.Recursion.q_unique _ _ _
    ((biallelic_isSolutionGen_iff ha12 ha21 hb12 hb21 hρ q').mp hq)

end Rhone.MarkovChain.GeneralMutation
