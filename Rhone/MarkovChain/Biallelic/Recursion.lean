/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Biallelic.OneLocus
public import Rhone.LinearAlgebra.Recursion.Exist

/-! # The two-locus consequence: a biallelic locus needs no general mutation matrix -/

@[expose] public section

namespace Rhone.MarkovChain.Biallelic

open Finset LinearAlgebra.Recursion

variable {KB : ℕ} {F : Type*} [Field F]

theorem biallelic_isSolutionP_iff_left (h2 : (2 : F) ≠ 0) {u12 u21 : F} (hs : u12 + u21 ≠ 0)
    {θB ρ : F} {πB : Fin KB → F} (hπB : ∑ j, πB j = 1) (q : Config 2 KB → F) :
    IsSolutionP (thetaOf u12 u21) θB ρ (piOf u12 u21) πB
        (jump (thetaOf u12 u21) (rate2 u12 u21)) (fun _ j => πB j) q
      ↔ IsSolution (thetaOf u12 u21) θB ρ (piOf u12 u21) πB q :=
  isSolutionP_iff (wgt_jump_rate2 h2 hs) (wgt_const_rows hπB) q

theorem biallelic_isSolutionP_iff_right (h2 : (2 : F) ≠ 0) {u12 u21 : F} (hs : u12 + u21 ≠ 0)
    {KA : ℕ} {θA ρ : F} {πA : Fin KA → F} (hπA : ∑ i, πA i = 1) (q : Config KA 2 → F) :
    IsSolutionP θA (thetaOf u12 u21) ρ πA (piOf u12 u21)
        (fun _ i => πA i) (jump (thetaOf u12 u21) (rate2 u12 u21)) q
      ↔ IsSolution θA (thetaOf u12 u21) ρ πA (piOf u12 u21) q :=
  isSolutionP_iff (wgt_const_rows hπA) (wgt_jump_rate2 h2 hs) q

theorem biallelic_isSolutionP_iff (h2 : (2 : F) ≠ 0) {a12 a21 b12 b21 : F}
    (hsA : a12 + a21 ≠ 0) (hsB : b12 + b21 ≠ 0) {ρ : F} (q : Config 2 2 → F) :
    IsSolutionP (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21)
        (jump (thetaOf a12 a21) (rate2 a12 a21)) (jump (thetaOf b12 b21) (rate2 b12 b21)) q
      ↔ IsSolution (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21) q :=
  isSolutionP_iff (wgt_jump_rate2 h2 hsA) (wgt_jump_rate2 h2 hsB) q

theorem biallelic_eq_q [LinearOrder F] [IsStrictOrderedRing F] {a12 a21 b12 b21 ρ : F}
    (ha12 : 0 ≤ a12) (ha21 : 0 ≤ a21) (hsA : a12 + a21 ≠ 0)
    (hb12 : 0 ≤ b12) (hb21 : 0 ≤ b21) (hsB : b12 + b21 ≠ 0) (hρ : 0 ≤ ρ)
    {q' : Config 2 2 → F}
    (hq : IsSolutionP (thetaOf a12 a21) (thetaOf b12 b21) ρ (piOf a12 a21) (piOf b12 b21)
      (jump (thetaOf a12 a21) (rate2 a12 a21)) (jump (thetaOf b12 b21) (rate2 b12 b21)) q') :
    q' = q (πA := piOf a12 a21) (πB := piOf b12 b21) (thetaOf_pos ha12 ha21 hsA)
      (thetaOf_pos hb12 hb21 hsB) hρ := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  exact q_unique _ _ _ ((biallelic_isSolutionP_iff h2 hsA hsB q').mp hq)

end Rhone.MarkovChain.Biallelic
