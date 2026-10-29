/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.SymmetricNull
public import Rhone.Statistics.DependentPairedTest.Transport
public import Rhone.Statistics.DependentPairedTest.Features
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.BigOperators.Option

/-! # Null size bound for iid binary contrasts with equal means, via ternary encoding -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget

abbrev Ternary := Option Bool

def ternaryValue : Ternary → ℝ
  | none => 0
  | some b => if b then 1 else -1

def ternaryFlip : Ternary ≃ Ternary where
  toFun := Option.map Bool.not
  invFun := Option.map Bool.not
  left_inv := by intro x; cases x with | none => rfl | some b => cases b <;> rfl
  right_inv := by intro x; cases x with | none => rfl | some b => cases b <;> rfl

theorem ternary_flip_value (x : Ternary) : ternaryValue (ternaryFlip x) = -ternaryValue x := by
  cases x with
  | none => norm_num [ternaryFlip, ternaryValue]
  | some b => cases b <;> norm_num [ternaryFlip, ternaryValue]

theorem ternary_zero_mean_symmetric (P : Law Ternary) (h : rejection P ternaryValue = 0)
    (x : Ternary) : P.mass (ternaryFlip x) = P.mass x := by
  have hm : P.mass (some true) = P.mass (some false) := by
    simp [rejection, univ_option, ternaryValue] at h
    linarith
  cases x with
  | none => rfl
  | some b =>
    cases b
    · exact hm
    · exact hm.symm

noncomputable def ternaryEncode {X : Type*} (F G : X → ℝ) (x : X) : Ternary :=
  if F x - G x = 0 then none else if F x - G x = 1 then some true else some false

theorem ternary_encode_value {X : Type*} {F G : X → ℝ}
    (hF : Binary F) (hG : Binary G) (x : X) :
    ternaryValue (ternaryEncode F G x) = F x - G x := by
  rcases hF x with hf | hf <;> rcases hG x with hg | hg <;>
    norm_num [ternaryEncode, ternaryValue, hf, hg]

theorem iid_binary_null_size {X : Type*} [Fintype X] (P : Law X) (N : ℕ)
    {F G : X → ℝ} (hF : Binary F) (hG : Binary G)
    (hmean : rejection P F = rejection P G) :
    probability (iid P N) (fun x => Rejects (fun i => F (x i) - G (x i))) ≤
      (1 : ℝ) / 20 := by
  let Q := pushforward P (ternaryEncode F G)
  have hQ : rejection Q ternaryValue = 0 := by
    rw [expectation_pushforward]
    simp_rw [ternary_encode_value hF hG]
    change contrastMean P F G = 0
    rw [contrast_mean, hmean, sub_self]
  have h := symmetric_null_size Q N ternaryFlip ternaryValue
    (ternary_zero_mean_symmetric Q hQ) ternary_flip_value
  rw [← iid_probability_transport P N (ternaryEncode F G)] at h
  simpa only [ternary_encode_value hF hG] using h

end Rhone.Statistics.DependentPairedTest
