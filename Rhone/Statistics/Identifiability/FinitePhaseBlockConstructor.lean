/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseModel

/-! # Construct the full two-stage model from its pre, post, and transition blocks -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix
namespace Rhone.Statistics.Identifiability.FinitePhase
variable {n m : ℕ}

def blockGenerator (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℝ :=
  Fin.addCases (fun i => Fin.addCases (fun j => A i j) (fun j => F i j))
    (fun i => Fin.addCases (fun _ => 0) (fun j => B i j))

lemma blockGenerator_metzler (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hA : IsMetzler A) (hF : ∀ i j, 0 ≤ F i j) (hB : IsMetzler B) :
    IsMetzler (blockGenerator A F B) := by
  intro i j hij
  revert hij
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      simpa only [blockGenerator, Fin.addCases_left] using
        hA i j (fun h => hij (congrArg (Fin.castAdd m) h))
    · intro _
      simpa only [blockGenerator, Fin.addCases_left, Fin.addCases_right] using hF i j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro _
      simp [blockGenerator]
    · intro hij
      simpa only [blockGenerator, Fin.addCases_right] using
        hB i j (fun h => hij (congrArg (Fin.natAdd n) h))

lemma blockGenerator_pre_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hflux : F *ᵥ (fun _ => 1) = exitRate A) (i : Fin n) :
    ∑ j, blockGenerator A F B (Fin.castAdd m i) j = 0 := by
  have h := congrFun hflux i
  simp only [exitRate, Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply] at h
  simp only [Fin.sum_univ_add, blockGenerator, Fin.addCases_left, Fin.addCases_right]
  linarith

lemma blockGenerator_post_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    ∑ j, blockGenerator A F B (Fin.natAdd n i) j = ∑ j, B i j := by
  simp [Fin.sum_univ_add, blockGenerator]

def Model.ofBlocks (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    (hA : IsMetzler A) (hAr : ∀ i, (∑ j, A i j) ≤ 0)
    (hB : IsMetzler B) (hBr : ∀ i, (∑ j, B i j) ≤ 0)
    (hF : ∀ i j, 0 ≤ F i j) (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    (hflux : F *ᵥ (fun _ => 1) = exitRate A) : Model n m where
  A := A
  B := B
  F := F
  N := blockGenerator A F B
  α := α
  A_metzler := hA
  B_metzler := hB
  N_metzler := blockGenerator_metzler A F B hA hF hB
  A_rows := hAr
  B_rows := hBr
  N_rows := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [blockGenerator_pre_sum A F B hflux]
    · rw [blockGenerator_post_sum]
      exact hBr i
  F_nonnegative := hF
  α_nonnegative := hα
  α_sum := hαsum
  flux := hflux
  pre_pre := by intros; simp [blockGenerator]
  post_pre := by intros; simp [blockGenerator]
  pre_post := by intros; simp [blockGenerator]
  post_post := by intros; simp [blockGenerator]
  exit_pre := by
    intro i
    simp only [exitRate, Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply]
    rw [blockGenerator_pre_sum A F B hflux, neg_zero]
  exit_post := by
    intro i
    simp only [exitRate, Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply]
    rw [blockGenerator_post_sum]

end Rhone.Statistics.Identifiability.FinitePhase
