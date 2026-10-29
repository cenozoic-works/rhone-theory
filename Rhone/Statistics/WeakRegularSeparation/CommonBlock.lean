/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.PaddedWords

/-! # Common finite block for an arbitrary finite collection of monomials -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites

theorem common_block_words (S : Finset (Fin 3 → ℕ)) :
    ∃ L : ℕ, ∃ w : (n : S) → Fin L → Option (Fin 3),
      ∀ (n : S) (x : Cube 3), (∏ j, optionalCoordinate (w n j) x) =
        ∏ i, (x i).val ^ n.val i := by
  classical
  let A := Σ n : S, Σ i : Fin 3, Fin (n.val i)
  let e := Fintype.equivFin A
  refine ⟨Fintype.card A, fun n j =>
    if (e.symm j).1 = n then some (e.symm j).2.1 else none, ?_⟩
  intro n x
  rw [← e.prod_comp (fun j => optionalCoordinate
    (if (e.symm j).1 = n then some (e.symm j).2.1 else none) x)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.prod_sigma]
  rw [Finset.prod_eq_single n]
  · simp only [ite_true, optionalCoordinate, Option.elim_some, Fintype.prod_sigma]
    have he (i : Fin 3) (j : Fin (n.val i)) :
        (e.symm (e ⟨n, ⟨i, j⟩⟩)).2.1 = i :=
      congrArg (fun a : A => a.2.1) (e.symm_apply_apply ⟨n, ⟨i, j⟩⟩)
    simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro b _ hbn
    simp [hbn, optionalCoordinate]
  · simp

def blockDistance {K L : ℕ} (k l : ℝ) (μ ν : Measure Joint) (hK : 0 < K) : ℝ :=
  ∑ x : Panel K L, |jointMass (uniformBlockRoots K L hK) k μ x -
    jointMass (uniformBlockRoots K L hK) l ν x|

theorem padded_moment_distance {K L : ℕ} (hK : 2 ≤ K) {k l : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν)
    (w : Fin L → Option (Fin 3)) :
    |(∫ x, ∏ j, optionalCoordinate (w j) x ∂μ.map (encode k)) -
      (∫ x, ∏ j, optionalCoordinate (w j) x ∂ν.map (encode l))| ≤
        blockDistance (K := K) (L := L) k l μ ν (by omega) := by
  rw [padded_word_moment hK hk μ hμ, padded_word_moment hK hl ν hν,
    ← Finset.sum_sub_distrib]
  unfold blockDistance
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [← mul_sub, abs_mul]
  apply mul_le_of_le_one_left (abs_nonneg _)
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    (fun j _ => optional_score_bound hK (w j) (x j))

end Rhone.Statistics.WeakRegularSeparation
