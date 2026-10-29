/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.SourceProof
import Mathlib.Tactic.LinearCombination

/-! # Source dependence on smaller valid blocks -/

@[expose] public section

namespace Rhone.Computation

theorem source_eq_srcR_of_lower (p : Params) (tab : PhiTable) (value : Nat → Nat → Nat → Rat)
    (i j t : Nat) (ht : t ≤ min i j)
    (h : ∀ a b d, a ≤ i → b ≤ j → a + b < i + j → d ≤ min a b →
      tab.get a b d = value a b d) :
    source p tab i j t = Rhone.Probability.ExplicitFormula.srcR
      (p.piA.getD 0 0 * p.piA.getD 1 0)
      (p.piA.getD 1 0 - p.piA.getD 0 0)
      (p.piB.getD 0 0 * p.piB.getD 1 0)
      (p.piB.getD 1 0 - p.piB.getD 0 0) value i j t := by
  have hi : t ≤ i := le_trans ht (min_le_left _ _)
  have hj : t ≤ j := le_trans ht (min_le_right _ _)
  have key : ∀ (coef a b d : Nat), a ≤ i → b ≤ j →
      (coef = 0 ∨ (a + b < i + j ∧ d ≤ min a b)) →
      (coef : Rat) * tab.get a b d = (coef : Rat) * value a b d := by
    intro coef a b d ha hb hc
    rcases hc with hz | ⟨hd, ht'⟩
    · simp [hz]
    · rw [h a b d ha hb hd ht']
  have c1 := key ((i - t) * (i - t - 1)) (i - 2) j t (Nat.sub_le _ _) le_rfl (by
    by_cases hc : (i - t) * (i - t - 1) = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have c2 := key ((i - t) * t) (i - 2) j (t - 1) (Nat.sub_le _ _) le_rfl (by
    by_cases hc : (i - t) * t = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have c3 := key ((i - t) * (i + t - 1)) (i - 1) j t (Nat.sub_le _ _) le_rfl (by
    by_cases hc : (i - t) * (i + t - 1) = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have c4 := key ((j - t) * (j - t - 1)) i (j - 2) t le_rfl (Nat.sub_le _ _) (by
    by_cases hc : (j - t) * (j - t - 1) = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have c5 := key ((j - t) * t) i (j - 2) (t - 1) le_rfl (Nat.sub_le _ _) (by
    by_cases hc : (j - t) * t = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have c6 := key ((j - t) * (j + t - 1)) i (j - 1) t le_rfl (Nat.sub_le _ _) (by
    by_cases hc : (j - t) * (j + t - 1) = 0
    · exact Or.inl hc
    · right
      have hp := Nat.pos_of_ne_zero hc
      have hleft := Nat.pos_of_mul_pos_right hp
      have hright := Nat.pos_of_mul_pos_left hp
      exact ⟨by omega, le_min (by omega) (by omega)⟩)
  have qkey : ∀ a b d : Nat, a ≤ i → b ≤ j →
      (2 ≤ t → a + b < i + j ∧ d ≤ min a b) →
      ((t * (t - 1) : Nat) : Rat) * tab.get a b d =
        ((t * (t - 1) : Nat) : Rat) * value a b d := by
    intro a b d ha hb hab
    apply key _ _ _ _ ha hb
    by_cases h2 : 2 ≤ t
    · exact Or.inr (hab h2)
    · left
      have hz : t = 0 ∨ t = 1 := by omega
      rcases hz with rfl | rfl <;> simp
  have c7 := qkey (i - 2) (j - 2) (t - 2)
    (Nat.sub_le _ _) (Nat.sub_le _ _)
    (fun h2 => ⟨by omega, le_min (by omega) (by omega)⟩)
  have c8 := qkey (i - 2) (j - 1) (t - 2)
    (Nat.sub_le _ _) (Nat.sub_le _ _)
    (fun h2 => ⟨by omega, le_min (by omega) (by omega)⟩)
  have c9 := qkey (i - 1) (j - 2) (t - 2)
    (Nat.sub_le _ _) (Nat.sub_le _ _)
    (fun h2 => ⟨by omega, le_min (by omega) (by omega)⟩)
  have c10 := qkey (i - 1) (j - 1) (t - 1)
    (Nat.sub_le _ _) (Nat.sub_le _ _)
    (fun h2 => ⟨by omega, le_min (by omega) (by omega)⟩)
  rw [source_eq_srcR]
  unfold Rhone.Probability.ExplicitFormula.srcR
  linear_combination
    (p.piA.getD 0 0 * p.piA.getD 1 0) * c1 +
    2 * (p.piA.getD 0 0 * p.piA.getD 1 0) * c2 +
    (p.piA.getD 1 0 - p.piA.getD 0 0) * c3 +
    (p.piB.getD 0 0 * p.piB.getD 1 0) * c4 +
    2 * (p.piB.getD 0 0 * p.piB.getD 1 0) * c5 +
    (p.piB.getD 1 0 - p.piB.getD 0 0) * c6 +
    (p.piA.getD 0 0 * p.piA.getD 1 0) * (p.piB.getD 0 0 * p.piB.getD 1 0) * c7 +
    (p.piA.getD 0 0 * p.piA.getD 1 0) * (p.piB.getD 1 0 - p.piB.getD 0 0) * c8 +
    (p.piA.getD 1 0 - p.piA.getD 0 0) * (p.piB.getD 0 0 * p.piB.getD 1 0) * c9 +
    (p.piA.getD 1 0 - p.piA.getD 0 0) * (p.piB.getD 1 0 - p.piB.getD 0 0) * c10

end Rhone.Computation
