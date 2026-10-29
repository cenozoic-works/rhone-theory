/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs

/-! # Semantic parameter validation -/

@[expose] public section

namespace Rhone.Computation

private theorem array_eq_pair {α : Type} (xs : Array α) (fallback : α)
    (hsize : xs.size = 2) :
    xs = #[xs.getD 0 fallback, xs.getD 1 fallback] := by
  rcases xs with ⟨xs⟩
  cases xs with
  | nil => simp at hsize
  | cons a xs =>
    cases xs with
    | nil => simp at hsize
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs => simp only [Array.size, List.length_cons] at hsize; omega

private theorem array_domain_iff (xs : Array Rat) (hsize : xs.size = 2) :
    (xs.all (· > 0) = true ∧ xs.foldl (· + ·) 0 = 1) ↔
      (∀ i : Fin 2, 0 < xs.getD i.val 0) ∧
      (∑ i : Fin 2, xs.getD i.val 0) = 1 := by
  rw [array_eq_pair xs 0 hsize]
  simp [Fin.forall_fin_two, Fin.sum_univ_two]

theorem Params.valid_iff (p : Params) :
    p.valid = true ↔
      0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho ∧
      p.piA.size = 2 ∧ p.piB.size = 2 ∧
      (∀ i : Fin 2, 0 < p.piA.getD i.val 0) ∧
      (∀ i : Fin 2, 0 < p.piB.getD i.val 0) ∧
      (∑ i : Fin 2, p.piA.getD i.val 0) = 1 ∧
      (∑ i : Fin 2, p.piB.getD i.val 0) = 1 := by
  simp only [Params.valid, Bool.and_eq_true_iff, decide_eq_true_eq, beq_iff_eq,
    and_assoc]
  constructor
  · rintro ⟨hθA, hθB, hρ, ha, hb, hpa, hpb, hsa, hsb⟩
    obtain ⟨hpa', hsa'⟩ := (array_domain_iff p.piA ha).mp ⟨hpa, hsa⟩
    obtain ⟨hpb', hsb'⟩ := (array_domain_iff p.piB hb).mp ⟨hpb, hsb⟩
    exact ⟨hθA, hθB, hρ, ha, hb, hpa', hpb', hsa', hsb'⟩
  · rintro ⟨hθA, hθB, hρ, ha, hb, hpa, hpb, hsa, hsb⟩
    obtain ⟨hpa', hsa'⟩ := (array_domain_iff p.piA ha).mpr ⟨hpa, hsa⟩
    obtain ⟨hpb', hsb'⟩ := (array_domain_iff p.piB hb).mpr ⟨hpb, hsb⟩
    exact ⟨hθA, hθB, hρ, ha, hb, hpa', hpb', hsa', hsb'⟩

end Rhone.Computation
