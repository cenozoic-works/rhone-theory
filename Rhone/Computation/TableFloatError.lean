/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Scientific
/-! # Maximum relative error for accepted table cells -/

@[expose] public section
namespace Rhone.Computation.TableFloatError

structure Cell where
  original : Rat
  word : Nat
  exponent : Int

def Cell.accepted (cell : Cell) : Bool :=
  Binary64Scientific.guardedAccepted cell.original cell.word cell.exponent

def Cell.relativeError (cell : Cell) : Rat :=
  match Binary64FiniteNearest.decodeFinite cell.word with
  | some value => |value - cell.original| / cell.original
  | none => 0

lemma Cell.accepted_decode {cell : Cell} (h : cell.accepted = true) :
    ∃ y, Binary64FiniteNearest.decodeFinite cell.word = some y := by
  have ha := Binary64Scientific.guarded_sound h
  simp only [Binary64Scientific.accepted, Bool.or_eq_true, decide_eq_true_eq] at ha
  rcases ha with ⟨_, hw⟩ | hp
  · refine ⟨0, ?_⟩
    rw [hw]
    norm_num [Binary64FiniteNearest.decodeFinite]
  · exact ⟨_, Binary64Scientific.normal_decode_finite
      (Binary64Normal.acceptedPositive_decode hp)⟩

lemma Cell.accepted_error {cell : Cell} (h : cell.accepted = true) :
    cell.relativeError ≤ 1 / (2 : Rat) ^ 53 := by
  obtain ⟨y, hy⟩ := Cell.accepted_decode h
  rw [Cell.relativeError, hy]
  exact Binary64Scientific.guarded_relative h hy

def maxRelativeError (cells : List Cell) : Rat :=
  (cells.map Cell.relativeError).foldr max 0

def accepted (cells : List Cell) : Bool := cells.all Cell.accepted

lemma maxRelativeError_bound {cells : List Cell} (h : accepted cells = true) :
    maxRelativeError cells ≤ 1 / (2 : Rat) ^ 53 := by
  induction cells with
  | nil => norm_num [maxRelativeError]
  | cons cell tail ih =>
    simp only [accepted, List.all_cons, Bool.and_eq_true] at h
    simp only [maxRelativeError, List.map_cons, List.foldr_cons, max_le_iff]
    exact ⟨Cell.accepted_error h.1, ih h.2⟩

lemma accepted_cell {cells : List Cell} (h : accepted cells = true)
    (cell : Cell) (hc : cell ∈ cells) : cell.accepted = true := by
  simp only [accepted, List.all_eq_true] at h
  exact h cell hc

lemma Cell.accepted_error_nonnegative {cell : Cell} (h : cell.accepted = true) :
    0 ≤ cell.relativeError := by
  have ha := Binary64Scientific.guarded_sound h
  simp only [Binary64Scientific.accepted, Bool.or_eq_true, decide_eq_true_eq] at ha
  rcases ha with ⟨hx, _⟩ | hp
  · simp [Cell.relativeError, hx]
    split <;> simp
  · simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at hp
    have hx : (0 : Rat) ≤ cell.original :=
      (le_of_lt (zpow_pos (show (0 : Rat) < 2 by norm_num) _)).trans hp.1
    unfold Cell.relativeError
    split <;> positivity

lemma maxRelativeError_upper {cells : List Cell} {cell : Cell} (h : cell ∈ cells) :
    cell.relativeError ≤ maxRelativeError cells := by
  induction cells with
  | nil => simp at h
  | cons head tail ih =>
    simp only [List.mem_cons] at h
    simp only [maxRelativeError, List.map_cons, List.foldr_cons]
    rcases h with he | ht
    · subst cell
      exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

lemma maxRelativeError_attained {cells : List Cell} (ha : accepted cells = true)
    (hne : cells ≠ []) : ∃ cell ∈ cells, maxRelativeError cells = cell.relativeError := by
  induction cells with
  | nil => contradiction
  | cons head tail ih =>
    simp only [accepted, List.all_cons, Bool.and_eq_true] at ha
    by_cases ht : tail = []
    · subst tail
      refine ⟨head, by simp, ?_⟩
      simp [maxRelativeError, max_eq_left (Cell.accepted_error_nonnegative ha.1)]
    · obtain ⟨cell, hc, he⟩ := ih ha.2 ht
      rcases le_total head.relativeError (maxRelativeError tail) with hlo | hhi
      · refine ⟨cell, by simp [hc], ?_⟩
        simp only [maxRelativeError, List.map_cons, List.foldr_cons]
        exact (max_eq_right hlo).trans he
      · refine ⟨head, by simp, ?_⟩
        simp only [maxRelativeError, List.map_cons, List.foldr_cons]
        exact max_eq_left hhi

end Rhone.Computation.TableFloatError
