/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Basic.Real.Basic

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSpan

inductive Span where
  | full | left | right
  deriving DecidableEq

def Compatible : Span → Span → Prop
  | .left, .left => False
  | .right, .right => False
  | _, _ => True

def merge : Span → Span → Span
  | .left, .left => .left
  | .right, .right => .right
  | _, _ => .full

def Valid (s : List Span) : Prop := s.Pairwise Compatible

theorem compatible_symm (a b : Span) : Compatible a b ↔ Compatible b a := by
  cases a <;> cases b <;> simp [Compatible]

theorem compatible_merge (a b c : Span)
    (ha : Compatible a c) (hb : Compatible b c) : Compatible (merge a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [Compatible, merge]

theorem valid_coalescence (a b : Span) (s : List Span)
    (h : Valid (a :: b :: s)) : Valid (merge a b :: s) := by
  simp only [Valid, List.pairwise_cons] at h ⊢
  refine ⟨?_, h.2.2⟩
  intro c hc
  exact compatible_merge a b c (h.1 c (by simp [hc])) (h.2.1 c hc)

theorem valid_perm (s t : List Span) (hp : s.Perm t) (h : Valid s) : Valid t := by
  exact h.perm hp (fun {a b} hab => (compatible_symm a b).mp hab)

theorem valid_coalescence_any (s : List Span) (a b : Span) (rest : List Span)
    (hp : s.Perm (a :: b :: rest)) (h : Valid s) : Valid (merge a b :: rest) := by
  exact valid_coalescence a b rest (valid_perm s (a :: b :: rest) hp h)

theorem valid_initial (n : ℕ) : Valid (List.replicate n Span.full) := by
  simp [Valid, Compatible]

theorem valid_first_split (n : ℕ) :
    Valid (Span.left :: Span.right :: List.replicate n Span.full) := by
  simp [Valid, List.pairwise_cons, Compatible, List.mem_replicate]

def lo (x : ℝ) : Span → ℝ
  | .right => x
  | _ => 0

def hi (x : ℝ) : Span → ℝ
  | .left => x
  | _ => 1

def Touches (x : ℝ) (a b : Span) : Prop :=
  lo x a ≤ hi x b ∧ lo x b ≤ hi x a

theorem compatible_touches (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a b : Span) (h : Compatible a b) : Touches x a b := by
  cases a <;> cases b <;> simp_all [Compatible, Touches, lo, hi]

theorem merge_endpoints (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a b : Span) :
    lo x (merge a b) = min (lo x a) (lo x b) ∧
    hi x (merge a b) = max (hi x a) (hi x b) := by
  cases a <;> cases b <;>
    simp [lo, hi, merge, min_eq_left hx0, min_eq_right hx0,
      max_eq_left hx1, max_eq_right hx1]

theorem valid_pairs_touch (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (s : List Span) (h : Valid s) : s.Pairwise (Touches x) := by
  exact h.imp (fun {a b} hab => compatible_touches x hx0 hx1 a b hab)

inductive Reachable : List Span → Prop where
  | initial (n : ℕ) : Reachable (List.replicate n .full)
  | firstSplit (n : ℕ) : Reachable (.left :: .right :: List.replicate n .full)
  | perm {s t : List Span} : Reachable s → s.Perm t → Reachable t
  | coalesce {a b : Span} {s : List Span} :
      Reachable (a :: b :: s) → Reachable (merge a b :: s)

theorem reachable_valid (s : List Span) (h : Reachable s) : Valid s := by
  induction h with
  | initial n => exact valid_initial n
  | firstSplit n => exact valid_first_split n
  | perm _ hp ih => exact valid_perm _ _ hp ih
  | coalesce _ ih => exact valid_coalescence _ _ _ ih

theorem reachable_pairs_touch (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (s : List Span) (h : Reachable s) : s.Pairwise (Touches x) := by
  exact valid_pairs_touch x hx0 hx1 s (reachable_valid s h)

def argRate (_a _b : Span) : ℝ := 1

noncomputable def smcRate (x : ℝ) (a b : Span) : ℝ := by
  classical
  exact if Touches x a b then 1 else 0

theorem reachable_coalescence_rates (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (s : List Span) (h : Reachable s) :
    s.Pairwise (fun a b => smcRate x a b = argRate a b) := by
  apply (reachable_pairs_touch x hx0 hx1 s h).imp
  intro a b hab
  simp [smcRate, argRate, hab]

def spanLength (x : ℝ) (a : Span) : ℝ := hi x a - lo x a

theorem spanLength_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a : Span) :
    0 ≤ spanLength x a ∧ spanLength x a ≤ 1 := by
  cases a with
  | full => simp [spanLength, lo, hi]
  | left => simpa [spanLength, lo, hi] using And.intro hx0 hx1
  | right =>
    simpa [spanLength, lo, hi] using
      And.intro (sub_nonneg.mpr hx1) (sub_le_self (1 : ℝ) hx0)

theorem daughter_lengths (x : ℝ) :
    spanLength x .left + spanLength x .right = 1 := by
  simp only [spanLength, lo, hi, sub_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

end Rhone.Coalescent.SmcSpan
