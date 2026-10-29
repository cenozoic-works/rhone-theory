/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Finite diploid pedigrees

Source: wright1922, p. 333. -/

@[expose] public section

namespace Rhone.Combinatorics

structure Pedigree (n : ℕ) where
  parents : Fin n → Option (Fin n × Fin n)
  parents_lt : ∀ i p, parents i = some p → p.1 < i ∧ p.2 < i

namespace Pedigree

variable {n : ℕ} (P : Pedigree n)

def parent (i : Fin n) (s : Fin 2) : Option (Fin n) :=
  (P.parents i).map fun p => if s = 0 then p.1 else p.2

theorem parent_of_founder {i : Fin n} (h : P.parents i = none) (s : Fin 2) :
    P.parent i s = none := by
  simp [parent, h]

theorem parent_zero {i : Fin n} {p : Fin n × Fin n} (h : P.parents i = some p) :
    P.parent i 0 = some p.1 := by
  simp [parent, h]

theorem parent_one {i : Fin n} {p : Fin n × Fin n} (h : P.parents i = some p) :
    P.parent i 1 = some p.2 := by
  simp [parent, h]

theorem parent_lt {i p : Fin n} {s : Fin 2} (h : P.parent i s = some p) : p < i := by
  unfold parent at h
  cases hq : P.parents i with
  | none => simp [hq] at h
  | some q =>
    have hlt := P.parents_lt i q hq
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    split_ifs at h
    · exact h ▸ hlt.1
    · exact h ▸ hlt.2

def follow : Fin n → List (Fin 2) → Option (Fin n)
  | i, [] => some i
  | i, s :: l => (P.parent i s).bind fun p => follow p l

def visited : Fin n → List (Fin 2) → Finset (Fin n)
  | i, [] => {i}
  | i, s :: l =>
    insert i (match P.parent i s with
      | none => ∅
      | some p => visited p l)

def chains (i a : Fin n) : Finset (List (Fin 2)) :=
  (if i = a then {[]} else ∅) ∪
    (Finset.univ : Finset (Fin 2)).biUnion fun s =>
      match _h : P.parent i s with
      | none => ∅
      | some p => (chains p a).image (List.cons s)
termination_by i.val
decreasing_by exact P.parent_lt (by assumption)

theorem chains_eq (i a : Fin n) :
    P.chains i a = (if i = a then {[]} else ∅) ∪
      (Finset.univ : Finset (Fin 2)).biUnion fun s =>
        (P.parent i s).elim ∅ fun p => (P.chains p a).image (List.cons s) := by
  rw [chains]
  congr 1
  refine Finset.biUnion_congr rfl fun s _ => ?_
  split
  · next h => rw [h]; rfl
  · next p h => rw [h]; rfl

theorem nil_mem_chains (i a : Fin n) : [] ∈ P.chains i a ↔ i = a := by
  rw [chains_eq]
  by_cases h : i = a
  · simp [h]
  · simp only [h, ite_false, Finset.empty_union, Finset.mem_biUnion, Finset.mem_univ,
      true_and, iff_false, not_exists]
    intro s
    cases P.parent i s <;> simp

theorem cons_mem_chains (i a : Fin n) (s : Fin 2) (l : List (Fin 2)) :
    s :: l ∈ P.chains i a ↔ ∃ p, P.parent i s = some p ∧ l ∈ P.chains p a := by
  rw [chains_eq]
  have hnil : s :: l ∉ (if i = a then ({[]} : Finset (List (Fin 2))) else ∅) := by
    split_ifs <;> simp
  simp only [Finset.mem_union, hnil, false_or, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    cases hp : P.parent i t with
    | none => simp [hp] at ht
    | some q =>
      rw [hp] at ht
      simp only [Option.elim_some, Finset.mem_image, List.cons.injEq] at ht
      obtain ⟨l', hl', hts, rfl⟩ := ht
      subst hts
      exact ⟨q, hp, hl'⟩
  · rintro ⟨q, hq, hl⟩
    refine ⟨s, ?_⟩
    rw [hq]
    exact Finset.mem_image_of_mem _ hl

theorem follow_le {i a : Fin n} {l : List (Fin 2)} (h : P.follow i l = some a) : a ≤ i := by
  induction l generalizing i with
  | nil =>
    simp only [follow, Option.some.injEq] at h
    exact h ▸ le_rfl
  | cons s l ih =>
    cases hp : P.parent i s with
    | none => simp [follow, hp] at h
    | some q =>
      simp only [follow, hp, Option.bind_some] at h
      exact (ih h).trans (P.parent_lt hp).le

theorem follow_eq_self_iff (i : Fin n) (l : List (Fin 2)) :
    P.follow i l = some i ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons s l =>
      cases hp : P.parent i s with
      | none => simp [follow, hp] at h
      | some q =>
        simp only [follow, hp, Option.bind_some] at h
        exact absurd (P.follow_le h) (not_le.mpr (P.parent_lt hp))
  · rintro rfl
    rfl

theorem mem_chains (i a : Fin n) (l : List (Fin 2)) :
    l ∈ P.chains i a ↔ P.follow i l = some a := by
  induction l generalizing i with
  | nil => simp [nil_mem_chains, follow]
  | cons s l ih =>
    rw [cons_mem_chains]
    cases hp : P.parent i s with
    | none => simp [follow, hp]
    | some q => simp [follow, hp, ih]

theorem self_mem_visited (i : Fin n) (l : List (Fin 2)) : i ∈ P.visited i l := by
  cases l <;> simp [visited]

theorem visited_le {i v : Fin n} {l : List (Fin 2)} (h : v ∈ P.visited i l) : v ≤ i := by
  induction l generalizing i with
  | nil =>
    simp only [visited, Finset.mem_singleton] at h
    exact h ▸ le_rfl
  | cons s l ih =>
    simp only [visited, Finset.mem_insert] at h
    rcases h with h | h
    · exact h ▸ le_rfl
    · cases hp : P.parent i s with
      | none => simp [hp] at h
      | some q =>
        rw [hp] at h
        exact (ih h).trans (P.parent_lt hp).le

end Pedigree

end Rhone.Combinatorics
