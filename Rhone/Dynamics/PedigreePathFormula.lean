/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.PedigreeKinship
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The path formula for kinship on a finite pedigree

Source: wright1922, p. 334. -/

@[expose] public section

namespace Rhone.Combinatorics.Pedigree

variable {n : ℕ}

def pathSum (P : Pedigree n) (i j : Fin n) : ℚ :=
  ∑ a, ∑ c₁ ∈ P.chains i a, ∑ c₂ ∈ P.chains j a,
    if P.visited i c₁ ∩ P.visited j c₂ ⊆ {a} then
      (1 / 2 : ℚ) ^ (c₁.length + c₂.length + 1) * (1 + P.inbreeding a)
    else 0

theorem visited_cons (P : Pedigree n) {i q : Fin n} {s : Fin 2} (h : P.parent i s = some q)
    (l : List (Fin 2)) : P.visited i (s :: l) = insert i (P.visited q l) := by
  simp [visited, h]

theorem chains_of_founder (P : Pedigree n) {j a : Fin n} (hj : P.parents j = none)
    (hja : j ≠ a) : P.chains j a = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  cases l with
  | nil => exact hja ((P.nil_mem_chains j a).mp hl)
  | cons s l =>
    obtain ⟨q, hq, _⟩ := (P.cons_mem_chains j a s l).mp hl
    rw [P.parent_of_founder hj s] at hq
    cases hq

theorem chains_of_parents (P : Pedigree n) {j a : Fin n} {p : Fin n × Fin n}
    (hj : P.parents j = some p) (hja : j ≠ a) :
    P.chains j a =
      (P.chains p.1 a).image (List.cons 0) ∪ (P.chains p.2 a).image (List.cons 1) := by
  ext l
  cases l with
  | nil =>
    simp only [P.nil_mem_chains, hja, Finset.mem_union, Finset.mem_image, reduceCtorEq,
      and_false, exists_false, or_self]
  | cons s l =>
    rw [P.cons_mem_chains]
    simp only [Finset.mem_union, Finset.mem_image, List.cons.injEq]
    constructor
    · rintro ⟨q, hq, hl⟩
      by_cases hs : s = 0
      · subst hs
        rw [P.parent_zero hj] at hq
        cases hq
        exact Or.inl ⟨l, hl, rfl, rfl⟩
      · have hs1 : s = 1 := by omega
        subst hs1
        rw [P.parent_one hj] at hq
        cases hq
        exact Or.inr ⟨l, hl, rfl, rfl⟩
    · rintro (⟨l', hl', hs, rfl⟩ | ⟨l', hl', hs, rfl⟩)
      · exact ⟨p.1, hs ▸ P.parent_zero hj, hl'⟩
      · exact ⟨p.2, hs ▸ P.parent_one hj, hl'⟩

theorem pathSum_comm (P : Pedigree n) (i j : Fin n) : P.pathSum i j = P.pathSum j i := by
  unfold pathSum
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₂ _ => Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.inter_comm, Nat.add_comm c₁.length c₂.length]

theorem pathSum_self (P : Pedigree n) (i : Fin n) :
    P.pathSum i i = (1 + P.inbreeding i) / 2 := by
  unfold pathSum
  rw [Finset.sum_eq_single i]
  · have hc : P.chains i i = {[]} := by
      ext l
      rw [P.mem_chains, P.follow_eq_self_iff, Finset.mem_singleton]
    rw [hc, Finset.sum_singleton, Finset.sum_singleton]
    simp only [visited, Finset.inter_self, Finset.Subset.refl, ↓reduceIte, List.length_nil,
      Nat.add_zero, Nat.zero_add, pow_one]
    ring
  · intro a _ ha
    refine Finset.sum_eq_zero fun c₁ _ => Finset.sum_eq_zero fun c₂ _ => ?_
    split_ifs with hsub
    · have hmem := hsub
        (Finset.mem_inter.mpr ⟨P.self_mem_visited i c₁, P.self_mem_visited i c₂⟩)
      exact absurd (Finset.mem_singleton.mp hmem).symm ha
    · rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem pathSum_of_lt_founder (P : Pedigree n) {i j : Fin n} (hij : i < j)
    (hj : P.parents j = none) : P.pathSum i j = 0 := by
  unfold pathSum
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c₁ hc₁ => ?_
  have hai : a ≤ i := P.follow_le ((P.mem_chains i a c₁).mp hc₁)
  rw [P.chains_of_founder hj (ne_of_gt (lt_of_le_of_lt hai hij)), Finset.sum_empty]

theorem pathSum_of_lt (P : Pedigree n) {i j : Fin n} {p : Fin n × Fin n} (hij : i < j)
    (hj : P.parents j = some p) :
    P.pathSum i j = (P.pathSum i p.1 + P.pathSum i p.2) / 2 := by
  have inner : ∀ a, ∀ c₁ ∈ P.chains i a,
      (∑ c₂ ∈ P.chains j a,
        if P.visited i c₁ ∩ P.visited j c₂ ⊆ {a} then
          (1 / 2 : ℚ) ^ (c₁.length + c₂.length + 1) * (1 + P.inbreeding a)
        else 0) =
      ((∑ c₂ ∈ P.chains p.1 a,
        if P.visited i c₁ ∩ P.visited p.1 c₂ ⊆ {a} then
          (1 / 2 : ℚ) ^ (c₁.length + c₂.length + 1) * (1 + P.inbreeding a)
        else 0) +
      (∑ c₂ ∈ P.chains p.2 a,
        if P.visited i c₁ ∩ P.visited p.2 c₂ ⊆ {a} then
          (1 / 2 : ℚ) ^ (c₁.length + c₂.length + 1) * (1 + P.inbreeding a)
        else 0)) / 2 := by
    intro a c₁ hc₁
    have hai : a ≤ i := P.follow_le ((P.mem_chains i a c₁).mp hc₁)
    have hja : j ≠ a := ne_of_gt (lt_of_le_of_lt hai hij)
    have hjv : j ∉ P.visited i c₁ := fun h => absurd (P.visited_le h) (not_le.mpr hij)
    have hdisj : Disjoint ((P.chains p.1 a).image (List.cons (0 : Fin 2)))
        ((P.chains p.2 a).image (List.cons (1 : Fin 2))) := by
      rw [Finset.disjoint_left]
      intro l h0 h1
      obtain ⟨l0, _, rfl⟩ := Finset.mem_image.mp h0
      obtain ⟨l1, _, h⟩ := Finset.mem_image.mp h1
      exact absurd (List.cons.inj h).1 (by decide)
    rw [P.chains_of_parents hj hja, Finset.sum_union hdisj,
      Finset.sum_image fun x _ y _ h => List.cons_injective h,
      Finset.sum_image fun x _ y _ h => List.cons_injective h, add_div, Finset.sum_div,
      Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [P.visited_cons (P.parent_zero hj), Finset.inter_insert_of_notMem hjv,
        List.length_cons]
      split_ifs
      · ring
      · ring
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [P.visited_cons (P.parent_one hj), Finset.inter_insert_of_notMem hjv,
        List.length_cons]
      split_ifs
      · ring
      · ring
  unfold pathSum
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl (inner a)]
  simp only [Finset.sum_add_distrib, Finset.sum_div, add_div]

theorem kinship_eq_pathSum (P : Pedigree n) (i j : Fin n) :
    P.kinship i j = P.pathSum i j := by
  refine pair_induction (motive := fun i j => P.kinship i j = P.pathSum i j) ?_ i j
  intro i j ih
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases hj : P.parents j with
    | none => rw [kinship_of_lt_founder P hij hj, pathSum_of_lt_founder P hij hj]
    | some p =>
      have hlt := P.parents_lt j p hj
      rw [kinship_of_lt P hij hj, pathSum_of_lt P hij hj,
        ih i p.1 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.1) _),
        ih i p.2 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.2) _)]
  · rw [kinship_self, pathSum_self]
  · rw [kinship_comm, pathSum_comm]
    cases hi : P.parents i with
    | none => rw [kinship_of_lt_founder P hji hi, pathSum_of_lt_founder P hji hi]
    | some p =>
      have hlt := P.parents_lt i p hi
      have h1 := Fin.lt_def.mp hlt.1
      have h2 := Fin.lt_def.mp hlt.2
      rw [kinship_of_lt P hji hi, pathSum_of_lt P hji hi,
        ih j p.1 (by omega), ih j p.2 (by omega)]

theorem inbreeding_eq_pathSum (P : Pedigree n) {i : Fin n} {p : Fin n × Fin n}
    (hi : P.parents i = some p) : P.inbreeding i = P.pathSum p.1 p.2 := by
  rw [inbreeding_of_parents P hi, kinship_eq_pathSum]

end Rhone.Combinatorics.Pedigree
