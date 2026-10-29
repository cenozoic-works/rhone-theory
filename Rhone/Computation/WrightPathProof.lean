/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.WrightPath
public import Rhone.Computation.KinshipProof
public import Rhone.Dynamics.PedigreePathFormula

/-! # Executable Wright path sum equals the specification -/

@[expose] public section
namespace Rhone.Computation.WrightPath
open Kinship Rhone.Combinatorics

theorem sumBy_eq_sum {α : Type} (f : α → Rat) (l : List α) : sumBy f l = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sumBy, ih]

theorem parentAt_eq {n : Nat} (P : Pedigree n) (i : Fin n) (s : Fin 2) :
    parentAt (pedList P) i.val s = (P.parent i s).map Fin.val := by
  unfold parentAt Pedigree.parent
  rw [parents_pedList]
  rcases P.parents i with _ | p
  · simp
  · simp only [Option.map_some]
    split_ifs <;> rfl

theorem mem_branch {n : Nat} (P : Pedigree n) (i : Fin n) (s : Fin 2)
    (rest : Nat → List (List (Fin 2))) (R : Fin n → Finset (List (Fin 2)))
    (hR : ∀ q : Fin n, q < i → ∀ c, c ∈ rest q.val ↔ c ∈ R q) (t : Fin 2) (l : List (Fin 2)) :
    t :: l ∈ branch (pedList P) rest i.val s ↔ t = s ∧ ∃ q, P.parent i s = some q ∧ l ∈ R q := by
  unfold branch
  rw [parentAt_eq]
  cases hq : P.parent i s with
  | none => simp
  | some q =>
    have hlt := P.parent_lt hq
    simp only [Option.map_some, List.mem_map, List.cons.injEq, Option.some.injEq]
    constructor
    · rintro ⟨c, hc, rfl, rfl⟩
      exact ⟨rfl, q, rfl, (hR q hlt c).1 hc⟩
    · rintro ⟨rfl, q', hq', hl⟩
      cases hq'
      exact ⟨l, (hR q hlt l).2 hl, rfl, rfl⟩

theorem mem_chainsF {n : Nat} (P : Pedigree n) (a : Fin n) :
    ∀ (i : Fin n) (f : Nat), i.val < f → ∀ c : List (Fin 2),
      c ∈ chainsF (pedList P) f i.val a.val ↔ c ∈ P.chains i a := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    intro f hf c
    cases f with
    | zero => omega
    | succ f =>
      have hb : ∀ s : Fin 2, ∀ t l, t :: l ∈ branch (pedList P)
          (fun p => chainsF (pedList P) f p a.val) i.val s ↔
          t = s ∧ ∃ q, P.parent i s = some q ∧ l ∈ P.chains q a := by
        intro s t l
        refine mem_branch P i s _ (fun q => P.chains q a) ?_ t l
        intro q hq c
        exact ih q hq f (by have := Fin.lt_def.mp hq; omega) c
      cases c with
      | nil =>
        rw [Pedigree.nil_mem_chains]
        have h0 : ∀ s : Fin 2, [] ∉ branch (pedList P)
            (fun p => chainsF (pedList P) f p a.val) i.val s := by
          intro s h
          unfold branch at h
          cases hh : parentAt (pedList P) i.val s <;> simp [hh] at h
        simp [chainsF, h0, Fin.ext_iff]
      | cons t l =>
        rw [Pedigree.cons_mem_chains]
        have hs : ∀ s : Fin 2, t :: l ∈ branch (pedList P)
            (fun p => chainsF (pedList P) f p a.val) i.val s ↔
            t = s ∧ ∃ q, P.parent i s = some q ∧ l ∈ P.chains q a := fun s => hb s t l
        simp only [chainsF, List.mem_append, hs]
        fin_cases t <;> simp

theorem branch_head {ped : Ped} {rest : Nat → List (List (Fin 2))} {i : Nat} {s : Fin 2}
    {c : List (Fin 2)} (h : c ∈ branch ped rest i s) : ∃ l, c = s :: l := by
  unfold branch at h
  cases hh : parentAt ped i s with
  | none => simp [hh] at h
  | some p =>
    simp only [hh, List.mem_map] at h
    obtain ⟨l, _, rfl⟩ := h
    exact ⟨l, rfl⟩

theorem branch_nodup {ped : Ped} {rest : Nat → List (List (Fin 2))} {i : Nat} {s : Fin 2}
    (h : ∀ p, (rest p).Nodup) : (branch ped rest i s).Nodup := by
  unfold branch
  cases parentAt ped i s with
  | none => simp
  | some p => exact (h p).map (fun x y hxy => by simpa using hxy)

theorem chainsF_nodup (ped : Ped) (f i a : Nat) : (chainsF ped f i a).Nodup := by
  induction f generalizing i with
  | zero => simp [chainsF]
  | succ f ih =>
    simp only [chainsF]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp
    · rw [List.nodup_append]
      refine ⟨branch_nodup (fun p => ih p), branch_nodup (fun p => ih p), ?_⟩
      intro x hx y hy hxy
      obtain ⟨l, rfl⟩ := branch_head hx
      obtain ⟨l', rfl⟩ := branch_head hy
      simp at hxy
    · intro x hx y hy hxy
      subst hxy
      have : ∃ l, x = (0 : Fin 2) :: l ∨ ∃ l, x = (1 : Fin 2) :: l := by
        rcases List.mem_append.1 hy with h | h
        · obtain ⟨l, hl⟩ := branch_head h; exact ⟨l, Or.inl hl⟩
        · obtain ⟨l, hl⟩ := branch_head h; exact ⟨l, Or.inr ⟨l, hl⟩⟩
      split_ifs at hx <;> simp at hx
      obtain ⟨l, h | ⟨l', h⟩⟩ := this <;> simp [hx] at h

theorem mem_visited {n : Nat} (P : Pedigree n) (c : List (Fin 2)) :
    ∀ (i : Fin n) (y : Nat), y ∈ visited (pedList P) i.val c ↔
      ∃ x : Fin n, x.val = y ∧ x ∈ P.visited i c := by
  induction c with
  | nil =>
    intro i y
    simp [visited, Pedigree.visited, eq_comm]
  | cons s l ih =>
    intro i y
    cases hq : P.parent i s with
    | none =>
      simp [visited, Pedigree.visited, parentAt_eq, hq, eq_comm]
    | some q =>
      simp only [visited, Pedigree.visited, parentAt_eq, hq, Option.map_some, List.mem_cons,
        Finset.mem_insert]
      rw [ih q y]
      constructor
      · rintro (rfl | ⟨x, rfl, hx⟩)
        · exact ⟨i, rfl, Or.inl rfl⟩
        · exact ⟨x, rfl, Or.inr hx⟩
      · rintro ⟨x, rfl, (rfl | hx)⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨x, rfl, hx⟩

theorem visited_test_iff {n : Nat} (P : Pedigree n) (i j a : Fin n) (c₁ c₂ : List (Fin 2)) :
    ((visited (pedList P) i.val c₁).all
        (fun x => !(visited (pedList P) j.val c₂).contains x || x == a.val) = true) ↔
      P.visited i c₁ ∩ P.visited j c₂ ⊆ {a} := by
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hx
    have m1 := (mem_visited P c₁ i x.val).2 ⟨x, rfl, h1⟩
    have m2 := (mem_visited P c₂ j x.val).2 ⟨x, rfl, h2⟩
    have := h x.val m1
    simp [m2] at this
    simpa [Fin.ext_iff] using this
  · intro h x hx
    by_cases hm : x ∈ visited (pedList P) j.val c₂
    · obtain ⟨x1, rfl, hx1⟩ := (mem_visited P c₁ i x).1 hx
      obtain ⟨x2, hx2, hx2'⟩ := (mem_visited P c₂ j x1.val).1 hm
      have : x2 = x1 := Fin.ext hx2
      subst this
      have := h (Finset.mem_inter.2 ⟨hx1, hx2'⟩)
      simp at this
      simp [this]
    · simp [hm]

theorem sum_range_list (F : Nat → Rat) (n : Nat) :
    ((List.range n).map F).sum = ∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem pathSum_eq {n : Nat} (P : Pedigree n) (i j : Fin n) :
    pathSum (pedList P) n i.val j.val = P.pathSum i j := by
  have hch : ∀ (u a : Fin n) (g : List (Fin 2) → Rat),
      sumBy g (chains (pedList P) u.val a.val) = ∑ c ∈ P.chains u a, g c := by
    intro u a g
    unfold chains
    rw [sumBy_eq_sum, ← List.sum_toFinset g (chainsF_nodup _ _ _ _)]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext c
    rw [List.mem_toFinset]
    exact mem_chainsF P a u _ (Nat.lt_succ_self _) c
  unfold pathSum Pedigree.pathSum
  rw [sumBy_eq_sum, sum_range_list, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hch i a]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [hch j a]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  by_cases h : P.visited i c₁ ∩ P.visited j c₂ ⊆ {a}
  · have h' := (visited_test_iff P i j a c₁ c₂).2 h
    simp only [h, h', ↓reduceIte, inbreeding_eq]
  · have h' : ¬ ((visited (pedList P) i.val c₁).all
        (fun x => !(visited (pedList P) j.val c₂).contains x || x == a.val) = true) :=
      fun hh => h ((visited_test_iff P i j a c₁ c₂).1 hh)
    rw [ite_eq_right_iff.2 (fun hh => absurd hh h'), ite_eq_right_iff.2 (fun hh => absurd hh h)]

theorem pathSum_eq_kinship {n : Nat} (P : Pedigree n) (i j : Fin n) :
    pathSum (pedList P) n i.val j.val = kinship (pedList P) i.val j.val := by
  rw [pathSum_eq, kinship_eq, Pedigree.kinship_eq_pathSum]

end Rhone.Computation.WrightPath
