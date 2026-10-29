/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Swap

/-! # Labelled states and the orbit map `Ξ` -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {SA SB : Type*}

structure IsMatching (M : Finset (SA × SB)) : Prop where
  fst : ∀ p ∈ M, ∀ p' ∈ M, p.1 = p'.1 → p = p'
  snd : ∀ p ∈ M, ∀ p' ∈ M, p.2 = p'.2 → p = p'

section ADom

variable [DecidableEq SA]

def domA (M : Finset (SA × SB)) : Finset SA := M.image Prod.fst

theorem mem_domA {M : Finset (SA × SB)} {u : SA} : u ∈ domA M ↔ ∃ v, (u, v) ∈ M := by
  simp only [domA, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp⟩
  · rintro ⟨v, hv⟩; exact ⟨(u, v), hv, rfl⟩

theorem mem_domA_of_mem {M : Finset (SA × SB)} {p : SA × SB} (hp : p ∈ M) : p.1 ∈ domA M :=
  Finset.mem_image_of_mem _ hp

theorem card_domA {M : Finset (SA × SB)} (h : IsMatching M) : (domA M).card = M.card :=
  Finset.card_image_of_injOn fun p hp p' hp' he => h.fst p hp p' hp' he

variable [Fintype SA]

def freeA (M : Finset (SA × SB)) : Finset SA := univ \ domA M

theorem mem_freeA {M : Finset (SA × SB)} {u : SA} : u ∈ freeA M ↔ ∀ v, (u, v) ∉ M := by
  simp only [freeA, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_domA, not_exists]

theorem notMem_freeA_of_mem {M : Finset (SA × SB)} {p : SA × SB} (hp : p ∈ M) :
    p.1 ∉ freeA M := by
  simp only [freeA, Finset.mem_sdiff, not_and, not_not]
  exact fun _ => mem_domA_of_mem hp

theorem card_freeA {M : Finset (SA × SB)} (h : IsMatching M) :
    (freeA M).card + M.card = Fintype.card SA := by
  rw [freeA, ← card_domA h, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
    Finset.card_univ]

end ADom

section BDom

variable [DecidableEq SB]

def domB (M : Finset (SA × SB)) : Finset SB := M.image Prod.snd

theorem mem_domB {M : Finset (SA × SB)} {v : SB} : v ∈ domB M ↔ ∃ u, (u, v) ∈ M := by
  simp only [domB, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.1, hp⟩
  · rintro ⟨u, hu⟩; exact ⟨(u, v), hu, rfl⟩

theorem mem_domB_of_mem {M : Finset (SA × SB)} {p : SA × SB} (hp : p ∈ M) : p.2 ∈ domB M :=
  Finset.mem_image_of_mem _ hp

theorem card_domB {M : Finset (SA × SB)} (h : IsMatching M) : (domB M).card = M.card :=
  Finset.card_image_of_injOn fun p hp p' hp' he => h.snd p hp p' hp' he

variable [Fintype SB]

def freeB (M : Finset (SA × SB)) : Finset SB := univ \ domB M

theorem mem_freeB {M : Finset (SA × SB)} {v : SB} : v ∈ freeB M ↔ ∀ u, (u, v) ∉ M := by
  simp only [freeB, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_domB, not_exists]

theorem notMem_freeB_of_mem {M : Finset (SA × SB)} {p : SA × SB} (hp : p ∈ M) :
    p.2 ∉ freeB M := by
  simp only [freeB, Finset.mem_sdiff, not_and, not_not]
  exact fun _ => mem_domB_of_mem hp

theorem card_freeB {M : Finset (SA × SB)} (h : IsMatching M) :
    (freeB M).card + M.card = Fintype.card SB := by
  rw [freeB, ← card_domB h, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
    Finset.card_univ]

end BDom

section Both

variable [DecidableEq SA] [DecidableEq SB]

theorem domA_erase {M : Finset (SA × SB)} (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    domA (M.erase p) = (domA M).erase p.1 := by
  ext u
  rw [mem_domA, Finset.mem_erase, mem_domA]
  constructor
  · rintro ⟨v, hv⟩
    rw [Finset.mem_erase] at hv
    exact ⟨fun hc => hv.1 (h.fst _ hv.2 _ hp hc), ⟨v, hv.2⟩⟩
  · rintro ⟨hne, v, hv⟩
    exact ⟨v, Finset.mem_erase.mpr ⟨fun hc => hne (congrArg Prod.fst hc), hv⟩⟩

theorem domB_erase {M : Finset (SA × SB)} (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    domB (M.erase p) = (domB M).erase p.2 := by
  ext v
  rw [mem_domB, Finset.mem_erase, mem_domB]
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_erase] at hu
    exact ⟨fun hc => hu.1 (h.snd _ hu.2 _ hp hc), ⟨u, hu.2⟩⟩
  · rintro ⟨hne, u, hu⟩
    exact ⟨u, Finset.mem_erase.mpr ⟨fun hc => hne (congrArg Prod.snd hc), hu⟩⟩

variable [Fintype SA] [Fintype SB]

omit [Fintype SB] in
theorem freeA_insert {M : Finset (SA × SB)} {k : SA} (l : SB) :
    freeA (insert (k, l) M) = (freeA M).erase k := by
  simp only [freeA, domA, Finset.image_insert]
  exact Finset.sdiff_insert _ _ _

omit [Fintype SB] in
theorem freeA_erase {M : Finset (SA × SB)} (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    freeA (M.erase p) = insert p.1 (freeA M) := by
  simp only [freeA, domA_erase h hp]
  exact Finset.sdiff_erase (Finset.mem_univ _)

omit [Fintype SA] in
theorem freeB_insert {M : Finset (SA × SB)} {l : SB} (k : SA) :
    freeB (insert (k, l) M) = (freeB M).erase l := by
  simp only [freeB, domB, Finset.image_insert]
  exact Finset.sdiff_insert _ _ _

omit [Fintype SA] in
theorem freeB_erase {M : Finset (SA × SB)} (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    freeB (M.erase p) = insert p.2 (freeB M) := by
  simp only [freeB, domB_erase h hp]
  exact Finset.sdiff_erase (Finset.mem_univ _)

end Both

section Counting

variable {ι : Type*} [DecidableEq ι]

theorem card_filter_erase_add {s : Finset ι} {u : ι} (hu : u ∈ s) (p : ι → Prop)
    [DecidablePred p] :
    ((s.erase u).filter p).card + (if p u then 1 else 0) = (s.filter p).card := by
  rw [Finset.filter_erase]
  by_cases h : p u
  · rw [ite_eq_left h, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hu, h⟩)]
    have : 1 ≤ (s.filter p).card := Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, h⟩⟩
    omega
  · rw [ite_eq_right h,
      Finset.erase_eq_of_notMem (fun hc => h (Finset.mem_filter.mp hc).2), add_zero]

theorem card_filter_insert {s : Finset ι} {u : ι} (hu : u ∉ s) (p : ι → Prop)
    [DecidablePred p] :
    ((insert u s).filter p).card = (s.filter p).card + (if p u then 1 else 0) := by
  rw [Finset.filter_insert]
  by_cases h : p u
  · rw [ite_eq_left h, ite_eq_left h,
      Finset.card_insert_of_notMem (fun hc => hu (Finset.mem_filter.mp hc).1)]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

end Counting

section Xi

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def xi (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB) : Config KA KB where
  a i := ((freeA M).filter fun u => α u = i).card
  b j := ((freeB M).filter fun v => β v = j).card
  c i j := (M.filter fun p => α p.1 = i ∧ β p.2 = j).card

variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)

@[simp] theorem xi_a (i : Fin KA) :
    (xi M α β).a i = ((freeA M).filter fun u => α u = i).card := rfl

@[simp] theorem xi_b (j : Fin KB) :
    (xi M α β).b j = ((freeB M).filter fun v => β v = j).card := rfl

@[simp] theorem xi_c (i : Fin KA) (j : Fin KB) :
    (xi M α β).c i j = (M.filter fun p => α p.1 = i ∧ β p.2 = j).card := rfl

theorem sumA_xi : (xi M α β).sumA = (freeA M).card :=
  (Finset.card_eq_sum_card_fiberwise fun u _ => Finset.mem_univ (α u)).symm

theorem sumB_xi : (xi M α β).sumB = (freeB M).card :=
  (Finset.card_eq_sum_card_fiberwise fun v _ => Finset.mem_univ (β v)).symm

theorem t_xi : (xi M α β).t = M.card := by
  have h : M.card = ∑ p : Fin KA × Fin KB, (M.filter fun r => (α r.1, β r.2) = p).card :=
    Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ _
  rw [Config.t, h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [xi_c]
  congr 1

theorem cRow_xi (i : Fin KA) : (xi M α β).cRow i = (M.filter fun p => α p.1 = i).card := by
  have h : (M.filter fun p => α p.1 = i).card
      = ∑ j : Fin KB, ((M.filter fun p => α p.1 = i).filter fun p => β p.2 = j).card :=
    Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ _
  rw [Config.cRow, h]
  exact Finset.sum_congr rfl fun j _ => by simp [Finset.filter_filter]

theorem cCol_xi (j : Fin KB) : (xi M α β).cCol j = (M.filter fun p => β p.2 = j).card := by
  have h : (M.filter fun p => β p.2 = j).card
      = ∑ i : Fin KA, ((M.filter fun p => β p.2 = j).filter fun p => α p.1 = i).card :=
    Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ _
  rw [Config.cCol, h]
  exact Finset.sum_congr rfl fun i _ => by simp [Finset.filter_filter, and_comm]

theorem nA_xi (h : IsMatching M) : (xi M α β).nA = Fintype.card SA := by
  rw [Config.nA, sumA_xi, t_xi]; exact card_freeA h

theorem nB_xi (h : IsMatching M) : (xi M α β).nB = Fintype.card SB := by
  rw [Config.nB, sumB_xi, t_xi]; exact card_freeB h

theorem n_xi (h : IsMatching M) :
    (xi M α β).n + M.card = Fintype.card SA + Fintype.card SB := by
  have hn := (xi M α β).n_add_t
  rw [nA_xi M α β h, nB_xi M α β h, t_xi] at hn
  exact hn

end Xi

end Rhone.Probability.Multilinear
