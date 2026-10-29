/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.State

/-! # The 15-symbol combo alphabet, the tag-union table, and the count vector -/

@[expose] public section

namespace Rhone.Coalescent.ArgLumping

open Finset TwoLocusGenealogy

inductive Tag where
  | N
  | R
  | BLU
  | M
  deriving DecidableEq, Repr

instance : Fintype Tag where
  elems := {Tag.N, Tag.R, Tag.BLU, Tag.M}
  complete := fun x => by cases x <;> simp

def mergeTag : Tag → Tag → Tag
  | .N, y => y
  | x, .N => x
  | .R, .R => .R
  | .BLU, .BLU => .BLU
  | _, _ => .M

@[simp] theorem mergeTag_N_left (y : Tag) : mergeTag .N y = y := by cases y <;> rfl

@[simp] theorem mergeTag_N_right (x : Tag) : mergeTag x .N = x := by cases x <;> rfl

def tagFromProp (p q : Prop) [Decidable p] [Decidable q] : Tag :=
  if p then (if q then Tag.N else Tag.R) else (if q then Tag.BLU else Tag.M)

theorem tagFromProp_congr {p q p' q' : Prop} [Decidable p] [Decidable q] [Decidable p']
    [Decidable q'] (hp : p ↔ p') (hq : q ↔ q') : tagFromProp p q = tagFromProp p' q' := by
  simp only [tagFromProp, hp, hq]

theorem mergeTag_tagFromProp (p q p' q' : Prop) [Decidable p] [Decidable q] [Decidable p']
    [Decidable q'] :
    mergeTag (tagFromProp p q) (tagFromProp p' q') = tagFromProp (p ∧ p') (q ∧ q') := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hp' : p' <;> by_cases hq' : q' <;>
    simp [tagFromProp, mergeTag, hp, hq, hp', hq']

variable {n : ℕ}

def tagOf (H S : Finset (Fin n)) : Tag :=
  if S = ∅ then .N else if S ⊆ H then .R else if Disjoint S H then .BLU else .M

theorem not_disjoint_of_nonempty_subset {H S : Finset (Fin n)} (hne : S.Nonempty)
    (hsub : S ⊆ H) : ¬ Disjoint S H := by
  intro hd
  obtain ⟨a, ha⟩ := hne
  exact (Finset.disjoint_left.1 hd) ha (hsub ha)

theorem subset_and_disjoint_iff {H S : Finset (Fin n)} : (S ⊆ H ∧ Disjoint S H) ↔ S = ∅ := by
  constructor
  · rintro ⟨hsub, hd⟩
    by_contra hne
    exact not_disjoint_of_nonempty_subset (Finset.nonempty_iff_ne_empty.2 hne) hsub hd
  · rintro rfl
    exact ⟨Finset.empty_subset _, Finset.disjoint_empty_left _⟩

theorem tagOf_eq_tagFromProp (H S : Finset (Fin n)) :
    tagOf H S = tagFromProp (S ⊆ H) (Disjoint S H) := by
  unfold tagOf tagFromProp
  by_cases h1 : S ⊆ H
  · by_cases h2 : Disjoint S H
    · rw [ite_eq_left (subset_and_disjoint_iff.1 ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2]
    · rw [ite_eq_right (fun h => h2 (by rw [h]; exact Finset.disjoint_empty_left _)),
        ite_eq_left h1,
        ite_eq_left h1, ite_eq_right h2]
  · rw [ite_eq_right (fun h => h1 (by rw [h]; exact Finset.empty_subset _)), ite_eq_right h1,
      ite_eq_right h1]

@[simp] theorem tagOf_empty (H : Finset (Fin n)) : tagOf H ∅ = Tag.N := by simp [tagOf]

theorem tagOf_eq_N_iff {H S : Finset (Fin n)} : tagOf H S = Tag.N ↔ S = ∅ := by
  unfold tagOf
  split_ifs with h1 h2 h3 <;> simp [h1]

theorem tagOf_eq_R_iff {H S : Finset (Fin n)} : tagOf H S = Tag.R ↔ (S.Nonempty ∧ S ⊆ H) := by
  unfold tagOf
  split_ifs with h1 h2 h3
  · simp [h1]
  · simp [Finset.nonempty_iff_ne_empty.2 h1, h2]
  · simp [h2]
  · simp [h2]

theorem tagOf_eq_BLU_iff {H S : Finset (Fin n)} :
    tagOf H S = Tag.BLU ↔ (S.Nonempty ∧ Disjoint S H) := by
  unfold tagOf
  split_ifs with h1 h2 h3
  · simp [h1]
  · simp [not_disjoint_of_nonempty_subset (Finset.nonempty_iff_ne_empty.2 h1) h2]
  · simp [Finset.nonempty_iff_ne_empty.2 h1, h3]
  · simp [h3]

theorem tagOf_eq_M_iff {H S : Finset (Fin n)} :
    tagOf H S = Tag.M ↔ (¬ S ⊆ H ∧ ¬ Disjoint S H) := by
  unfold tagOf
  split_ifs with h1 h2 h3
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h2, h3]

theorem tagOf_ne_N_iff {H S : Finset (Fin n)} : tagOf H S ≠ Tag.N ↔ S ≠ ∅ := by
  rw [Ne, Ne, tagOf_eq_N_iff]

theorem tagOf_union (H A B : Finset (Fin n)) :
    tagOf H (A ∪ B) = mergeTag (tagOf H A) (tagOf H B) := by
  rw [tagOf_eq_tagFromProp, tagOf_eq_tagFromProp, tagOf_eq_tagFromProp, mergeTag_tagFromProp]
  exact tagFromProp_congr Finset.union_subset_iff Finset.disjoint_union_left

def swapTag : Tag → Tag
  | .N => .N
  | .R => .BLU
  | .BLU => .R
  | .M => .M

@[simp] theorem swapTag_eq_R_iff (x : Tag) : swapTag x = Tag.R ↔ x = Tag.BLU := by
  cases x <;> simp [swapTag]

@[simp] theorem swapTag_eq_BLU_iff (x : Tag) : swapTag x = Tag.BLU ↔ x = Tag.R := by
  cases x <;> simp [swapTag]

@[simp] theorem swapTag_eq_M_iff (x : Tag) : swapTag x = Tag.M ↔ x = Tag.M := by
  cases x <;> simp [swapTag]

theorem swapTag_tagFromProp (p q : Prop) [Decidable p] [Decidable q] :
    swapTag (tagFromProp p q) = tagFromProp q p := by
  by_cases hp : p <;> by_cases hq : q <;> simp [tagFromProp, swapTag, hp, hq]

theorem tagOf_compl (H S : Finset (Fin n)) : tagOf Hᶜ S = swapTag (tagOf H S) := by
  rw [tagOf_eq_tagFromProp, tagOf_eq_tagFromProp, swapTag_tagFromProp]
  refine tagFromProp_congr ?_ ?_
  · rw [Finset.disjoint_left]
    exact ⟨fun h a ha => by simpa using h ha, fun h a ha => by simpa using h ha⟩
  · rw [Finset.disjoint_left]
    refine ⟨fun h a ha => ?_, fun h a ha hc => (Finset.mem_compl.1 hc) (h ha)⟩
    by_contra hc
    exact h ha (Finset.mem_compl.2 hc)

theorem tagOf_univ {H : Finset (Fin n)} (hH : H.Nonempty) (hHc : Hᶜ.Nonempty) :
    tagOf H Finset.univ = Tag.M := by
  refine tagOf_eq_M_iff.2 ⟨fun hsub => ?_, fun hd => ?_⟩
  · obtain ⟨a, ha⟩ := hHc
    exact (Finset.mem_compl.1 ha) (hsub (Finset.mem_univ a))
  · obtain ⟨a, ha⟩ := hH
    exact (Finset.disjoint_right.1 hd) ha (Finset.mem_univ a)

abbrev Combo : Type := {c : Tag × Tag // c ≠ (Tag.N, Tag.N)}

theorem card_Tag : Fintype.card Tag = 4 := rfl

theorem card_Combo : Fintype.card Combo = 15 := by
  have h : Fintype.card Combo
      = Fintype.card (Tag × Tag) - Fintype.card {c : Tag × Tag // c = (Tag.N, Tag.N)} :=
    Fintype.card_subtype_compl _
  rw [h, Fintype.card_subtype_eq, Fintype.card_prod, card_Tag]

def comboOf (HA HB : Finset (Fin n)) (l : Lin n) : Tag × Tag := (tagOf HA l.1, tagOf HB l.2)

def proj (HA HB : Finset (Fin n)) (L : Finset (Lin n)) : Tag × Tag → ℕ :=
  fun c => (L.filter fun l => comboOf HA HB l = c).card

theorem comboOf_ne_NN {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hw : WF L) {l : Lin n}
    (hl : l ∈ L) : comboOf HA HB l ≠ (Tag.N, Tag.N) := by
  intro h
  have h1 : l.1 = ∅ := tagOf_eq_N_iff.1 (congrArg Prod.fst h)
  have h2 : l.2 = ∅ := tagOf_eq_N_iff.1 (congrArg Prod.snd h)
  rcases hw.carries l hl with hc | hc
  · exact (Finset.nonempty_iff_ne_empty.1 hc) h1
  · exact (Finset.nonempty_iff_ne_empty.1 hc) h2

theorem proj_NN {HA HB : Finset (Fin n)} {L : Finset (Lin n)} (hw : WF L) :
    proj HA HB L (Tag.N, Tag.N) = 0 := by
  rw [proj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun {l} hl => comboOf_ne_NN hw hl

def totA (C : Tag × Tag → ℕ) : ℕ := ∑ c ∈ Finset.univ.filter fun c : Tag × Tag => c.1 ≠ .N, C c

def totB (C : Tag × Tag → ℕ) : ℕ := ∑ c ∈ Finset.univ.filter fun c : Tag × Tag => c.2 ≠ .N, C c

def countA (t : Tag) (C : Tag × Tag → ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : Tag × Tag => c.1 = t, C c

def countB (t : Tag) (C : Tag × Tag → ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : Tag × Tag => c.2 = t, C c

theorem sum_proj_filter (HA HB : Finset (Fin n)) (L : Finset (Lin n)) (P : Tag × Tag → Prop)
    [DecidablePred P] :
    ∑ c ∈ Finset.univ.filter P, proj HA HB L c
      = (L.filter fun l => P (comboOf HA HB l)).card := by
  simp only [proj]
  rw [Finset.sum_card_fiberwise_eq_card_filter L (Finset.univ.filter P) (comboOf HA HB)]
  refine congrArg Finset.card (Finset.filter_congr fun l _ => ?_)
  simp

theorem totA_eq (HA HB : Finset (Fin n)) (L : Finset (Lin n)) :
    totA (proj HA HB L) = (L.filter fun l => l.1 ≠ ∅).card := by
  rw [totA, sum_proj_filter]
  simp only [comboOf, ne_eq, tagOf_eq_N_iff]

theorem totB_eq (HA HB : Finset (Fin n)) (L : Finset (Lin n)) :
    totB (proj HA HB L) = (L.filter fun l => l.2 ≠ ∅).card := by
  rw [totB, sum_proj_filter]
  simp only [comboOf, ne_eq, tagOf_eq_N_iff]

theorem countA_eq (HA HB : Finset (Fin n)) (L : Finset (Lin n)) (t : Tag) :
    countA t (proj HA HB L) = (L.filter fun l => tagOf HA l.1 = t).card := by
  rw [countA, sum_proj_filter]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)

theorem countB_eq (HA HB : Finset (Fin n)) (L : Finset (Lin n)) (t : Tag) :
    countB t (proj HA HB L) = (L.filter fun l => tagOf HB l.2 = t).card := by
  rw [countB, sum_proj_filter]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)

def indC (k c : Tag × Tag) : ℕ := if k = c then 1 else 0

def insC (k c : Tag × Tag) : ℕ := if k = (Tag.N, Tag.N) then 0 else indC k c

def coalCombo (C : Tag × Tag → ℕ) (i j : Tag × Tag) : Tag × Tag :=
  (if i.1 ≠ .N ∧ j.1 ≠ .N ∧ totA C = 2 then Tag.N else mergeTag i.1 j.1,
   if i.2 ≠ .N ∧ j.2 ≠ .N ∧ totB C = 2 then Tag.N else mergeTag i.2 j.2)

def coalC (C : Tag × Tag → ℕ) (i j : Tag × Tag) : Tag × Tag → ℕ :=
  fun c => C c + insC (coalCombo C i j) c - indC i c - indC j c

def recC (C : Tag × Tag → ℕ) (k : Tag × Tag) : Tag × Tag → ℕ :=
  fun c => C c + indC (k.1, Tag.N) c + indC (Tag.N, k.2) c - indC k c

end Rhone.Coalescent.ArgLumping
