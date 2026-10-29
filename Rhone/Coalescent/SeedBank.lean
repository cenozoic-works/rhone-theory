/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.KingmanPartition

/-!
# The seed-bank coalescent of a finite sample

Source: blath_etal2016, Definition 3.1, eq. (3.1). -/

@[expose] public section

namespace Rhone.Coalescent.SeedBank

open Finset MarkovChain

section Events

variable {S T ι : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] [Fintype ι]

noncomputable def eventQ (r : ι → S → ℝ) (e : ι → S → S) : Matrix S S ℝ := fun x y =>
  (∑ i, if y = e i x then r i x else 0) - if x = y then ∑ i, r i x else 0

theorem sum_eventQ_mul (r : ι → S → ℝ) (e : ι → S → S) (x : S) (g : S → ℝ) :
    ∑ y, eventQ r e x y * g y = ∑ i, r i x * (g (e i x) - g x) := by
  simp only [eventQ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_mul]
  · simp [ite_mul, Finset.sum_mul]

noncomputable def eventChain (r : ι → S → ℝ) (e : ι → S → S) (hr : ∀ i x, 0 ≤ r i x) :
    RateChain S where
  Q := eventQ r e
  off_diag_nonneg x y hxy := by
    simp only [eventQ, hxy, ↓reduceIte, sub_zero]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · exact hr i x
    · exact le_rfl
  row_sum x := by
    have h := sum_eventQ_mul r e x fun _ => 1
    simpa using h

omit [Fintype S] in
theorem eventQ_eq_zero {r : ι → S → ℝ} {e : ι → S → S} {x y : S} (hxy : x ≠ y)
    (h : ∀ i, y = e i x → r i x = 0) : eventQ r e x y = 0 := by
  simp only [eventQ, hxy, ↓reduceIte, sub_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hy
  · exact h i hy
  · rfl

omit [DecidableEq S] in
theorem lumps_of_forall_sum {R : RateChain S} {R' : RateChain T} {f : S → T}
    (h : ∀ (g : T → ℝ) (x : S), ∑ y, R.Q x y * g (f y) = ∑ t, R'.Q (f x) t * g t) :
    R.Lumps f R' := by
  intro x t
  have ht := h (fun t' => if t' = t then 1 else 0) x
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte] at ht
  rw [← ht, Finset.sum_filter]

end Events

@[ext]
structure Marked (α : Type*) [Fintype α] [DecidableEq α] where
  partition : Finpartition (univ : Finset α)
  dormant : α → Bool
  dormant_eq' : ∀ B ∈ partition.parts, ∀ a ∈ B, ∀ b ∈ B, dormant a = dormant b

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable instance : DecidableEq (Marked α) := Classical.decEq _

noncomputable instance : Fintype (Marked α) :=
  Fintype.ofInjective (fun x : Marked α => (x.partition, x.dormant)) fun _ _ h =>
    Marked.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : MeasurableSpace (Marked α) := ⊤

instance : DiscreteMeasurableSpace (Marked α) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable {x : Marked α} {B C : Finset α} {s : Finset (Finset α)}

theorem Marked.dormant_eq (x : Marked α) (hB : B ∈ x.partition.parts) {a b : α} (ha : a ∈ B)
    (hb : b ∈ B) : x.dormant a = x.dormant b :=
  x.dormant_eq' B hB a ha b hb

def activeParts (x : Marked α) : Finset (Finset α) :=
  x.partition.parts.filter fun B => ∀ a ∈ B, x.dormant a = false

def dormantParts (x : Marked α) : Finset (Finset α) :=
  x.partition.parts.filter fun B => ∀ a ∈ B, x.dormant a = true

theorem mem_activeParts :
    B ∈ activeParts x ↔ B ∈ x.partition.parts ∧ ∀ a ∈ B, x.dormant a = false :=
  mem_filter

theorem mem_dormantParts :
    B ∈ dormantParts x ↔ B ∈ x.partition.parts ∧ ∀ a ∈ B, x.dormant a = true :=
  mem_filter

theorem activeParts_subset (x : Marked α) : activeParts x ⊆ x.partition.parts :=
  filter_subset _ _

theorem dormantParts_subset (x : Marked α) : dormantParts x ⊆ x.partition.parts :=
  filter_subset _ _

theorem disjoint_activeParts_dormantParts (x : Marked α) :
    Disjoint (activeParts x) (dormantParts x) := by
  rw [Finset.disjoint_left]
  intro B hA hD
  obtain ⟨hB, h1⟩ := mem_activeParts.1 hA
  obtain ⟨-, h2⟩ := mem_dormantParts.1 hD
  obtain ⟨a, ha⟩ := x.partition.nonempty_of_mem_parts hB
  exact Bool.false_ne_true ((h1 a ha).symm.trans (h2 a ha))

theorem activeParts_union_dormantParts (x : Marked α) :
    activeParts x ∪ dormantParts x = x.partition.parts := by
  ext B
  rw [mem_union, mem_activeParts, mem_dormantParts]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hB
    obtain ⟨a, ha⟩ := x.partition.nonempty_of_mem_parts hB
    cases hd : x.dormant a
    · exact Or.inl ⟨hB, fun b hb => (x.dormant_eq hB hb ha).trans hd⟩
    · exact Or.inr ⟨hB, fun b hb => (x.dormant_eq hB hb ha).trans hd⟩

theorem card_activeParts_add_card_dormantParts (x : Marked α) :
    (activeParts x).card + (dormantParts x).card = x.partition.parts.card := by
  rw [← card_union_of_disjoint (disjoint_activeParts_dormantParts x),
    activeParts_union_dormantParts]

def flipBlock (x : Marked α) (B : Finset α) : Marked α :=
  if h : B ∈ x.partition.parts then
    { partition := x.partition
      dormant := fun a => if a ∈ B then !x.dormant a else x.dormant a
      dormant_eq' := by
        intro C hC a ha b hb
        by_cases hCB : C = B
        · subst hCB
          simp only [ha, hb, ↓reduceIte]
          rw [x.dormant_eq hC ha hb]
        · have hd : Disjoint C B := x.partition.disjoint hC h hCB
          have ha' : a ∉ B := Finset.disjoint_left.1 hd ha
          have hb' : b ∉ B := Finset.disjoint_left.1 hd hb
          simp only [ha', hb', ↓reduceIte]
          exact x.dormant_eq hC ha hb }
  else x

theorem flipBlock_partition (x : Marked α) (B : Finset α) :
    (flipBlock x B).partition = x.partition := by
  unfold flipBlock
  split_ifs <;> rfl

theorem flipBlock_dormant (h : B ∈ x.partition.parts) (a : α) :
    (flipBlock x B).dormant a = if a ∈ B then !x.dormant a else x.dormant a := by
  rw [flipBlock, dite_eq_left h]

theorem mem_activeParts_flipBlock (hB : B ∈ x.partition.parts) :
    C ∈ activeParts (flipBlock x B) ↔
      if C = B then C ∈ dormantParts x else C ∈ activeParts x := by
  rw [mem_activeParts, flipBlock_partition]
  split_ifs with hCB
  · subst hCB
    rw [mem_dormantParts]
    refine and_congr_right fun _ => forall₂_congr fun a ha => ?_
    rw [flipBlock_dormant hB, ite_eq_left ha]
    cases x.dormant a <;> simp
  · rw [mem_activeParts]
    refine and_congr_right fun hC => forall₂_congr fun a ha => ?_
    have ha' : a ∉ B := Finset.disjoint_left.1 (x.partition.disjoint hC hB hCB) ha
    rw [flipBlock_dormant hB, ite_eq_right ha']

theorem mem_dormantParts_flipBlock (hB : B ∈ x.partition.parts) :
    C ∈ dormantParts (flipBlock x B) ↔
      if C = B then C ∈ activeParts x else C ∈ dormantParts x := by
  rw [mem_dormantParts, flipBlock_partition]
  split_ifs with hCB
  · subst hCB
    rw [mem_activeParts]
    refine and_congr_right fun _ => forall₂_congr fun a ha => ?_
    rw [flipBlock_dormant hB, ite_eq_left ha]
    cases x.dormant a <;> simp
  · rw [mem_dormantParts]
    refine and_congr_right fun hC => forall₂_congr fun a ha => ?_
    have ha' : a ∉ B := Finset.disjoint_left.1 (x.partition.disjoint hC hB hCB) ha
    rw [flipBlock_dormant hB, ite_eq_right ha']

theorem activeParts_flipBlock_of_active (hB : B ∈ activeParts x) :
    activeParts (flipBlock x B) = (activeParts x).erase B := by
  have hnd : B ∉ dormantParts x :=
    Finset.disjoint_left.1 (disjoint_activeParts_dormantParts x) hB
  ext C
  rw [mem_activeParts_flipBlock (activeParts_subset x hB), mem_erase]
  split_ifs with hCB
  · subst hCB
    simp [hnd]
  · simp [hCB]

theorem dormantParts_flipBlock_of_active (hB : B ∈ activeParts x) :
    dormantParts (flipBlock x B) = insert B (dormantParts x) := by
  ext C
  rw [mem_dormantParts_flipBlock (activeParts_subset x hB), mem_insert]
  split_ifs with hCB
  · subst hCB
    simp [hB]
  · simp [hCB]

theorem activeParts_flipBlock_of_dormant (hB : B ∈ dormantParts x) :
    activeParts (flipBlock x B) = insert B (activeParts x) := by
  ext C
  rw [mem_activeParts_flipBlock (dormantParts_subset x hB), mem_insert]
  split_ifs with hCB
  · subst hCB
    simp [hB]
  · simp [hCB]

theorem dormantParts_flipBlock_of_dormant (hB : B ∈ dormantParts x) :
    dormantParts (flipBlock x B) = (dormantParts x).erase B := by
  have hna : B ∉ activeParts x :=
    Finset.disjoint_right.1 (disjoint_activeParts_dormantParts x) hB
  ext C
  rw [mem_dormantParts_flipBlock (dormantParts_subset x hB), mem_erase]
  split_ifs with hCB
  · subst hCB
    simp [hna]
  · simp [hCB]

def mergeActive (x : Marked α) (s : Finset (Finset α)) : Marked α :=
  if h : s ⊆ activeParts x then
    { partition := mergeBlocks x.partition s
      dormant := x.dormant
      dormant_eq' := by
        intro C hC a ha b hb
        have hs : s ⊆ x.partition.parts := h.trans (activeParts_subset x)
        by_cases hne : s.Nonempty
        · rw [parts_mergeBlocks hs hne, mem_insert] at hC
          rcases hC with rfl | hC
          · obtain ⟨u, hu, hau⟩ := Finset.mem_sup.1 ha
            obtain ⟨v, hv, hbv⟩ := Finset.mem_sup.1 hb
            rw [(mem_activeParts.1 (h hu)).2 a hau, (mem_activeParts.1 (h hv)).2 b hbv]
          · exact x.dormant_eq (mem_sdiff.1 hC).1 ha hb
        · rw [mergeBlocks, dite_eq_right fun h' => hne h'.2] at hC
          exact x.dormant_eq hC ha hb }
  else x

theorem mergeActive_partition (h : s ⊆ activeParts x) :
    (mergeActive x s).partition = mergeBlocks x.partition s := by
  rw [mergeActive, dite_eq_left h]

theorem mergeActive_dormant (x : Marked α) (s : Finset (Finset α)) :
    (mergeActive x s).dormant = x.dormant := by
  unfold mergeActive
  split_ifs <;> rfl

theorem activeParts_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) :
    activeParts (mergeActive x s) = insert (s.sup id) (activeParts x \ s) := by
  rw [mem_powersetCard] at hs
  have hsp := hs.1.trans (activeParts_subset x)
  have hne : s.Nonempty := card_pos.1 (by omega)
  ext C
  rw [mem_activeParts, mergeActive_partition hs.1, mergeActive_dormant,
    parts_mergeBlocks hsp hne, mem_insert, mem_insert, mem_sdiff, mem_sdiff, mem_activeParts]
  constructor
  · rintro ⟨rfl | ⟨hC, hCs⟩, hd⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨hC, hd⟩, hCs⟩
  · rintro (rfl | ⟨⟨hC, hd⟩, hCs⟩)
    · refine ⟨Or.inl rfl, fun a ha => ?_⟩
      obtain ⟨u, hu, hau⟩ := Finset.mem_sup.1 ha
      exact (mem_activeParts.1 (hs.1 hu)).2 a hau
    · exact ⟨Or.inr ⟨hC, hCs⟩, hd⟩

theorem dormantParts_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) :
    dormantParts (mergeActive x s) = dormantParts x := by
  rw [mem_powersetCard] at hs
  have hsp := hs.1.trans (activeParts_subset x)
  have hne : s.Nonempty := card_pos.1 (by omega)
  ext C
  rw [mem_dormantParts, mergeActive_partition hs.1, mergeActive_dormant,
    parts_mergeBlocks hsp hne, mem_insert, mem_sdiff, mem_dormantParts]
  constructor
  · rintro ⟨rfl | ⟨hC, -⟩, hd⟩
    · exfalso
      obtain ⟨u, hu⟩ := hne
      obtain ⟨a, ha⟩ := x.partition.nonempty_of_mem_parts (hsp hu)
      have h1 := (mem_activeParts.1 (hs.1 hu)).2 a ha
      have h2 := hd a (Finset.mem_sup.2 ⟨u, hu, ha⟩)
      exact Bool.false_ne_true (h1.symm.trans h2)
    · exact ⟨hC, hd⟩
  · rintro ⟨hC, hd⟩
    refine ⟨Or.inr ⟨hC, fun hCs => ?_⟩, hd⟩
    exact Finset.disjoint_left.1 (disjoint_activeParts_dormantParts x) (hs.1 hCs)
      (mem_dormantParts.2 ⟨hC, hd⟩)

theorem card_activeParts_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) :
    (activeParts (mergeActive x s)).card + 1 = (activeParts x).card := by
  rw [activeParts_mergeActive hs]
  rw [mem_powersetCard] at hs
  have hsp := hs.1.trans (activeParts_subset x)
  have hx : s.sup id ∉ activeParts x \ s := fun h =>
    sup_notMem_parts hsp hs.2 (activeParts_subset x (mem_sdiff.1 h).1)
  have hle : s.card ≤ (activeParts x).card := card_le_card hs.1
  rw [card_insert_of_notMem hx, card_sdiff_of_subset hs.1]
  omega

noncomputable def eventRate (c K : ℝ) : Finset α ⊕ Finset (Finset α) → Marked α → ℝ
  | Sum.inl B, x => if B ∈ activeParts x then c else if B ∈ dormantParts x then c * K else 0
  | Sum.inr s, x => if s ∈ powersetCard 2 (activeParts x) then 1 else 0

def eventTarget : Finset α ⊕ Finset (Finset α) → Marked α → Marked α
  | Sum.inl B, x => flipBlock x B
  | Sum.inr s, x => mergeActive x s

theorem eventRate_nonneg {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (i : Finset α ⊕ Finset (Finset α)) (x : Marked α) : 0 ≤ eventRate c K i x := by
  rcases i with B | s
  · simp only [eventRate]
    split_ifs
    · exact hc
    · exact mul_nonneg hc hK
    · exact le_rfl
  · simp only [eventRate]
    split_ifs
    · exact zero_le_one
    · exact le_rfl

variable (α) in
/-- Source: blath_etal2016, Definition 3.1, eq. (3.1). -/
noncomputable def chain (c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) : RateChain (Marked α) :=
  eventChain (eventRate c K) eventTarget (eventRate_nonneg hc hK)

variable {c K : ℝ}

theorem sum_chain_Q_mul (hc : 0 ≤ c) (hK : 0 ≤ K) (x : Marked α) (g : Marked α → ℝ) :
    ∑ y, (chain α c K hc hK).Q x y * g y =
      ∑ B ∈ activeParts x, c * (g (flipBlock x B) - g x) +
      ∑ B ∈ dormantParts x, c * K * (g (flipBlock x B) - g x) +
      ∑ s ∈ powersetCard 2 (activeParts x), (g (mergeActive x s) - g x) := by
  rw [show (chain α c K hc hK).Q = eventQ (eventRate c K) eventTarget from rfl, sum_eventQ_mul,
    Fintype.sum_sum_type]
  have h1 : ∀ B : Finset α,
      eventRate c K (Sum.inl B) x * (g (eventTarget (Sum.inl B) x) - g x) =
        (if B ∈ activeParts x then c * (g (flipBlock x B) - g x) else 0) +
          (if B ∈ dormantParts x then c * K * (g (flipBlock x B) - g x) else 0) := by
    intro B
    have hdis : B ∈ activeParts x → B ∉ dormantParts x := fun h =>
      Finset.disjoint_left.1 (disjoint_activeParts_dormantParts x) h
    simp only [eventRate, eventTarget]
    by_cases hA : B ∈ activeParts x
    · simp [hA, hdis hA]
    · by_cases hD : B ∈ dormantParts x <;> simp [hA, hD]
  have h2 : ∀ s : Finset (Finset α),
      eventRate c K (Sum.inr s) x * (g (eventTarget (Sum.inr s) x) - g x) =
        if s ∈ powersetCard 2 (activeParts x) then g (mergeActive x s) - g x else 0 := by
    intro s
    simp only [eventRate, eventTarget]
    split_ifs <;> simp
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]

@[ext]
structure CountState (n : ℕ) where
  active : ℕ
  dormant : ℕ
  le : active + dormant ≤ n
deriving DecidableEq

namespace CountState

variable {n : ℕ}

noncomputable instance : Fintype (CountState n) :=
  Fintype.ofInjective
    (fun p : CountState n => ((⟨p.active, by have := p.le; omega⟩ : Fin (n + 1)),
      (⟨p.dormant, by have := p.le; omega⟩ : Fin (n + 1))))
    fun p q h => CountState.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)

instance : MeasurableSpace (CountState n) := ⊤

instance : DiscreteMeasurableSpace (CountState n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def toDormant (p : CountState n) : CountState n :=
  if h : 1 ≤ p.active then ⟨p.active - 1, p.dormant + 1, by have := p.le; omega⟩ else p

def toActive (p : CountState n) : CountState n :=
  if h : 1 ≤ p.dormant then ⟨p.active + 1, p.dormant - 1, by have := p.le; omega⟩ else p

def coalesce (p : CountState n) : CountState n :=
  if h : 1 ≤ p.active then ⟨p.active - 1, p.dormant, by have := p.le; omega⟩ else p

end CountState

def count (x : Marked α) : CountState (Fintype.card α) where
  active := (activeParts x).card
  dormant := (dormantParts x).card
  le := by
    rw [card_activeParts_add_card_dormantParts]
    exact le_of_le_of_eq x.partition.card_parts_le_card Finset.card_univ

theorem count_flipBlock_of_active (hB : B ∈ activeParts x) :
    count (flipBlock x B) = (count x).toDormant := by
  have h1 : 1 ≤ (count x).active := card_pos.2 ⟨B, hB⟩
  have hnd : B ∉ dormantParts x :=
    Finset.disjoint_left.1 (disjoint_activeParts_dormantParts x) hB
  rw [CountState.toDormant, dite_eq_left h1]
  ext
  · change (activeParts (flipBlock x B)).card = (activeParts x).card - 1
    rw [activeParts_flipBlock_of_active hB, card_erase_of_mem hB]
  · change (dormantParts (flipBlock x B)).card = (dormantParts x).card + 1
    rw [dormantParts_flipBlock_of_active hB, card_insert_of_notMem hnd]

theorem count_flipBlock_of_dormant (hB : B ∈ dormantParts x) :
    count (flipBlock x B) = (count x).toActive := by
  have h1 : 1 ≤ (count x).dormant := card_pos.2 ⟨B, hB⟩
  have hna : B ∉ activeParts x :=
    Finset.disjoint_right.1 (disjoint_activeParts_dormantParts x) hB
  rw [CountState.toActive, dite_eq_left h1]
  ext
  · change (activeParts (flipBlock x B)).card = (activeParts x).card + 1
    rw [activeParts_flipBlock_of_dormant hB, card_insert_of_notMem hna]
  · change (dormantParts (flipBlock x B)).card = (dormantParts x).card - 1
    rw [dormantParts_flipBlock_of_dormant hB, card_erase_of_mem hB]

theorem count_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) :
    count (mergeActive x s) = (count x).coalesce := by
  have hc := card_activeParts_mergeActive hs
  have h1 : 1 ≤ (count x).active := by
    change 1 ≤ (activeParts x).card
    omega
  rw [CountState.coalesce, dite_eq_left h1]
  ext
  · change (activeParts (mergeActive x s)).card = (activeParts x).card - 1
    omega
  · change (dormantParts (mergeActive x s)).card = (dormantParts x).card
    rw [dormantParts_mergeActive hs]

noncomputable def countRate {n : ℕ} (c K : ℝ) (i : Fin 3) (p : CountState n) : ℝ :=
  ![c * p.active, c * K * p.dormant, (p.active.choose 2 : ℝ)] i

def countTarget {n : ℕ} (i : Fin 3) (p : CountState n) : CountState n :=
  ![p.toDormant, p.toActive, p.coalesce] i

theorem countRate_nonneg {n : ℕ} (hc : 0 ≤ c) (hK : 0 ≤ K) (i : Fin 3) (p : CountState n) :
    0 ≤ countRate c K i p := by
  fin_cases i
  · exact mul_nonneg hc (Nat.cast_nonneg _)
  · exact mul_nonneg (mul_nonneg hc hK) (Nat.cast_nonneg _)
  · exact Nat.cast_nonneg _

/-- Source: blath_etal2016, Definition 2.7, eq. (2.5). -/
noncomputable def countChain (n : ℕ) (c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K) :
    RateChain (CountState n) :=
  eventChain (countRate c K) countTarget (countRate_nonneg hc hK)

theorem sum_countChain_Q_mul {n : ℕ} (hc : 0 ≤ c) (hK : 0 ≤ K) (p : CountState n)
    (g : CountState n → ℝ) :
    ∑ q, (countChain n c K hc hK).Q p q * g q =
      c * p.active * (g p.toDormant - g p) + c * K * p.dormant * (g p.toActive - g p) +
      (p.active.choose 2 : ℝ) * (g p.coalesce - g p) := by
  rw [show (countChain n c K hc hK).Q = eventQ (countRate c K) countTarget from rfl,
    sum_eventQ_mul, Fin.sum_univ_three]
  rfl

/-- Source: blath_etal2016, Definition 2.7, eq. (2.5); blath_etal2016, Definition 3.1. -/
theorem chain_lumps_count (hc : 0 ≤ c) (hK : 0 ≤ K) :
    (chain α c K hc hK).Lumps count (countChain (Fintype.card α) c K hc hK) := by
  refine lumps_of_forall_sum fun g x => ?_
  have e1 : ∀ B ∈ activeParts x, c * (g (count (flipBlock x B)) - g (count x)) =
      c * (g (count x).toDormant - g (count x)) := fun B hB => by
    rw [count_flipBlock_of_active hB]
  have e2 : ∀ B ∈ dormantParts x, c * K * (g (count (flipBlock x B)) - g (count x)) =
      c * K * (g (count x).toActive - g (count x)) := fun B hB => by
    rw [count_flipBlock_of_dormant hB]
  have e3 : ∀ s ∈ powersetCard 2 (activeParts x), g (count (mergeActive x s)) - g (count x) =
      g (count x).coalesce - g (count x) := fun s hs => by
    rw [count_mergeActive hs]
  rw [sum_chain_Q_mul hc hK x fun y => g (count y), sum_countChain_Q_mul,
    Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3]
  simp only [Finset.sum_const, card_powersetCard, nsmul_eq_mul]
  change _ = c * ((activeParts x).card : ℝ) * _ + c * K * ((dormantParts x).card : ℝ) * _ +
    (((activeParts x).card.choose 2 : ℕ) : ℝ) * _
  ring

theorem ne_flipBlock (hB : B ∈ x.partition.parts) : x ≠ flipBlock x B := by
  intro h
  obtain ⟨a, ha⟩ := x.partition.nonempty_of_mem_parts hB
  have h1 := congrFun (congrArg Marked.dormant h) a
  rw [flipBlock_dormant hB, ite_eq_left ha] at h1
  cases hd : x.dormant a <;> simp [hd] at h1

theorem flipBlock_injOn (hB : B ∈ x.partition.parts) (hC : C ∈ x.partition.parts)
    (h : flipBlock x B = flipBlock x C) : B = C := by
  by_contra hne
  obtain ⟨a, ha⟩ := x.partition.nonempty_of_mem_parts hB
  have ha' : a ∉ C := Finset.disjoint_left.1 (x.partition.disjoint hB hC hne) ha
  have h1 := congrFun (congrArg Marked.dormant h) a
  rw [flipBlock_dormant hB, flipBlock_dormant hC, ite_eq_left ha, ite_eq_right ha'] at h1
  cases hd : x.dormant a <;> simp [hd] at h1

theorem card_parts_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) :
    (mergeActive x s).partition.parts.card + 1 = x.partition.parts.card := by
  rw [mem_powersetCard] at hs
  rw [mergeActive_partition hs.1]
  exact card_parts_mergeBlocks (hs.1.trans (activeParts_subset x)) hs.2

theorem mergeActive_ne_flipBlock (hs : s ∈ powersetCard 2 (activeParts x)) (B : Finset α) :
    mergeActive x s ≠ flipBlock x B := by
  intro h
  have h1 := card_parts_mergeActive hs
  rw [h, flipBlock_partition] at h1
  omega

theorem ne_mergeActive (hs : s ∈ powersetCard 2 (activeParts x)) : x ≠ mergeActive x s := by
  intro h
  have h1 := card_parts_mergeActive hs
  rw [← h] at h1
  omega

theorem mergeActive_injOn {t : Finset (Finset α)} (hs : s ∈ powersetCard 2 (activeParts x))
    (ht : t ∈ powersetCard 2 (activeParts x)) (h : mergeActive x s = mergeActive x t) :
    s = t := by
  rw [mem_powersetCard] at hs ht
  have h1 := congrArg Marked.partition h
  rw [mergeActive_partition hs.1, mergeActive_partition ht.1] at h1
  rw [← parts_sdiff_parts_mergeBlocks (hs.1.trans (activeParts_subset x)) hs.2,
    ← parts_sdiff_parts_mergeBlocks (ht.1.trans (activeParts_subset x)) ht.2, h1]

theorem chain_Q_of_ne (hc : 0 ≤ c) (hK : 0 ≤ K) {x y : Marked α} (hxy : x ≠ y) :
    (chain α c K hc hK).Q x y =
      ∑ B ∈ activeParts x, (if flipBlock x B = y then c else 0) +
      ∑ B ∈ dormantParts x, (if flipBlock x B = y then c * K else 0) +
      ∑ s ∈ powersetCard 2 (activeParts x), (if mergeActive x s = y then (1 : ℝ) else 0) := by
  have h := sum_chain_Q_mul hc hK x fun z => if z = y then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte, hxy,
    sub_zero] at h
  exact h

theorem chain_Q_deactivate (hc : 0 ≤ c) (hK : 0 ≤ K) (hB : B ∈ activeParts x) :
    (chain α c K hc hK).Q x (flipBlock x B) = c := by
  have hBp := activeParts_subset x hB
  have hnd : B ∉ dormantParts x :=
    Finset.disjoint_left.1 (disjoint_activeParts_dormantParts x) hB
  have h1 : ∑ C ∈ activeParts x, (if flipBlock x C = flipBlock x B then c else 0) = c := by
    rw [Finset.sum_eq_single_of_mem B hB fun C hC hne => ite_eq_right fun h =>
      hne (flipBlock_injOn (activeParts_subset x hC) hBp h)]
    simp
  have h2 : ∑ C ∈ dormantParts x, (if flipBlock x C = flipBlock x B then c * K else 0) = 0 :=
    Finset.sum_eq_zero fun C hC => ite_eq_right fun h =>
      hnd (flipBlock_injOn (dormantParts_subset x hC) hBp h ▸ hC)
  have h3 : ∑ s ∈ powersetCard 2 (activeParts x),
      (if mergeActive x s = flipBlock x B then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun s hs => ite_eq_right (mergeActive_ne_flipBlock hs B)
  rw [chain_Q_of_ne hc hK (ne_flipBlock hBp), h1, h2, h3, add_zero, add_zero]

theorem chain_Q_activate (hc : 0 ≤ c) (hK : 0 ≤ K) (hB : B ∈ dormantParts x) :
    (chain α c K hc hK).Q x (flipBlock x B) = c * K := by
  have hBp := dormantParts_subset x hB
  have hna : B ∉ activeParts x :=
    Finset.disjoint_right.1 (disjoint_activeParts_dormantParts x) hB
  have h1 : ∑ C ∈ activeParts x, (if flipBlock x C = flipBlock x B then c else 0) = 0 :=
    Finset.sum_eq_zero fun C hC => ite_eq_right fun h =>
      hna (flipBlock_injOn (activeParts_subset x hC) hBp h ▸ hC)
  have h2 : ∑ C ∈ dormantParts x, (if flipBlock x C = flipBlock x B then c * K else 0) =
      c * K := by
    rw [Finset.sum_eq_single_of_mem B hB fun C hC hne => ite_eq_right fun h =>
      hne (flipBlock_injOn (dormantParts_subset x hC) hBp h)]
    simp
  have h3 : ∑ s ∈ powersetCard 2 (activeParts x),
      (if mergeActive x s = flipBlock x B then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun s hs => ite_eq_right (mergeActive_ne_flipBlock hs B)
  rw [chain_Q_of_ne hc hK (ne_flipBlock hBp), h1, h2, h3, zero_add, add_zero]

theorem chain_Q_merge (hc : 0 ≤ c) (hK : 0 ≤ K) (hs : s ∈ powersetCard 2 (activeParts x)) :
    (chain α c K hc hK).Q x (mergeActive x s) = 1 := by
  have h1 : ∑ C ∈ activeParts x, (if flipBlock x C = mergeActive x s then c else 0) = 0 :=
    Finset.sum_eq_zero fun C _ => ite_eq_right fun h => mergeActive_ne_flipBlock hs C h.symm
  have h2 : ∑ C ∈ dormantParts x, (if flipBlock x C = mergeActive x s then c * K else 0) = 0 :=
    Finset.sum_eq_zero fun C _ => ite_eq_right fun h => mergeActive_ne_flipBlock hs C h.symm
  have h3 : ∑ t ∈ powersetCard 2 (activeParts x),
      (if mergeActive x t = mergeActive x s then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem s hs fun t ht hne => ite_eq_right fun h =>
      hne (mergeActive_injOn ht hs h)]
    simp
  rw [chain_Q_of_ne hc hK (ne_mergeActive hs), h1, h2, h3, zero_add, zero_add]

theorem exists_event_of_chain_Q_ne_zero (hc : 0 ≤ c) (hK : 0 ≤ K) {x y : Marked α}
    (hxy : x ≠ y) (h : (chain α c K hc hK).Q x y ≠ 0) :
    (∃ B ∈ activeParts x, y = flipBlock x B) ∨ (∃ B ∈ dormantParts x, y = flipBlock x B) ∨
      ∃ s ∈ powersetCard 2 (activeParts x), y = mergeActive x s := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  have h1 : ∑ B ∈ activeParts x, (if flipBlock x B = y then c else 0) = 0 :=
    Finset.sum_eq_zero fun B hB => ite_eq_right fun he => hcon.1 ⟨B, hB, he.symm⟩
  have h2 : ∑ B ∈ dormantParts x, (if flipBlock x B = y then c * K else 0) = 0 :=
    Finset.sum_eq_zero fun B hB => ite_eq_right fun he => hcon.2.1 ⟨B, hB, he.symm⟩
  have h3 : ∑ s ∈ powersetCard 2 (activeParts x),
      (if mergeActive x s = y then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun s hs => ite_eq_right fun he => hcon.2.2 ⟨s, hs, he.symm⟩
  exact h (by rw [chain_Q_of_ne hc hK hxy, h1, h2, h3, add_zero, add_zero])

namespace CountState

variable {n : ℕ} {p : CountState n}

theorem toDormant_ne (h : 1 ≤ p.active) : p.toDormant ≠ p := by
  intro he
  have h1 := congrArg CountState.dormant he
  rw [toDormant, dite_eq_left h] at h1
  change p.dormant + 1 = p.dormant at h1
  omega

theorem toActive_ne (h : 1 ≤ p.dormant) : p.toActive ≠ p := by
  intro he
  have h1 := congrArg CountState.dormant he
  rw [toActive, dite_eq_left h] at h1
  change p.dormant - 1 = p.dormant at h1
  omega

theorem coalesce_ne (h : 1 ≤ p.active) : p.coalesce ≠ p := by
  intro he
  have h1 := congrArg CountState.active he
  rw [coalesce, dite_eq_left h] at h1
  change p.active - 1 = p.active at h1
  omega

end CountState

theorem chain_Q_eq_zero_of_count_eq (hc : 0 ≤ c) (hK : 0 ≤ K) {x y : Marked α} (hxy : x ≠ y)
    (h : count x = count y) : (chain α c K hc hK).Q x y = 0 := by
  by_contra hne
  rcases exists_event_of_chain_Q_ne_zero hc hK hxy hne with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩ |
    ⟨s, hs, rfl⟩
  · rw [count_flipBlock_of_active hB] at h
    exact CountState.toDormant_ne (p := count x) (card_pos.2 ⟨B, hB⟩) h.symm
  · rw [count_flipBlock_of_dormant hB] at h
    exact CountState.toActive_ne (p := count x) (card_pos.2 ⟨B, hB⟩) h.symm
  · rw [count_mergeActive hs] at h
    have h1 := card_activeParts_mergeActive hs
    exact CountState.coalesce_ne (p := count x)
      (by change 1 ≤ (activeParts x).card; omega) h.symm

theorem countChain_rate {n : ℕ} (hc : 0 ≤ c) (hK : 0 ≤ K) (p : CountState n) :
    (countChain n c K hc hK).rate p =
      c * p.active + c * K * p.dormant + (p.active.choose 2 : ℝ) := by
  have h := sum_countChain_Q_mul hc hK p fun q => if q = p then (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte] at h
  have h1 : c * p.active * ((if p.toDormant = p then (1 : ℝ) else 0) - 1) =
      -(c * p.active) := by
    by_cases ha : 1 ≤ p.active
    · rw [ite_eq_right (CountState.toDormant_ne ha)]
      ring
    · have h0 : p.active = 0 := by omega
      simp [h0]
  have h2 : c * K * p.dormant * ((if p.toActive = p then (1 : ℝ) else 0) - 1) =
      -(c * K * p.dormant) := by
    by_cases hd : 1 ≤ p.dormant
    · rw [ite_eq_right (CountState.toActive_ne hd)]
      ring
    · have h0 : p.dormant = 0 := by omega
      simp [h0]
  have h3 : (p.active.choose 2 : ℝ) * ((if p.coalesce = p then (1 : ℝ) else 0) - 1) =
      -(p.active.choose 2 : ℝ) := by
    by_cases ha : 1 ≤ p.active
    · rw [ite_eq_right (CountState.coalesce_ne ha)]
      ring
    · have h0 : p.active = 0 := by omega
      simp [h0]
  rw [RateChain.rate, h, h1, h2, h3]
  ring

theorem chain_rate (hc : 0 ≤ c) (hK : 0 ≤ K) (x : Marked α) :
    (chain α c K hc hK).rate x =
      c * (activeParts x).card + c * K * (dormantParts x).card +
        ((activeParts x).card.choose 2 : ℝ) := by
  rw [(chain_lumps_count hc hK).rate_eq (fun _ _ => chain_Q_eq_zero_of_count_eq hc hK) x,
    countChain_rate]
  rfl

end Rhone.Coalescent.SeedBank
