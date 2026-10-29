/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Cannings
public import Rhone.Coalescent.KingmanPartition
public import Mathlib.Logic.Equiv.Embedding
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.Cast

/-!
# The ancestral chain of a Cannings model on partitions of the sample

Source: mohle_sagitov2001, p. 1548, eq. (3). -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Rhone.Combinatorics MarkovChain

section Embeddings

variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]

theorem card_filter_trans_embedding (x : Y ↪ X) (R : (Y ↪ C) → Prop) [DecidablePred R] :
    (univ.filter fun e : X ↪ C => R (x.trans e)).card =
      (univ.filter R).card *
        (Fintype.card C - Fintype.card Y).descFactorial (Fintype.card X - Fintype.card Y) := by
  classical
  let φ : Y ⊕ ↥(Set.range x)ᶜ ≃ X :=
    (Equiv.sumCongr (Equiv.ofInjective x x.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range x))
  let Ψ : (X ↪ C) ≃ Σ u : Y ↪ C, (↥(Set.range x)ᶜ ↪ ↥(Set.range u)ᶜ) :=
    (Equiv.embeddingCongr φ.symm (Equiv.refl C)).trans
      Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted
  have hΨ : ∀ e, (Ψ e).1 = x.trans e := by
    intro e
    ext y
    rfl
  have hcard : ∀ u : Y ↪ C, Fintype.card (↥(Set.range x)ᶜ ↪ ↥(Set.range u)ᶜ) =
      (Fintype.card C - Fintype.card Y).descFactorial (Fintype.card X - Fintype.card Y) := by
    intro u
    rw [Fintype.card_embedding_eq, Fintype.card_compl_set, Fintype.card_compl_set,
      Set.card_range_of_injective x.injective, Set.card_range_of_injective u.injective]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  rw [Fintype.card_congr ((Ψ.subtypeEquiv (q := fun s => R s.1) fun e => by rw [hΨ]).trans
    (Equiv.subtypeSigmaEquiv _ R)), Fintype.card_sigma]
  simp [hcard]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : ι → ℕ)

theorem card_filter_embedding_fst_eq (p : ι) :
    (univ.filter fun u : Y ↪ Σ p, Fin (ν p) => ∀ y, (u y).1 = p).card =
      (ν p).descFactorial (Fintype.card Y) := by
  classical
  rw [← Fintype.card_subtype]
  let e : {u : Y ↪ Σ p, Fin (ν p) // ∀ y, (u y).1 = p} ≃ (Y ↪ Fin (ν p)) :=
    (Equiv.codRestrict Y {s : Σ p, Fin (ν p) | s.1 = p}).trans
      (Equiv.embeddingCongr (Equiv.refl Y) (Equiv.sigmaSubtype p))
  exact (Fintype.card_congr e).trans (by rw [Fintype.card_embedding_eq, Fintype.card_fin])

theorem card_filter_embedding_fst_const (y₀ : Y) :
    (univ.filter fun u : Y ↪ Σ p, Fin (ν p) => ∀ y, (u y).1 = (u y₀).1).card =
      ∑ p, (ν p).descFactorial (Fintype.card Y) := by
  rw [card_eq_sum_card_fiberwise (f := fun u : Y ↪ Σ p, Fin (ν p) => (u y₀).1) (t := univ)
    fun _ _ => mem_coe.2 (mem_univ _)]
  refine sum_congr rfl fun p _ => ?_
  rw [← card_filter_embedding_fst_eq ν p]
  congr 1
  ext u
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h, hp⟩ y
    rw [h y, hp]
  · intro h
    exact ⟨fun y => by rw [h y, h y₀], h y₀⟩

theorem card_filter_sameParent (x : Y ↪ X) (y₀ : Y) :
    (univ.filter fun e : X ↪ Σ p, Fin (ν p) => ∀ y, (e (x y)).1 = (e (x y₀)).1).card =
      (∑ p, (ν p).descFactorial (Fintype.card Y)) *
        (∑ p, ν p - Fintype.card Y).descFactorial (Fintype.card X - Fintype.card Y) := by
  have h := card_filter_trans_embedding (C := Σ p, Fin (ν p)) x
    (fun u => ∀ y, (u y).1 = (u y₀).1)
  rw [card_filter_embedding_fst_const ν y₀] at h
  simpa using h

end Embeddings

section Partitions

variable {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} [DecidableEq β]

def kerPartition (f : α → β) : Finpartition (univ : Finset α) :=
  haveI : DecidableRel (Setoid.ker f).r := fun a b => inferInstanceAs (Decidable (f a = f b))
  Finpartition.ofSetoid (Setoid.ker f)

theorem mem_part_kerPartition (f : α → β) {a b : α} :
    b ∈ (kerPartition f).part a ↔ f a = f b :=
  Finpartition.mem_part_ofSetoid_iff_rel

theorem finpartition_eq_of_mem_part_iff {P Q : Finpartition (univ : Finset α)}
    (h : ∀ a b, b ∈ P.part a ↔ b ∈ Q.part a) : P = Q := by
  have hpart : ∀ a, P.part a = Q.part a := fun a => Finset.ext fun b => h a b
  have key : ∀ {P Q : Finpartition (univ : Finset α)}, (∀ a, P.part a = Q.part a) →
      P.parts ⊆ Q.parts := by
    intro P Q hPQ p hp
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hp
    rw [← P.part_eq_of_mem hp ha, hPQ a]
    exact Q.part_mem.2 (mem_univ a)
  exact Finpartition.ext (Subset.antisymm (key hpart) (key fun a => (hpart a).symm))

variable {π : Finpartition (univ : Finset α)}

theorem mem_part_iff_part_eq {a b : α} : b ∈ π.part a ↔ π.part b = π.part a :=
  ⟨fun h => π.part_eq_of_mem (π.part_mem.2 (mem_univ a)) h,
    fun h => h ▸ π.mem_part (mem_univ b)⟩

theorem mem_part_mergeBlocks {s : Finset (Finset α)} (hs : s ⊆ π.parts) (hne : s.Nonempty)
    {a b : α} :
    b ∈ (mergeBlocks π s).part a ↔ (π.part a ∈ s ∧ π.part b ∈ s) ∨ π.part b = π.part a := by
  have hsup : ∀ c : α, c ∈ s.sup id ↔ π.part c ∈ s := by
    intro c
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨C, hC, hcC⟩
      rwa [π.part_eq_of_mem (hs hC) hcC]
    · intro h
      exact ⟨π.part c, h, π.mem_part (mem_univ c)⟩
  rw [Finpartition.mem_part_iff_exists, parts_mergeBlocks hs hne]
  constructor
  · rintro ⟨p, hp, hbp, hap⟩
    rcases mem_insert.1 hp with rfl | hp
    · exact Or.inl ⟨(hsup a).1 hap, (hsup b).1 hbp⟩
    · have hpπ := (mem_sdiff.1 hp).1
      exact Or.inr ((π.part_eq_of_mem hpπ hbp).trans (π.part_eq_of_mem hpπ hap).symm)
  · rintro (⟨ha, hb⟩ | h)
    · exact ⟨s.sup id, mem_insert_self _ _, (hsup b).2 hb, (hsup a).2 ha⟩
    · by_cases ha : π.part a ∈ s
      · exact ⟨s.sup id, mem_insert_self _ _, (hsup b).2 (h ▸ ha), (hsup a).2 ha⟩
      · refine ⟨π.part a, mem_insert_of_mem (mem_sdiff.2 ⟨π.part_mem.2 (mem_univ a), ha⟩), ?_,
          π.mem_part (mem_univ a)⟩
        rw [← h]
        exact π.mem_part (mem_univ b)

def blockOf (π : Finpartition (univ : Finset α)) (a : α) : {B // B ∈ π.parts} :=
  ⟨π.part a, π.part_mem.2 (mem_univ a)⟩

theorem exists_blockOf_eq (x : {B // B ∈ π.parts}) : ∃ a, a ∈ x.1 ∧ blockOf π a = x := by
  obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts x.2
  exact ⟨a, ha, Subtype.ext (π.part_eq_of_mem x.2 ha)⟩

theorem pair_subset_parts (x y : {B // B ∈ π.parts}) :
    ({x.1, y.1} : Finset (Finset α)) ⊆ π.parts := by
  intro B hB
  rcases mem_insert.1 hB with rfl | hB
  · exact x.2
  · rw [mem_singleton.1 hB]
    exact y.2

theorem mergeBlocks_pair_mem_merges {x y : {B // B ∈ π.parts}} (hxy : x ≠ y) :
    mergeBlocks π {x.1, y.1} ∈ merges π :=
  mem_image.2 ⟨{x.1, y.1}, mem_powersetCard.2 ⟨pair_subset_parts x y,
    card_pair fun h => hxy (Subtype.ext h)⟩, rfl⟩

theorem exists_pair_of_mem_merges {σ : Finpartition (univ : Finset α)} (h : σ ∈ merges π) :
    ∃ x y : {B // B ∈ π.parts}, x ≠ y ∧ σ = mergeBlocks π {x.1, y.1} := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 h
  rw [mem_powersetCard] at hs
  obtain ⟨B, B', hBB', rfl⟩ := Finset.card_eq_two.1 hs.2
  exact ⟨⟨B, hs.1 (by simp)⟩, ⟨B', hs.1 (by simp)⟩, fun h => hBB' (Subtype.ext_iff.1 h), rfl⟩

variable (g : {B // B ∈ π.parts} → β)

theorem kerPartition_blockOf_of_injective (hg : Function.Injective g) :
    kerPartition (fun a => g (blockOf π a)) = π := by
  refine finpartition_eq_of_mem_part_iff fun a b => ?_
  rw [mem_part_kerPartition, mem_part_iff_part_eq, hg.eq_iff]
  exact ⟨fun h => (Subtype.ext_iff.1 h).symm, fun h => Subtype.ext h.symm⟩

theorem kerPartition_blockOf_of_pair {x y : {B // B ∈ π.parts}} (hg : g x = g y)
    (huniq : ∀ u v, u ≠ v → g u = g v → (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
    kerPartition (fun a => g (blockOf π a)) = mergeBlocks π {x.1, y.1} := by
  have hmem : ∀ c : α, π.part c ∈ ({x.1, y.1} : Finset (Finset α)) ↔
      blockOf π c = x ∨ blockOf π c = y := by
    intro c
    rw [mem_insert, mem_singleton]
    exact or_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine finpartition_eq_of_mem_part_iff fun a b => ?_
  rw [mem_part_kerPartition, mem_part_mergeBlocks (pair_subset_parts x y) (insert_nonempty _ _),
    hmem, hmem]
  constructor
  · intro h
    by_cases hab : blockOf π a = blockOf π b
    · exact Or.inr (Subtype.ext_iff.1 hab).symm
    · rcases huniq _ _ hab h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Or.inl h1, Or.inr h2⟩
      · exact Or.inl ⟨Or.inr h1, Or.inl h2⟩
  · rintro (⟨ha, hb⟩ | h)
    · rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2]
      · exact hg
      · exact hg.symm
    · exact congrArg g (Subtype.ext h.symm)

theorem apply_eq_of_kerPartition_blockOf_eq {x y : {B // B ∈ π.parts}}
    (h : kerPartition (fun a => g (blockOf π a)) = mergeBlocks π {x.1, y.1}) : g x = g y := by
  obtain ⟨a, -, hax⟩ := exists_blockOf_eq x
  obtain ⟨b, -, hby⟩ := exists_blockOf_eq y
  have hmem : b ∈ (mergeBlocks π {x.1, y.1}).part a := by
    refine (mem_part_mergeBlocks (pair_subset_parts x y) (insert_nonempty _ _)).2
      (Or.inl ⟨?_, ?_⟩)
    · rw [← hax]
      exact mem_insert_self _ _
    · rw [← hby]
      exact mem_insert_of_mem (mem_singleton_self _)
  rw [← h, mem_part_kerPartition] at hmem
  rwa [hax, hby] at hmem

end Partitions

end Rhone.Coalescent

namespace Rhone.MarkovChain.CanningsModel

open Finset Coalescent Rhone.Combinatorics

variable {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)

abbrev Child (ω : Ω) : Type := Σ p : Fin N, Fin (M.ν ω p)

theorem card_child (ω : Ω) : Fintype.card (M.Child ω) = N := by
  rw [Fintype.card_sigma]
  simp [M.sum_ν ω]

def pairCount (ω : Ω) : ℕ := ∑ p, (M.ν ω p).descFactorial 2

def tripleCount (ω : Ω) : ℕ := ∑ p, (M.ν ω p).descFactorial 3

noncomputable def pairCoalProb : ℝ :=
  (∑ ω, M.w ω * ∑ p, ((M.ν ω p).descFactorial 2 : ℝ)) / ((N : ℝ) * (N - 1))

noncomputable def tripleCoalProb : ℝ :=
  (∑ ω, M.w ω * ∑ p, ((M.ν ω p).descFactorial 3 : ℝ)) / ((N : ℝ) * (N - 1) * (N - 2))

theorem cast_descFactorial_three (a : ℕ) :
    ((a.descFactorial 3 : ℕ) : ℝ) = (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) := by
  rcases a with _ | _ | _ | a
  · simp
  · simp
  · norm_num [Nat.descFactorial]
  · rw [Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ,
      Nat.descFactorial_zero]
    push_cast
    ring

theorem pairCoalProb_eq_sum :
    M.pairCoalProb = ∑ ω, M.w ω * ((M.pairCount ω : ℝ) / (N.descFactorial 2 : ℝ)) := by
  rw [pairCoalProb, Finset.sum_div, Nat.cast_descFactorial_two]
  refine sum_congr rfl fun ω _ => ?_
  rw [pairCount, mul_div_assoc]
  push_cast
  rfl

theorem tripleCoalProb_eq_sum :
    M.tripleCoalProb = ∑ ω, M.w ω * ((M.tripleCount ω : ℝ) / (N.descFactorial 3 : ℝ)) := by
  rw [tripleCoalProb, Finset.sum_div, cast_descFactorial_three]
  refine sum_congr rfl fun ω _ => ?_
  rw [tripleCount, mul_div_assoc]
  push_cast
  rfl

theorem pairCoalProb_nonneg : 0 ≤ M.pairCoalProb := by
  rw [pairCoalProb_eq_sum]
  exact sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (by positivity)

theorem tripleCoalProb_nonneg : 0 ≤ M.tripleCoalProb := by
  rw [tripleCoalProb_eq_sum]
  exact sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (by positivity)

theorem sum_w_mul_sum_parents (g : ℕ → ℝ) (k : Fin N) :
    ∑ ω, M.w ω * ∑ p, g (M.ν ω p) = N * ∑ ω, M.w ω * g (M.ν ω k) := by
  have hp : ∀ p, ∑ ω, M.w ω * g (M.ν ω p) = ∑ ω, M.w ω * g (M.ν ω k) := by
    intro p
    have h := M.exchangeable (Equiv.swap k p) (fun x => g (x k))
    simp only [Equiv.swap_apply_left] at h
    exact h
  have e : ∀ ω, M.w ω * ∑ p, g (M.ν ω p) = ∑ p, M.w ω * g (M.ν ω p) :=
    fun ω => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => hp p]
  simp

theorem pairCoalProb_eq (k : Fin N) :
    M.pairCoalProb =
      (∑ ω, M.w ω * ((M.ν ω k : ℝ) * ((M.ν ω k : ℝ) - 1))) / ((N : ℝ) - 1) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos k).ne'
  have h := M.sum_w_mul_sum_parents (fun a => ((a.descFactorial 2 : ℕ) : ℝ)) k
  simp only [Nat.cast_descFactorial_two] at h
  rw [pairCoalProb]
  simp only [Nat.cast_descFactorial_two]
  rw [h, mul_div_mul_left _ _ hN]

theorem tripleCoalProb_eq (k : Fin N) :
    M.tripleCoalProb =
      (∑ ω, M.w ω * ((M.ν ω k : ℝ) * ((M.ν ω k : ℝ) - 1) * ((M.ν ω k : ℝ) - 2))) /
        (((N : ℝ) - 1) * ((N : ℝ) - 2)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos k).ne'
  have h := M.sum_w_mul_sum_parents (fun a => ((a.descFactorial 3 : ℕ) : ℝ)) k
  simp only [cast_descFactorial_three] at h
  rw [tripleCoalProb]
  simp only [cast_descFactorial_three]
  rw [h, mul_assoc (N : ℝ), mul_div_mul_left _ _ hN]

variable {α : Type*} [Fintype α] [DecidableEq α]

def parentPartition (ω : Ω) (π : Finpartition (univ : Finset α))
    (e : {B // B ∈ π.parts} ↪ M.Child ω) : Finpartition (univ : Finset α) :=
  kerPartition fun i => (e (blockOf π i)).1

variable (α) in
noncomputable def ancestralMatrix :
    Matrix (Finpartition (univ : Finset α)) (Finpartition (univ : Finset α)) ℝ := fun π σ =>
  ∑ ω, M.w ω * ((univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω =>
    M.parentPartition ω π e = σ).card : ℝ) / (N.descFactorial π.parts.card : ℝ)

theorem card_block_embeddings (ω : Ω) (π : Finpartition (univ : Finset α)) :
    Fintype.card ({B // B ∈ π.parts} ↪ M.Child ω) = N.descFactorial π.parts.card := by
  rw [Fintype.card_embedding_eq, Fintype.card_coe, M.card_child]

theorem card_parts_le_of_card_le (h : Fintype.card α ≤ N)
    (π : Finpartition (univ : Finset α)) : π.parts.card ≤ N :=
  (π.card_parts_le_card.trans_eq Finset.card_univ).trans h

theorem cast_descFactorial_ne_zero {b : ℕ} (h : b ≤ N) : (N.descFactorial b : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 fun h0 => absurd (Nat.descFactorial_eq_zero_iff_lt.1 h0) (not_lt.2 h)

theorem ancestralMatrix_nonneg (π σ : Finpartition (univ : Finset α)) :
    0 ≤ M.ancestralMatrix α π σ :=
  sum_nonneg fun ω _ => div_nonneg (mul_nonneg (M.w_nonneg ω) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem ancestralMatrix_row_sum (h : Fintype.card α ≤ N) (π : Finpartition (univ : Finset α)) :
    ∑ σ, M.ancestralMatrix α π σ = 1 := by
  have hpos := cast_descFactorial_ne_zero (card_parts_le_of_card_le h π)
  have hω : ∀ ω, ∑ σ, M.w ω * ((univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω =>
      M.parentPartition ω π e = σ).card : ℝ) / (N.descFactorial π.parts.card : ℝ) = M.w ω := by
    intro ω
    rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum,
      ← card_eq_sum_card_fiberwise (f := M.parentPartition ω π) (s := univ) (t := univ)
        fun _ _ => mem_coe.2 (mem_univ _),
      Finset.card_univ, M.card_block_embeddings, mul_div_assoc, div_self hpos, mul_one]
  simp only [ancestralMatrix]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun ω _ => hω ω]
  exact M.sum_w

variable (α) in
noncomputable def ancestralChain (h : Fintype.card α ≤ N) :
    FinChain (Finpartition (univ : Finset α)) where
  P := M.ancestralMatrix α
  nonneg := M.ancestralMatrix_nonneg
  row_sum := M.ancestralMatrix_row_sum h

theorem ancestralChain_P (h : Fintype.card α ≤ N) :
    (M.ancestralChain α h).P = M.ancestralMatrix α := rfl

end Rhone.MarkovChain.CanningsModel
