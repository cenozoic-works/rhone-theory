/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Sample

/-! # Blocks, the canonical labelling, and the kernel `P(ξ_A, ξ_B)` -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB KA' KB' : ℕ}

def blkA (S : Sample n) (α : Fin n → Fin KA) (k : Fin n) : Finset (Fin n) :=
  S.LA.filter fun k' => α k' = α k

def blkB (S : Sample n) (β : Fin n → Fin KB) (k : Fin n) : Finset (Fin n) :=
  S.LB.filter fun k' => β k' = β k

variable (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB)

theorem blkA_subset (k : Fin n) : blkA S α k ⊆ S.LA := Finset.filter_subset _ _

theorem blkB_subset (k : Fin n) : blkB S β k ⊆ S.LB := Finset.filter_subset _ _

theorem mem_blkA_iff {k k' : Fin n} : k' ∈ blkA S α k ↔ k' ∈ S.LA ∧ α k' = α k :=
  Finset.mem_filter

theorem mem_blkB_iff {k k' : Fin n} : k' ∈ blkB S β k ↔ k' ∈ S.LB ∧ β k' = β k :=
  Finset.mem_filter

theorem mem_blkA_self {k : Fin n} (hk : k ∈ S.LA) : k ∈ blkA S α k :=
  Finset.mem_filter.mpr ⟨hk, rfl⟩

theorem mem_blkB_self {k : Fin n} (hk : k ∈ S.LB) : k ∈ blkB S β k :=
  Finset.mem_filter.mpr ⟨hk, rfl⟩

theorem blkA_nonempty {k : Fin n} (hk : k ∈ S.LA) : (blkA S α k).Nonempty :=
  ⟨k, mem_blkA_self S α hk⟩

theorem blkA_eq_of {k k' : Fin n} (h : α k = α k') : blkA S α k = blkA S α k' := by
  simp only [blkA, h]

theorem blkB_eq_of {k k' : Fin n} (h : β k = β k') : blkB S β k = blkB S β k' := by
  simp only [blkB, h]

theorem blkA_disjoint {k k' : Fin n} (h : blkA S α k ≠ blkA S α k') :
    Disjoint (blkA S α k) (blkA S α k') :=
  Finset.disjoint_left.mpr fun _m hm hm' =>
    h (((blkA_eq_of S α (Finset.mem_filter.mp hm).2).symm.trans
      (blkA_eq_of S α (Finset.mem_filter.mp hm').2)))

def partsA : Finset (Finset (Fin n)) := S.LA.image (blkA S α)

def partsB : Finset (Finset (Fin n)) := S.LB.image (blkB S β)

theorem mem_partsA {B : Finset (Fin n)} :
    B ∈ partsA S α ↔ ∃ k ∈ S.LA, blkA S α k = B := Finset.mem_image

theorem sup_partsA : (partsA S α).sup id = S.LA := by
  refine le_antisymm (Finset.sup_le ?_) fun k hk => ?_
  · intro B hB
    obtain ⟨k, _, rfl⟩ := (mem_partsA S α).mp hB
    exact blkA_subset S α k
  · exact Finset.mem_sup.mpr ⟨blkA S α k, (mem_partsA S α).mpr ⟨k, hk, rfl⟩,
      mem_blkA_self S α hk⟩

theorem pairwiseDisjoint_partsA : (partsA S α : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro B hB B' hB' hne
  obtain ⟨k, _, rfl⟩ := (mem_partsA S α).mp hB
  obtain ⟨k', _, rfl⟩ := (mem_partsA S α).mp hB'
  exact blkA_disjoint S α hne

def finpartA : Finpartition S.LA where
  parts := partsA S α
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr (pairwiseDisjoint_partsA S α)
  sup_parts := sup_partsA S α
  bot_notMem hB := by
    obtain ⟨k, hk, hbk⟩ := (mem_partsA S α).mp hB
    exact (blkA_nonempty S α hk).ne_empty hbk

def repA (k : Fin n) : Fin n :=
  if h : (blkA S α k).Nonempty then (blkA S α k).min' h else k

def repB (k : Fin n) : Fin n :=
  if h : (blkB S β k).Nonempty then (blkB S β k).min' h else k

theorem repA_mem_blkA {k : Fin n} (hk : k ∈ S.LA) : repA S α k ∈ blkA S α k := by
  rw [repA, dite_eq_left (blkA_nonempty S α hk)]
  exact Finset.min'_mem _ _

theorem repB_mem_blkB {k : Fin n} (hk : k ∈ S.LB) : repB S β k ∈ blkB S β k := by
  rw [repB, dite_eq_left ⟨k, mem_blkB_self S β hk⟩]
  exact Finset.min'_mem _ _

theorem repA_mem {k : Fin n} (hk : k ∈ S.LA) : repA S α k ∈ S.LA :=
  blkA_subset S α k (repA_mem_blkA S α hk)

theorem repB_mem {k : Fin n} (hk : k ∈ S.LB) : repB S β k ∈ S.LB :=
  blkB_subset S β k (repB_mem_blkB S β hk)

theorem alpha_repA {k : Fin n} (hk : k ∈ S.LA) : α (repA S α k) = α k :=
  (Finset.mem_filter.mp (repA_mem_blkA S α hk)).2

theorem beta_repB {k : Fin n} (hk : k ∈ S.LB) : β (repB S β k) = β k :=
  (Finset.mem_filter.mp (repB_mem_blkB S β hk)).2

theorem repA_eq_of {k k' : Fin n} (hk : k ∈ S.LA) (hk' : k' ∈ S.LA) (h : α k = α k') :
    repA S α k = repA S α k' := by
  have hb : blkA S α k = blkA S α k' := blkA_eq_of S α h
  rw [repA, repA, dite_eq_left (blkA_nonempty S α hk), dite_eq_left (blkA_nonempty S α hk')]
  simp only [hb]

theorem repB_eq_of {k k' : Fin n} (hk : k ∈ S.LB) (hk' : k' ∈ S.LB) (h : β k = β k') :
    repB S β k = repB S β k' := by
  have hb : blkB S β k = blkB S β k' := blkB_eq_of S β h
  rw [repB, repB, dite_eq_left ⟨k, mem_blkB_self S β hk⟩, dite_eq_left ⟨k', mem_blkB_self S β hk'⟩]
  simp only [hb]

theorem repA_eq_iff {k k' : Fin n} (hk : k ∈ S.LA) (hk' : k' ∈ S.LA) :
    repA S α k = repA S α k' ↔ α k = α k' := by
  refine ⟨fun h => ?_, repA_eq_of S α hk hk'⟩
  rw [← alpha_repA S α hk, ← alpha_repA S α hk', h]

theorem repB_eq_iff {k k' : Fin n} (hk : k ∈ S.LB) (hk' : k' ∈ S.LB) :
    repB S β k = repB S β k' ↔ β k = β k' := by
  refine ⟨fun h => ?_, repB_eq_of S β hk hk'⟩
  rw [← beta_repB S β hk, ← beta_repB S β hk', h]

theorem injOn_repA : Set.InjOn α ↑(S.LA.image (repA S α)) := by
  intro x hx y hy hxy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (by simpa using hx)
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp (by simpa using hy)
  rw [alpha_repA S α hk, alpha_repA S α hk'] at hxy
  exact repA_eq_of S α hk hk' hxy

theorem injOn_repB : Set.InjOn β ↑(S.LB.image (repB S β)) := by
  intro x hx y hy hxy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (by simpa using hx)
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp (by simpa using hy)
  rw [beta_repB S β hk, beta_repB S β hk'] at hxy
  exact repB_eq_of S β hk hk' hxy

def liftFun (R : Finset (Fin n)) (α : Fin n → Fin KA) (k : Fin n) : Fin (KA + n) :=
  if k ∈ R then Fin.castAdd n (α k) else Fin.natAdd KA k

theorem liftFun_of_mem {R : Finset (Fin n)} {k : Fin n} (hk : k ∈ R) :
    liftFun R α k = Fin.castAdd n (α k) := ite_eq_left hk

theorem liftFun_injective (R : Finset (Fin n)) (h : Set.InjOn α ↑R) :
    Function.Injective (liftFun R α) := by
  intro k1 k2 hk
  simp only [liftFun] at hk
  by_cases h1 : k1 ∈ R <;> by_cases h2 : k2 ∈ R
  · rw [ite_eq_left h1, ite_eq_left h2] at hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_castAdd] at hv
    exact h (by simpa using h1) (by simpa using h2) (Fin.val_injective hv)
  · rw [ite_eq_left h1, ite_eq_right h2] at hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have := (α k1).isLt
    omega
  · rw [ite_eq_right h1, ite_eq_left h2] at hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have := (α k2).isLt
    omega
  · rw [ite_eq_right h1, ite_eq_right h2] at hk
    have hv := congrArg Fin.val hk
    simp only [Fin.val_natAdd] at hv
    exact Fin.val_injective (by omega)

noncomputable def repEmbA : Fin n ↪ Fin (KA + n) :=
  ⟨liftFun (S.LA.image (repA S α)) α, liftFun_injective α _ (injOn_repA S α)⟩

noncomputable def repEmbB : Fin n ↪ Fin (KB + n) :=
  ⟨liftFun (S.LB.image (repB S β)) β, liftFun_injective β _ (injOn_repB S β)⟩

def castAddEmb (KA n : ℕ) : Fin KA ↪ Fin (KA + n) :=
  ⟨Fin.castAdd n, fun _ _ h => Fin.val_injective (by simpa using congrArg Fin.val h)⟩

theorem repEmbA_repA {k : Fin n} (hk : k ∈ S.LA) :
    repEmbA S α (repA S α k) = castAddEmb KA n (α k) := by
  have hmem : repA S α k ∈ S.LA.image (repA S α) := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  change liftFun (S.LA.image (repA S α)) α (repA S α k) = Fin.castAdd n (α k)
  rw [liftFun_of_mem α hmem, alpha_repA S α hk]

theorem repEmbB_repB {k : Fin n} (hk : k ∈ S.LB) :
    repEmbB S β (repB S β k) = castAddEmb KB n (β k) := by
  have hmem : repB S β k ∈ S.LB.image (repB S β) := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  change liftFun (S.LB.image (repB S β)) β (repB S β k) = Fin.castAdd n (β k)
  rw [liftFun_of_mem β hmem, beta_repB S β hk]

section Kernel

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem PIA_cfgOf_rep (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    PIA (KA := KA) (KB := KB) hθA hθB hρ (cfgOf S α β)
      = PIA (KA := n) (KB := n) hθA hθB hρ (cfgOf S (repA S α) (repB S β)) := by
  rw [← PIA_push (castAddEmb KA n) (castAddEmb KB n) hθA hθB hρ (cfgOf S α β), push_cfgOf,
    cfgOf_congr S (α := fun k => castAddEmb KA n (α k))
      (α' := fun k => repEmbA S α (repA S α k))
      (β := fun k => castAddEmb KB n (β k)) (β' := fun k => repEmbB S β (repB S β k))
      (fun k hk => (repEmbA_repA S α hk).symm) (fun k hk => (repEmbB_repB S β hk).symm),
    ← push_cfgOf S (repA S α) (repB S β) (repEmbA S α) (repEmbB S β),
    PIA_push (repEmbA S α) (repEmbB S β) hθA hθB hρ]

noncomputable def Plab (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (S : Sample n)
    (α : Fin n → Fin KA) (β : Fin n → Fin KB) : F :=
  PIA hθA hθB hρ (cfgOf S α β)

theorem Plab_eq_rep (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    Plab hθA hθB hρ S α β = Plab hθA hθB hρ S (repA S α) (repB S β) :=
  PIA_cfgOf_rep S α β hθA hθB hρ

end Kernel

def SamePartA (S : Sample n) (α : Fin n → Fin KA) (α' : Fin n → Fin KA') : Prop :=
  ∀ k ∈ S.LA, ∀ k' ∈ S.LA, (α k = α k' ↔ α' k = α' k')

def SamePartB (S : Sample n) (β : Fin n → Fin KB) (β' : Fin n → Fin KB') : Prop :=
  ∀ k ∈ S.LB, ∀ k' ∈ S.LB, (β k = β k' ↔ β' k = β' k')

theorem blkA_congr {α' : Fin n → Fin KA'} (h : SamePartA S α α') {k : Fin n} (hk : k ∈ S.LA) :
    blkA S α k = blkA S α' k :=
  Finset.filter_congr fun k' hk' => h k' hk' k hk

theorem blkB_congr {β' : Fin n → Fin KB'} (h : SamePartB S β β') {k : Fin n} (hk : k ∈ S.LB) :
    blkB S β k = blkB S β' k :=
  Finset.filter_congr fun k' hk' => h k' hk' k hk

theorem repA_congr {α' : Fin n → Fin KA'} (h : SamePartA S α α') {k : Fin n} (hk : k ∈ S.LA) :
    repA S α k = repA S α' k := by
  have hb : blkA S α k = blkA S α' k := blkA_congr S α h hk
  rw [repA, repA, dite_eq_left (blkA_nonempty S α hk), dite_eq_left (blkA_nonempty S α' hk)]
  simp only [hb]

theorem repB_congr {β' : Fin n → Fin KB'} (h : SamePartB S β β') {k : Fin n} (hk : k ∈ S.LB) :
    repB S β k = repB S β' k := by
  have hb : blkB S β k = blkB S β' k := blkB_congr S β h hk
  rw [repB, repB, dite_eq_left ⟨k, mem_blkB_self S β hk⟩, dite_eq_left ⟨k, mem_blkB_self S β' hk⟩]
  simp only [hb]

theorem samePartA_iff_blkA {α' : Fin n → Fin KA'} :
    SamePartA S α α' ↔ ∀ k ∈ S.LA, blkA S α k = blkA S α' k := by
  refine ⟨fun h k hk => blkA_congr S α h hk, fun h k hk k' hk' => ?_⟩
  constructor
  · intro hα
    have hm : k' ∈ blkA S α' k := by
      rw [← h k hk]; exact Finset.mem_filter.mpr ⟨hk', hα.symm⟩
    exact ((Finset.mem_filter.mp hm).2).symm
  · intro hα
    have hm : k' ∈ blkA S α k := by
      rw [h k hk]; exact Finset.mem_filter.mpr ⟨hk', hα.symm⟩
    exact ((Finset.mem_filter.mp hm).2).symm

theorem samePartA_iff_partsA {α' : Fin n → Fin KA'} :
    SamePartA S α α' ↔ partsA S α = partsA S α' := by
  rw [samePartA_iff_blkA]
  refine ⟨fun h => ?_, fun h k hk => ?_⟩
  · refine Finset.image_congr ?_
    intro k hk
    exact h k hk
  · have hmem : blkA S α k ∈ partsA S α' := by
      rw [← h]; exact (mem_partsA S α).mpr ⟨k, hk, rfl⟩
    obtain ⟨m, hm, hmk⟩ := (mem_partsA S α').mp hmem
    have hk' : k ∈ blkA S α' m := by rw [hmk]; exact mem_blkA_self S α hk
    rw [← hmk, blkA_eq_of S α' (Finset.mem_filter.mp hk').2]

section Wd

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem Plab_congr_part (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {α' : Fin n → Fin KA'} {β' : Fin n → Fin KB'}
    (hA : SamePartA S α α') (hB : SamePartB S β β') :
    Plab hθA hθB hρ S α β = Plab hθA hθB hρ S α' β' := by
  rw [Plab_eq_rep S α β hθA hθB hρ, Plab_eq_rep S α' β' hθA hθB hρ]
  exact congrArg _ (cfgOf_congr S (fun k hk => repA_congr S α hA hk)
    fun k hk => repB_congr S β hB hk)

theorem Plab_relabel_alleles (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) :
    Plab hθA hθB hρ S (fun k => σ (α k)) (fun k => τ (β k)) = Plab hθA hθB hρ S α β := by
  rw [Plab, Plab, cfgOf_relabel, PIA_relabel]

theorem Plab_emb (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {K L : ℕ}
    (e : Fin KA ↪ Fin K) (f : Fin KB ↪ Fin L) :
    Plab hθA hθB hρ S (fun k => e (α k)) (fun k => f (β k)) = Plab hθA hθB hρ S α β := by
  rw [Plab, Plab, ← push_cfgOf, PIA_push]

theorem Plab_perm (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (π : Equiv.Perm (Fin n))
    (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) :
    Plab hθA hθB hρ S (fun k => α (π k)) (fun k => β (π k)) = Plab hθA hθB hρ S α β := by
  rw [Plab, Plab, cfgOf_perm S α β π hA hB]

end Wd

end Rhone.Probability.InfiniteAlleles
