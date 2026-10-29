/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Count
public import Rhone.Probability.InfiniteAlleles.Blocks

/-! # Shapes, and the transitivity of `S_n` on partitions of a fixed shape -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB : ℕ} (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB)

def mAcount (i : Fin KA) : ℕ := (S.LA.filter fun k => α k = i).card

def mBcount (j : Fin KB) : ℕ := (S.LB.filter fun k => β k = j).card

def blockOfLabelA (i : Fin KA) : Finset (Fin n) := S.LA.filter fun k => α k = i

def blockOfLabelB (j : Fin KB) : Finset (Fin n) := S.LB.filter fun k => β k = j

def shapeA : Multiset ℕ := (Multiset.map (mAcount S α) Finset.univ.val).filter (0 < ·)

def shapeB : Multiset ℕ := (Multiset.map (mBcount S β) Finset.univ.val).filter (0 < ·)

theorem usedA_eq_filter : S.LA.image α = Finset.univ.filter fun i => 0 < mAcount S α i := by
  ext i
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mAcount,
    Finset.card_pos]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
    exact ⟨k, h1, h2⟩

theorem usedB_eq_filter : S.LB.image β = Finset.univ.filter fun j => 0 < mBcount S β j := by
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mBcount,
    Finset.card_pos]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hk
    exact ⟨k, h1, h2⟩

theorem partsA_eq_image : partsA S α = (S.LA.image α).image (blockOfLabelA S α) := by
  rw [partsA, Finset.image_image]
  rfl

theorem partsB_eq_image : partsB S β = (S.LB.image β).image (blockOfLabelB S β) := by
  rw [partsB, Finset.image_image]
  rfl

theorem injOn_blockOfLabelA : Set.InjOn (blockOfLabelA S α) ↑(S.LA.image α) := by
  intro i hi i' _ h
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (by simpa using hi)
  have hmem : k ∈ blockOfLabelA S α (α k) := Finset.mem_filter.mpr ⟨hk, rfl⟩
  rw [h] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem injOn_blockOfLabelB : Set.InjOn (blockOfLabelB S β) ↑(S.LB.image β) := by
  intro j hj j' _ h
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (by simpa using hj)
  have hmem : k ∈ blockOfLabelB S β (β k) := Finset.mem_filter.mpr ⟨hk, rfl⟩
  rw [h] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem shapeA_eq_blockSizes : shapeA S α = (partsA S α).val.map Finset.card := by
  have h1 : (partsA S α).val.map Finset.card = (S.LA.image α).val.map (mAcount S α) := by
    rw [partsA_eq_image, Finset.image_val_of_injOn (injOn_blockOfLabelA S α), Multiset.map_map]
    rfl
  rw [h1, shapeA, Multiset.filter_map, usedA_eq_filter, Finset.filter_val]
  rfl

theorem shapeB_eq_blockSizes : shapeB S β = (partsB S β).val.map Finset.card := by
  have h1 : (partsB S β).val.map Finset.card = (S.LB.image β).val.map (mBcount S β) := by
    rw [partsB_eq_image, Finset.image_val_of_injOn (injOn_blockOfLabelB S β), Multiset.map_map]
    rfl
  rw [h1, shapeB, Multiset.filter_map, usedB_eq_filter, Finset.filter_val]
  rfl

theorem mAcount_perm (π : Equiv.Perm (Fin n)) (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) (i : Fin KA) :
    mAcount S (fun k => α (π k)) i = mAcount S α i :=
  card_filter_perm π S.LA hA fun k => α k = i

theorem shapeA_perm (π : Equiv.Perm (Fin n)) (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) :
    shapeA S (fun k => α (π k)) = shapeA S α := by
  rw [shapeA, shapeA, funext fun i => mAcount_perm S α π hA i]

theorem mBcount_perm (π : Equiv.Perm (Fin n)) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) (j : Fin KB) :
    mBcount S (fun k => β (π k)) j = mBcount S β j :=
  card_filter_perm π S.LB hB fun k => β k = j

theorem shapeB_perm (π : Equiv.Perm (Fin n)) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) :
    shapeB S (fun k => β (π k)) = shapeB S β := by
  rw [shapeB, shapeB, funext fun j => mBcount_perm S β π hB j]

theorem shapeA_congr {KA' : ℕ} {α' : Fin n → Fin KA'} (h : SamePartA S α α') :
    shapeA S α = shapeA S α' := by
  rw [shapeA_eq_blockSizes, shapeA_eq_blockSizes, (samePartA_iff_partsA S α).mp h]

theorem shapeB_congr {KB' : ℕ} {β' : Fin n → Fin KB'} (h : SamePartB S β β') :
    shapeB S β = shapeB S β' := by
  have hpart : partsB S β = partsB S β' := Finset.image_congr fun k hk => blkB_congr S β h hk
  rw [shapeB_eq_blockSizes, shapeB_eq_blockSizes, hpart]

theorem fibreCard_eq_count {ι : Type*} [DecidableEq ι] (g : Fin KA → ι) (m : ι) :
    fibreCard g m = Multiset.count m (Multiset.map g Finset.univ.val) := by
  have h1 : (Finset.univ.filter fun a => g a = m) = (Finset.univ.filter fun a => m = g a) :=
    Finset.filter_congr fun a _ => eq_comm
  rw [Multiset.count_map, fibreCard, h1]
  rfl

theorem count_shapeA {m : ℕ} (hm : 0 < m) :
    Multiset.count m (shapeA S α) = fibreCard (mAcount S α) m := by
  rw [shapeA, Multiset.count_filter, ite_eq_left hm, ← fibreCard_eq_count]

theorem count_shapeB {m : ℕ} (hm : 0 < m) :
    Multiset.count m (shapeB S β) = fibreCard (mBcount S β) m := by
  rw [shapeB, Multiset.count_filter, ite_eq_left hm, ← fibreCard_eq_count]

theorem card_shapeA_add : fibreCard (mAcount S α) 0 + Multiset.card (shapeA S α) = KA := by
  have hsplit : Multiset.filter (fun x : ℕ => ¬ 0 < x) (Multiset.map (mAcount S α) univ.val)
      = Multiset.filter (fun x : ℕ => 0 = x) (Multiset.map (mAcount S α) univ.val) :=
    Multiset.filter_congr fun x _ => by omega
  have hzero : Multiset.card (Multiset.filter (fun x : ℕ => ¬ 0 < x)
      (Multiset.map (mAcount S α) univ.val)) = fibreCard (mAcount S α) 0 := by
    rw [hsplit, fibreCard_eq_count, Multiset.count_eq_card_filter_eq]
  have htot : Multiset.card (Multiset.map (mAcount S α) (univ : Finset (Fin KA)).val) = KA := by
    rw [Multiset.card_map]
    simp
  have hsum : Multiset.card (Multiset.filter (fun x : ℕ => 0 < x)
        (Multiset.map (mAcount S α) univ.val))
      + Multiset.card (Multiset.filter (fun x : ℕ => ¬ 0 < x)
        (Multiset.map (mAcount S α) univ.val))
      = Multiset.card (Multiset.map (mAcount S α) (univ : Finset (Fin KA)).val) := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  rw [← hzero, shapeA]
  omega

theorem card_shapeB_add : fibreCard (mBcount S β) 0 + Multiset.card (shapeB S β) = KB := by
  have hsplit : Multiset.filter (fun x : ℕ => ¬ 0 < x) (Multiset.map (mBcount S β) univ.val)
      = Multiset.filter (fun x : ℕ => 0 = x) (Multiset.map (mBcount S β) univ.val) :=
    Multiset.filter_congr fun x _ => by omega
  have hzero : Multiset.card (Multiset.filter (fun x : ℕ => ¬ 0 < x)
      (Multiset.map (mBcount S β) univ.val)) = fibreCard (mBcount S β) 0 := by
    rw [hsplit, fibreCard_eq_count, Multiset.count_eq_card_filter_eq]
  have htot : Multiset.card (Multiset.map (mBcount S β) (univ : Finset (Fin KB)).val) = KB := by
    rw [Multiset.card_map]
    simp
  have hsum : Multiset.card (Multiset.filter (fun x : ℕ => 0 < x)
        (Multiset.map (mBcount S β) univ.val))
      + Multiset.card (Multiset.filter (fun x : ℕ => ¬ 0 < x)
        (Multiset.map (mBcount S β) univ.val))
      = Multiset.card (Multiset.map (mBcount S β) (univ : Finset (Fin KB)).val) := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  rw [← hzero, shapeB]
  omega

theorem fibreCard_mAcount_congr {α' : Fin n → Fin KA} (h : shapeA S α = shapeA S α') (m : ℕ) :
    fibreCard (mAcount S α) m = fibreCard (mAcount S α') m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 := card_shapeA_add S α
    have h2 := card_shapeA_add S α'
    rw [h] at h1
    omega
  · rw [← count_shapeA S α hm, ← count_shapeA S α' hm, h]

theorem fibreCard_mBcount_congr {β' : Fin n → Fin KB} (h : shapeB S β = shapeB S β') (m : ℕ) :
    fibreCard (mBcount S β) m = fibreCard (mBcount S β') m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 := card_shapeB_add S β
    have h2 := card_shapeB_add S β'
    rw [h] at h1
    omega
  · rw [← count_shapeB S β hm, ← count_shapeB S β' hm, h]

theorem exists_perm_of_shapeA_eq (hfull : S.LA = Finset.univ) {α α' : Fin n → Fin n}
    (h : shapeA S α = shapeA S α') :
    ∃ π : Equiv.Perm (Fin n), SamePartA S (fun k => α (π k)) α' := by
  have hmc : ∀ γ : Fin n → Fin n, mAcount S γ = fibreCard γ := by
    intro γ; funext i; rw [mAcount, fibreCard, hfull]
  obtain ⟨σ, hσ⟩ := exists_perm_of_fibreCard_eq (f := mAcount S α') (f₀ := mAcount S α)
    fun m => (fibreCard_mAcount_congr S α h m).symm
  have h2 : ∀ i, fibreCard α' i = fibreCard (fun k => σ.symm (α k)) i := by
    intro i
    have e1 : fibreCard (fun k => σ.symm (α k)) i = fibreCard α (σ i) :=
      congrArg Finset.card (Finset.filter_congr fun k _ => Equiv.symm_apply_eq σ)
    have hs : mAcount S α (σ i) = mAcount S α' i := congrFun hσ i
    rw [e1, ← hmc α, ← hmc α']
    exact hs.symm
  obtain ⟨π, hπ⟩ := exists_perm_of_fibreCard_eq h2
  refine ⟨π, fun k _ k' _ => ?_⟩
  have e : ∀ m, α' m = σ.symm (α (π m)) := fun m => (congrFun hπ m).symm
  rw [e k, e k']
  exact ⟨fun hh => congrArg (fun x => σ.symm x) hh, fun hh => σ.symm.injective hh⟩

theorem exists_perm_of_shapeB_eq (hfull : S.LB = Finset.univ) {β β' : Fin n → Fin n}
    (h : shapeB S β = shapeB S β') :
    ∃ π : Equiv.Perm (Fin n), SamePartB S (fun k => β (π k)) β' := by
  have hmc : ∀ γ : Fin n → Fin n, mBcount S γ = fibreCard γ := by
    intro γ; funext j; rw [mBcount, fibreCard, hfull]
  obtain ⟨σ, hσ⟩ := exists_perm_of_fibreCard_eq (f := mBcount S β') (f₀ := mBcount S β)
    fun m => (fibreCard_mBcount_congr S β h m).symm
  have h2 : ∀ j, fibreCard β' j = fibreCard (fun k => σ.symm (β k)) j := by
    intro j
    have e1 : fibreCard (fun k => σ.symm (β k)) j = fibreCard β (σ j) :=
      congrArg Finset.card (Finset.filter_congr fun k _ => Equiv.symm_apply_eq σ)
    have hs : mBcount S β (σ j) = mBcount S β' j := congrFun hσ j
    rw [e1, ← hmc β, ← hmc β']
    exact hs.symm
  obtain ⟨π, hπ⟩ := exists_perm_of_fibreCard_eq h2
  refine ⟨π, fun k _ k' _ => ?_⟩
  have e : ∀ m, β' m = σ.symm (β (π m)) := fun m => (congrFun hπ m).symm
  rw [e k, e k']
  exact ⟨fun hh => congrArg (fun x => σ.symm x) hh, fun hh => σ.symm.injective hh⟩

end Rhone.Probability.InfiniteAlleles
