/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Blocks

/-! # Identity-by-descent class equals allelic class for sampling configurations -/

@[expose] public section

namespace Rhone.Probability.OrbitCounts

open Finset LinearAlgebra.Recursion InfiniteAlleles

variable {n E K L : ℕ}

theorem blkA_ibd_subset (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (k : Fin n) : blkA S mrm k ⊆ blkA S (fun m => typ (mrm m)) k := by
  intro k' hk'
  obtain ⟨hk'A, hk'eq⟩ := Finset.mem_filter.mp hk'
  exact Finset.mem_filter.mpr ⟨hk'A, congrArg typ hk'eq⟩

theorem blkB_ibd_subset (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (k : Fin n) : blkB S mrm k ⊆ blkB S (fun m => typ (mrm m)) k := by
  intro k' hk'
  obtain ⟨hk'B, hk'eq⟩ := Finset.mem_filter.mp hk'
  exact Finset.mem_filter.mpr ⟨hk'B, congrArg typ hk'eq⟩

theorem partsA_ibd_le (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    {B : Finset (Fin n)} (hB : B ∈ partsA S mrm) :
    ∃ C ∈ partsA S (fun m => typ (mrm m)), B ⊆ C := by
  obtain ⟨k, hk, rfl⟩ := (mem_partsA S mrm).mp hB
  exact ⟨blkA S (fun m => typ (mrm m)) k, (mem_partsA S _).mpr ⟨k, hk, rfl⟩,
    blkA_ibd_subset S mrm typ k⟩

theorem samePartA_of_injOn (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (hinj : Set.InjOn typ (mrm '' (S.LA : Set (Fin n)))) :
    SamePartA S (fun m => typ (mrm m)) mrm := by
  intro k hk k' hk'
  exact ⟨fun h => hinj ⟨k, Finset.mem_coe.mpr hk, rfl⟩ ⟨k', Finset.mem_coe.mpr hk', rfl⟩ h,
    fun h => congrArg typ h⟩

theorem samePartB_of_injOn (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (hinj : Set.InjOn typ (mrm '' (S.LB : Set (Fin n)))) :
    SamePartB S (fun m => typ (mrm m)) mrm := by
  intro k hk k' hk'
  exact ⟨fun h => hinj ⟨k, Finset.mem_coe.mpr hk, rfl⟩ ⟨k', Finset.mem_coe.mpr hk', rfl⟩ h,
    fun h => congrArg typ h⟩

theorem partsA_eq_of_injOn (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (hinj : Set.InjOn typ (mrm '' (S.LA : Set (Fin n)))) :
    partsA S (fun m => typ (mrm m)) = partsA S mrm :=
  (samePartA_iff_partsA S _).mp (samePartA_of_injOn S mrm typ hinj)

theorem repA_eq_of_injOn (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (hinj : Set.InjOn typ (mrm '' (S.LA : Set (Fin n)))) {k : Fin n} (hk : k ∈ S.LA) :
    repA S (fun m => typ (mrm m)) k = repA S mrm k :=
  repA_congr S _ (samePartA_of_injOn S mrm typ hinj) hk

section Kernel

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem Plab_allelic_eq_ibd (S : Sample n) (mrmA : Fin n → Fin E) (mrmB : Fin n → Fin L)
    (typA : Fin E → Fin K) (typB : Fin L → Fin K) (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hinjA : Set.InjOn typA (mrmA '' (S.LA : Set (Fin n))))
    (hinjB : Set.InjOn typB (mrmB '' (S.LB : Set (Fin n)))) :
    Plab hθA hθB hρ S (fun m => typA (mrmA m)) (fun m => typB (mrmB m))
      = Plab hθA hθB hρ S mrmA mrmB :=
  Plab_congr_part S _ _ hθA hθB hρ (samePartA_of_injOn S mrmA typA hinjA)
    (samePartB_of_injOn S mrmB typB hinjB)

end Kernel

theorem exists_collision_of_card_lt (S : Sample n) (mrm : Fin n → Fin E) (typ : Fin E → Fin K)
    (h : K < (S.LA.image mrm).card) :
    ∃ k ∈ S.LA, ∃ k' ∈ S.LA, typ (mrm k) = typ (mrm k') ∧ mrm k ≠ mrm k' := by
  have hcard : (Finset.univ : Finset (Fin K)).card < (S.LA.image mrm).card := by
    simpa using h
  obtain ⟨e, he, e', he', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun a _ => Finset.mem_univ (typ a))
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp he'
  exact ⟨k, hk, k', hk', heq, hne⟩

theorem exists_not_samePartA :
    ∃ (S : Sample 2) (mrm : Fin 2 → Fin 2) (typ : Fin 2 → Fin 1),
      ¬ SamePartA S (fun m => typ (mrm m)) mrm := by
  refine ⟨⟨Finset.univ, Finset.univ⟩, id, fun _ => 0, fun h => ?_⟩
  have h01 : (0 : Fin 2) = 1 := (h 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)).mp rfl
  exact absurd h01 (by decide)

theorem exists_partsA_ne :
    ∃ (S : Sample 2) (mrm : Fin 2 → Fin 2) (typ : Fin 2 → Fin 1),
      partsA S (fun m => typ (mrm m)) ≠ partsA S mrm := by
  obtain ⟨S, mrm, typ, h⟩ := exists_not_samePartA
  exact ⟨S, mrm, typ, fun hc => h ((samePartA_iff_partsA S _).mpr hc)⟩

end Rhone.Probability.OrbitCounts
