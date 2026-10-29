/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.ChineseRestaurant

/-! # Exchangeable random partitions of a finite set -/

@[expose] public section

namespace Rhone.Probability

open Finset

variable {n : ℕ}

def permuteFamily (σ : Equiv.Perm (Fin n)) (ζ : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  ζ.image (Finset.map σ.toEmbedding)

theorem isSetPartition_permuteFamily (σ : Equiv.Perm (Fin n)) {ζ : Finset (Finset (Fin n))}
    (hζ : Combinatorics.IsSetPartition (Finset.univ : Finset (Fin n)) ζ) :
    Combinatorics.IsSetPartition (Finset.univ : Finset (Fin n)) (permuteFamily σ ζ) := by
  refine ⟨?_, fun B _ => subset_univ B, ?_, ?_⟩
  · intro h
    obtain ⟨B, hB, hBe⟩ := mem_image.1 h
    have : B = ∅ := by simpa using hBe
    exact hζ.1 (this ▸ hB)
  · intro B hB C hC hne
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    obtain ⟨C', hC', rfl⟩ := mem_image.1 hC
    have : B' ≠ C' := fun h => hne (h ▸ rfl)
    exact (Finset.disjoint_map _).2 (hζ.2.2.1 B' hB' C' hC' this)
  · intro x _
    obtain ⟨B, hB, hxB⟩ := hζ.2.2.2 (σ.symm x) (mem_univ _)
    exact ⟨B.map σ.toEmbedding, mem_image_of_mem _ hB, by simpa using hxB⟩

def permutePartition (σ : Equiv.Perm (Fin n))
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  Combinatorics.finpartitionOfSetPartition
      (isSetPartition_permuteFamily σ (Combinatorics.isSetPartition_parts P))

theorem parts_permutePartition (σ : Equiv.Perm (Fin n))
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (permutePartition σ P).parts = P.parts.image (Finset.map σ.toEmbedding) := rfl

def IsExchangeable (μ : PMF (Finpartition (Finset.univ : Finset (Fin n)))) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (P : Finpartition (Finset.univ : Finset (Fin n))),
    μ (permutePartition σ P) = μ P

theorem crpPartition_isExchangeable {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    IsExchangeable (crpPartition hθ N) := by
  intro σ P
  rw [crpPartition_apply, crpPartition_apply, parts_permutePartition]
  have hinj : Function.Injective (Finset.map σ.toEmbedding) := Finset.map_injective _
  rw [card_image_of_injective _ hinj, prod_image (fun B _ C _ h => hinj h)]
  simp only [card_map]

def blockSizes (P : Finpartition (Finset.univ : Finset (Fin n))) : Multiset ℕ :=
  P.parts.val.map Finset.card

theorem blockSizes_permutePartition (σ : Equiv.Perm (Fin n))
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    blockSizes (permutePartition σ P) = blockSizes P := by
  have hinj : Function.Injective (Finset.map σ.toEmbedding) := Finset.map_injective _
  rw [blockSizes, parts_permutePartition, Finset.image_val_of_injOn hinj.injOn,
    Multiset.map_map, blockSizes]
  exact Multiset.map_congr rfl fun B _ => by simp

private theorem exists_equiv_card_eq {s t : Finset (Finset (Fin n))}
    (h : s.val.map Finset.card = t.val.map Finset.card) :
    ∃ e : s ≃ t, ∀ B : s, (e B).1.card = B.1.card := by
  have key : ∀ (u : Finset (Finset (Fin n))) (c : ℕ),
      Fintype.card {B : u // B.1.card = c} = Multiset.count c (u.val.map Finset.card) := by
    intro u c
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun B : Finset (Fin n) => B ∈ u) (fun B => B.card = c)),
      Fintype.card_of_subtype (u.filter fun B => B.card = c)
        (fun B => by simp [Finset.mem_filter]),
      Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun a _ => eq_comm
  have hc : ∀ c : ℕ, Fintype.card {B : s // B.1.card = c} =
      Fintype.card {C : t // C.1.card = c} := fun c => by rw [key, key, h]
  exact ⟨Equiv.ofFiberEquiv (f := fun B : s => B.1.card) (g := fun C : t => C.1.card)
    (fun c => Fintype.equivOfCardEq (hc c)), fun B => Equiv.ofFiberEquiv_map
      (f := fun B : s => B.1.card) (g := fun C : t => C.1.card) _ B⟩

theorem exists_perm_of_blockSizes_eq {P Q : Finpartition (Finset.univ : Finset (Fin n))}
    (h : blockSizes P = blockSizes Q) :
    ∃ σ : Equiv.Perm (Fin n), permutePartition σ P = Q := by
  obtain ⟨e, he⟩ := exists_equiv_card_eq (s := P.parts) (t := Q.parts) h
  set τ : (Σ B : P.parts, B.1) ≃ (Σ C : Q.parts, C.1) :=
    Equiv.sigmaCongr e (fun B => Finset.equivOfCardEq (he B).symm) with hτ
  have hτ1 : ∀ y, (τ y).1 = e y.1 := fun y => rfl
  set σ : Equiv.Perm (Fin n) :=
    (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)).symm.trans
      ((P.equivSigmaParts.trans (τ.trans Q.equivSigmaParts.symm)).trans
        (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))) with hσ
  have hmap : ∀ (B : Finset (Fin n)) (hB : B ∈ P.parts),
      B.map σ.toEmbedding = (e ⟨B, hB⟩).1 := by
    intro B hB
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map, he])
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hz
    set y := τ (P.equivSigmaParts ⟨x, Finset.mem_univ x⟩) with hy
    have hy1 : y.1 = e ⟨B, hB⟩ := by
      rw [hy, hτ1]
      congr 1
      exact Subtype.ext (P.part_eq_of_mem hB hx)
    have hy2 : (σ x) = y.2.1 := rfl
    have hmem : ∀ w : Q.parts, y.1 = w → y.2.1 ∈ w.1 := by
      rintro w rfl
      exact y.2.2
    exact hy2 ▸ hmem _ hy1
  refine ⟨σ, Finpartition.ext ?_⟩
  rw [parts_permutePartition]
  ext C
  constructor
  · intro hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
    rw [hmap B hB]
    exact (e ⟨B, hB⟩).2
  · intro hC
    refine Finset.mem_image.2 ⟨(e.symm ⟨C, hC⟩).1, (e.symm ⟨C, hC⟩).2, ?_⟩
    rw [hmap _ (e.symm ⟨C, hC⟩).2]
    simp

theorem isExchangeable_iff_blockSizes
    (μ : PMF (Finpartition (Finset.univ : Finset (Fin n)))) :
    IsExchangeable μ ↔ ∀ P Q, blockSizes P = blockSizes Q → μ P = μ Q := by
  constructor
  · intro hμ P Q h
    obtain ⟨σ, rfl⟩ := exists_perm_of_blockSizes_eq h
    exact (hμ σ P).symm
  · intro h σ P
    exact h _ _ (blockSizes_permutePartition σ P)

theorem isExchangeable_iff_exists_blockSizes
    (μ : PMF (Finpartition (Finset.univ : Finset (Fin n)))) :
    IsExchangeable μ ↔ ∃ p : Multiset ℕ → ENNReal, ∀ P, μ P = p (blockSizes P) := by
  classical
  rw [isExchangeable_iff_blockSizes]
  constructor
  · intro h
    refine ⟨fun m => if hm : ∃ P, blockSizes P = m then μ hm.choose else 0, fun P => ?_⟩
    have hm : ∃ Q, blockSizes Q = blockSizes P := ⟨P, rfl⟩
    beta_reduce
    rw [dite_eq_left hm]
    exact h _ _ hm.choose_spec.symm
  · rintro ⟨p, hp⟩ P Q h
    rw [hp, hp, h]

end Rhone.Probability
