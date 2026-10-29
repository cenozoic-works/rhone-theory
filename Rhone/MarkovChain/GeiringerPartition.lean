/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerModel

/-!
# Product marginals under the mask fragmentation operation

Source: geiringer1944, eq. (41), p. 43. -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset

theorem atomise_singleton_parts {κ : Type*} [DecidableEq κ]
    (B mask : Finset κ) :
    (Finpartition.atomise B {mask}).parts =
      ({B \ mask, B ∩ mask} : Finset (Finset κ)).erase ∅ := by
  have hpow : ({mask} : Finset (Finset κ)).powerset = {∅, {mask}} := by
    ext Q
    simp only [mem_powerset, subset_singleton_iff, mem_insert, mem_singleton]
  simp [Finpartition.atomise, Finpartition.ofErase, hpow,
    filter_notMem_eq_sdiff, filter_mem_eq_inter]

theorem marginal_empty {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (p : (κ → Ω) → ℝ) (h : κ → Ω)
    (hp : ∑ h, p h = 1) : marginal p ∅ h = 1 := by
  simpa [marginal] using hp

theorem atomise_marginal_product {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (p : (κ → Ω) → ℝ) (B mask : Finset κ)
    (h : κ → Ω) (hp : ∑ h, p h = 1) (hB : B.Nonempty) :
    (∏ C ∈ (Finpartition.atomise B {mask}).parts, marginal p C h) =
      marginal p (B ∩ mask) h*marginal p (B \ mask) h := by
  rw [atomise_singleton_parts,
    prod_erase _ (f := fun C => marginal p C h) (a := ∅) (marginal_empty p h hp)]
  have hne : B \ mask ≠ B ∩ mask := by
    intro heq
    obtain ⟨l, hl⟩ := hB
    by_cases hm : l ∈ mask
    · have := mem_inter.mpr ⟨hl, hm⟩
      rw [← heq] at this
      exact (mem_sdiff.mp this).2 hm
    · have := mem_sdiff.mpr ⟨hl, hm⟩
      rw [heq] at this
      exact hm (mem_inter.mp this).2
  simp [hne, mul_comm]

theorem partition_product_split {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] (p : (κ → Ω) → ℝ)
    (π : Finpartition (Finset.univ : Finset κ)) (masks : π.parts → Finset κ)
    (h : κ → Ω) (hp : ∑ h, p h = 1) :
    partitionProduct p (splitPartition π masks) h =
      ∏ B : π.parts, marginal p (B.val ∩ masks B) h*marginal p (B.val \ masks B) h := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(univ : Finset π.parts))
      (fun B => (Finpartition.atomise B.val {masks B}).parts) := by
    intro B _ D _ hBD
    apply Finset.disjoint_left.mpr
    intro C hC hC'
    have hval : B.val ≠ D.val := fun heq => hBD (Subtype.ext heq)
    have hd := π.disjoint B.property D.property hval
    have hdC : Disjoint C C := hd.mono
      ((Finpartition.atomise B.val {masks B}).le hC)
      ((Finpartition.atomise D.val {masks D}).le hC')
    exact (Finpartition.atomise B.val {masks B}).ne_bot hC (disjoint_self.mp hdC)
  unfold partitionProduct splitPartition
  rw [Finpartition.bind_parts]
  change (∏ C ∈ univ.biUnion (fun B : π.parts =>
    (Finpartition.atomise B.val {masks B}).parts), marginal p C h) = _
  rw [prod_biUnion hdis]
  apply prod_congr rfl
  intro B _
  exact atomise_marginal_product p B.val (masks B) h hp
    (Finset.nonempty_iff_ne_empty.mpr (π.ne_bot B.property))

end Rhone.MarkovChain.Geiringer
