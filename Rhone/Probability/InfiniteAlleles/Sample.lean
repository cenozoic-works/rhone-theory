/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Reduce

/-! # The ordered doubly-typed sample and its configuration -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB K L : ℕ}

structure Sample (n : ℕ) where
  LA : Finset (Fin n)
  LB : Finset (Fin n)

namespace Sample

variable (S : Sample n)

def onlyA : Finset (Fin n) := S.LA \ S.LB

def onlyB : Finset (Fin n) := S.LB \ S.LA

def both : Finset (Fin n) := S.LA ∩ S.LB

theorem onlyA_subset : S.onlyA ⊆ S.LA := Finset.sdiff_subset

theorem onlyB_subset : S.onlyB ⊆ S.LB := Finset.sdiff_subset

theorem both_subset_LA : S.both ⊆ S.LA := Finset.inter_subset_left

theorem both_subset_LB : S.both ⊆ S.LB := Finset.inter_subset_right

theorem onlyA_union_both : S.onlyA ∪ S.both = S.LA := Finset.sdiff_union_inter _ _

theorem onlyB_union_both : S.onlyB ∪ S.both = S.LB := by
  rw [onlyB, both, Finset.inter_comm]
  exact Finset.sdiff_union_inter _ _

theorem disjoint_onlyA_both : Disjoint S.onlyA S.both :=
  Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2

theorem disjoint_onlyB_both : Disjoint S.onlyB S.both :=
  Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1

theorem card_onlyA_add_both : S.onlyA.card + S.both.card = S.LA.card := by
  rw [← Finset.card_union_of_disjoint S.disjoint_onlyA_both, onlyA_union_both]

theorem card_onlyB_add_both : S.onlyB.card + S.both.card = S.LB.card := by
  rw [← Finset.card_union_of_disjoint S.disjoint_onlyB_both, onlyB_union_both]

end Sample

def cfgOf (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB) : Config KA KB where
  a i := (S.onlyA.filter fun k => α k = i).card
  b j := (S.onlyB.filter fun k => β k = j).card
  c i j := (S.both.filter fun k => α k = i ∧ β k = j).card

variable (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB)

@[simp] theorem cfgOf_a (i : Fin KA) :
    (cfgOf S α β).a i = (S.onlyA.filter fun k => α k = i).card := rfl

@[simp] theorem cfgOf_b (j : Fin KB) :
    (cfgOf S α β).b j = (S.onlyB.filter fun k => β k = j).card := rfl

@[simp] theorem cfgOf_c (i : Fin KA) (j : Fin KB) :
    (cfgOf S α β).c i j = (S.both.filter fun k => α k = i ∧ β k = j).card := rfl

theorem sumA_cfgOf : (cfgOf S α β).sumA = S.onlyA.card :=
  (Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_univ (α k)).symm

theorem sumB_cfgOf : (cfgOf S α β).sumB = S.onlyB.card :=
  (Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_univ (β k)).symm

theorem cRow_cfgOf (i : Fin KA) :
    (cfgOf S α β).cRow i = (S.both.filter fun k => α k = i).card := by
  have hf : ∀ j : Fin KB, (S.both.filter fun k => α k = i ∧ β k = j)
      = (S.both.filter fun k => α k = i).filter fun k => β k = j := by
    intro j; rw [Finset.filter_filter]
  change ∑ j, (S.both.filter fun k => α k = i ∧ β k = j).card = _
  rw [Finset.sum_congr rfl fun j _ => by rw [hf j]]
  exact (Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_univ (β k)).symm

theorem cCol_cfgOf (j : Fin KB) :
    (cfgOf S α β).cCol j = (S.both.filter fun k => β k = j).card := by
  have hf : ∀ i : Fin KA, (S.both.filter fun k => α k = i ∧ β k = j)
      = (S.both.filter fun k => β k = j).filter fun k => α k = i := by
    intro i
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun _ _ => and_comm
  change ∑ i, (S.both.filter fun k => α k = i ∧ β k = j).card = _
  rw [Finset.sum_congr rfl fun i _ => by rw [hf i]]
  exact (Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_univ (α k)).symm

theorem t_cfgOf : (cfgOf S α β).t = S.both.card := by
  rw [Config.t_eq_sum_cRow, Finset.sum_congr rfl fun i _ => cRow_cfgOf S α β i]
  exact (Finset.card_eq_sum_card_fiberwise fun k _ => Finset.mem_univ (α k)).symm

theorem mA_cfgOf (i : Fin KA) :
    (cfgOf S α β).mA i = (S.LA.filter fun k => α k = i).card := by
  rw [Config.mA, cfgOf_a, cRow_cfgOf, ← S.onlyA_union_both, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter S.disjoint_onlyA_both)]

theorem mB_cfgOf (j : Fin KB) :
    (cfgOf S α β).mB j = (S.LB.filter fun k => β k = j).card := by
  rw [Config.mB, cfgOf_b, cCol_cfgOf, ← S.onlyB_union_both, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter S.disjoint_onlyB_both)]

theorem nA_cfgOf : (cfgOf S α β).nA = S.LA.card := by
  rw [Config.nA, sumA_cfgOf, t_cfgOf, S.card_onlyA_add_both]

theorem nB_cfgOf : (cfgOf S α β).nB = S.LB.card := by
  rw [Config.nB, sumB_cfgOf, t_cfgOf, S.card_onlyB_add_both]

theorem n_cfgOf : (cfgOf S α β).n = (S.LA ∪ S.LB).card := by
  have h1 := S.card_onlyA_add_both
  have h2 := S.card_onlyB_add_both
  have h3 : (S.LA ∪ S.LB).card + S.both.card = S.LA.card + S.LB.card :=
    Finset.card_union_add_card_inter _ _
  rw [Config.n, sumA_cfgOf, sumB_cfgOf, t_cfgOf]
  omega

theorem cfgOf_congr {α α' : Fin n → Fin KA} {β β' : Fin n → Fin KB}
    (hα : ∀ k ∈ S.LA, α k = α' k) (hβ : ∀ k ∈ S.LB, β k = β' k) :
    cfgOf S α β = cfgOf S α' β' := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · exact congrArg Finset.card
      (Finset.filter_congr fun k hk => by rw [hα k (S.onlyA_subset hk)])
  · exact congrArg Finset.card
      (Finset.filter_congr fun k hk => by rw [hβ k (S.onlyB_subset hk)])
  · exact congrArg Finset.card (Finset.filter_congr fun k hk => by
      rw [hα k (S.both_subset_LA hk), hβ k (S.both_subset_LB hk)])

theorem cfgOf_relabel (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) :
    cfgOf S (fun k => σ (α k)) (fun k => τ (β k))
      = InfiniteAlleles.relabel σ.symm τ.symm (cfgOf S α β) := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · exact congrArg Finset.card (Finset.filter_congr fun k _ => by
      rw [Equiv.eq_symm_apply])
  · exact congrArg Finset.card (Finset.filter_congr fun k _ => by
      rw [Equiv.eq_symm_apply])
  · exact congrArg Finset.card (Finset.filter_congr fun k _ => by
      rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply])

theorem perm_mem_region (π : Equiv.Perm (Fin n))
    (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) :
    (∀ k, k ∈ S.onlyA ↔ π k ∈ S.onlyA) ∧ (∀ k, k ∈ S.onlyB ↔ π k ∈ S.onlyB)
      ∧ ∀ k, k ∈ S.both ↔ π k ∈ S.both := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩ <;>
    simp only [Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff, Finset.mem_inter,
      ← hA k, ← hB k]

theorem card_filter_perm (π : Equiv.Perm (Fin n)) (T : Finset (Fin n))
    (hT : ∀ k, k ∈ T ↔ π k ∈ T) (p : Fin n → Prop) [DecidablePred p] :
    (T.filter fun k => p (π k)).card = (T.filter p).card :=
  Finset.card_equiv π fun k => by
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨(hT k).mp h.1, h.2⟩, fun h => ⟨(hT k).mpr h.1, h.2⟩⟩

theorem cfgOf_perm (π : Equiv.Perm (Fin n))
    (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) :
    cfgOf S (fun k => α (π k)) (fun k => β (π k)) = cfgOf S α β := by
  obtain ⟨h1, h2, h3⟩ := perm_mem_region S π hA hB
  exact Config.ext (funext fun i => card_filter_perm π _ h1 fun k => α k = i)
    (funext fun j => card_filter_perm π _ h2 fun k => β k = j)
    (funext fun i => funext fun j => card_filter_perm π _ h3 fun k => α k = i ∧ β k = j)

theorem push_cfgOf (e : Fin KA ↪ Fin K) (f : Fin KB ↪ Fin L) :
    push e f (cfgOf S α β) = cfgOf S (fun k => e (α k)) (fun k => f (β k)) := by
  have hemptyA : ∀ i' : Fin K, (∀ i, e i ≠ i') →
      (S.onlyA.filter fun k => e (α k) = i').card = 0 := by
    intro i' hi'
    rw [Finset.filter_eq_empty_iff.mpr fun k _ => hi' (α k), Finset.card_empty]
  have hemptyB : ∀ j' : Fin L, (∀ j, f j ≠ j') →
      (S.onlyB.filter fun k => f (β k) = j').card = 0 := by
    intro j' hj'
    rw [Finset.filter_eq_empty_iff.mpr fun k _ => hj' (β k), Finset.card_empty]
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_) (funext fun i' => funext fun j' =>
    ?_)
  · by_cases hi' : ∀ i, e i ≠ i'
    · rw [push_a_off e f _ hi']
      exact (hemptyA i' hi').symm
    · obtain ⟨i, rfl⟩ : ∃ i, e i = i' := by
        by_contra hc; exact hi' fun i hi => hc ⟨i, hi⟩
      rw [push_a, cfgOf_a, cfgOf_a]
      exact congrArg Finset.card (Finset.filter_congr fun k _ => by
        simp [e.apply_eq_iff_eq])
  · by_cases hj' : ∀ j, f j ≠ j'
    · rw [push_b_off e f _ hj']
      exact (hemptyB j' hj').symm
    · obtain ⟨j, rfl⟩ : ∃ j, f j = j' := by
        by_contra hc; exact hj' fun j hj => hc ⟨j, hj⟩
      rw [push_b, cfgOf_b, cfgOf_b]
      exact congrArg Finset.card (Finset.filter_congr fun k _ => by
        simp [f.apply_eq_iff_eq])
  · by_cases hi' : ∀ i, e i ≠ i'
    · rw [push_c_off_left e f _ hi']
      refine (?_ : (cfgOf S (fun k => e (α k)) fun k => f (β k)).c i' j' = 0).symm
      rw [cfgOf_c, Finset.filter_eq_empty_iff.mpr fun k _ hk => hi' (α k) hk.1,
        Finset.card_empty]
    · obtain ⟨i, rfl⟩ : ∃ i, e i = i' := by
        by_contra hc; exact hi' fun i hi => hc ⟨i, hi⟩
      by_cases hj' : ∀ j, f j ≠ j'
      · rw [push_c_off_right e f _ (e i) hj']
        refine (?_ : (cfgOf S (fun k => e (α k)) fun k => f (β k)).c (e i) j' = 0).symm
        rw [cfgOf_c, Finset.filter_eq_empty_iff.mpr fun k _ hk => hj' (β k) hk.2,
          Finset.card_empty]
      · obtain ⟨j, rfl⟩ : ∃ j, f j = j' := by
          by_contra hc; exact hj' fun j hj => hc ⟨j, hj⟩
        rw [push_c, cfgOf_c, cfgOf_c]
        exact congrArg Finset.card (Finset.filter_congr fun k _ => by
          simp [e.apply_eq_iff_eq, f.apply_eq_iff_eq])

end Rhone.Probability.InfiniteAlleles
