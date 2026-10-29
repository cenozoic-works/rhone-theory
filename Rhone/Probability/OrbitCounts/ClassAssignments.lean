/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.OrbitCounts.Aut
public import Rhone.Probability.OrbitCounts.Orbit

/-! # The labelled pairs in a class, and `M(c)/|Aut(c)|` -/

@[expose] public section

namespace Rhone.Probability.OrbitCounts

open Finset LinearAlgebra.Recursion InfiniteAlleles

attribute [local instance] instDecidableEqConfig

variable {n KA KB : ℕ}

def assign (S : Sample n) (ξ : Config KA KB) :
    Finset ((Fin n → Fin KA) × (Fin n → Fin KB)) :=
  Finset.univ.filter fun p => cfgOf S p.1 p.2 = ξ

def classAssign (S : Sample n) (ξ : Config KA KB) :
    Finset ((Fin n → Fin KA) × (Fin n → Fin KB)) :=
  Finset.univ.filter fun p => cfgOf S p.1 p.2 ∈ relabelOrbit ξ

def classPairs (S : Sample n) (ξ : Config KA KB) :
    Finset ((Fin n → Fin n) × (Fin n → Fin n)) :=
  (classAssign S ξ).image fun p => (repA S p.1, repB S p.2)

theorem mem_assign {S : Sample n} {ξ : Config KA KB}
    {p : (Fin n → Fin KA) × (Fin n → Fin KB)} :
    p ∈ assign S ξ ↔ cfgOf S p.1 p.2 = ξ := by
  rw [assign, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_classAssign {S : Sample n} {ξ : Config KA KB}
    {p : (Fin n → Fin KA) × (Fin n → Fin KB)} :
    p ∈ classAssign S ξ ↔ cfgOf S p.1 p.2 ∈ relabelOrbit ξ := by
  rw [classAssign, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem relabel_mem_relabelOrbit {ξ η : Config KA KB} (hη : η ∈ relabelOrbit ξ)
    (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) :
    relabel σ τ η ∈ relabelOrbit ξ := by
  obtain ⟨σ₀, τ₀, rfl⟩ := mem_relabelOrbit.mp hη
  exact mem_relabelOrbit.mpr ⟨σ₀ * σ, τ₀ * τ, (relabel_relabel σ₀ σ τ₀ τ ξ).symm⟩

theorem card_assign_relabel (S : Sample n) (ξ : Config KA KB) (σ : Equiv.Perm (Fin KA))
    (τ : Equiv.Perm (Fin KB)) :
    (assign S (relabel σ τ ξ)).card = (assign S ξ).card := by
  refine Finset.card_bij (fun p _ => (fun k => σ (p.1 k), fun k => τ (p.2 k))) ?_ ?_ ?_
  · intro p hp
    refine mem_assign.mpr ?_
    have e1 : σ * σ.symm = 1 := Equiv.ext fun x => by simp
    have e2 : τ * τ.symm = 1 := Equiv.ext fun x => by simp
    rw [cfgOf_relabel S p.1 p.2 σ τ, mem_assign.mp hp, relabel_relabel σ σ.symm τ τ.symm ξ,
      e1, e2, relabel_one]
  · intro p _ p' _ heq
    have h1 : (fun k => σ (p.1 k)) = fun k => σ (p'.1 k) := congrArg Prod.fst heq
    have h2 : (fun k => τ (p.2 k)) = fun k => τ (p'.2 k) := congrArg Prod.snd heq
    refine Prod.ext (funext fun k => σ.injective (congrFun h1 k))
      (funext fun k => τ.injective (congrFun h2 k))
  · intro q hq
    refine ⟨(fun k => σ.symm (q.1 k), fun k => τ.symm (q.2 k)), mem_assign.mpr ?_, ?_⟩
    · rw [cfgOf_relabel S q.1 q.2 σ.symm τ.symm, mem_assign.mp hq, Equiv.symm_symm,
        Equiv.symm_symm]
    · exact Prod.ext (funext fun k => σ.apply_symm_apply _) (funext fun k => τ.apply_symm_apply _)

theorem card_classAssign (S : Sample n) (ξ : Config KA KB) :
    (classAssign S ξ).card = (relabelOrbit ξ).card * (assign S ξ).card := by
  classical
  have hmaps : ∀ p ∈ classAssign S ξ, cfgOf S p.1 p.2 ∈ relabelOrbit ξ :=
    fun _ hp => mem_classAssign.mp hp
  have hfib : ∀ η ∈ relabelOrbit ξ,
      ((classAssign S ξ).filter fun p => cfgOf S p.1 p.2 = η).card = (assign S ξ).card := by
    intro η hη
    obtain ⟨σ, τ, rfl⟩ := mem_relabelOrbit.mp hη
    have hset : ((classAssign S ξ).filter fun p => cfgOf S p.1 p.2 = relabel σ τ ξ)
        = assign S (relabel σ τ ξ) := by
      ext p
      rw [Finset.mem_filter, mem_assign]
      exact ⟨fun h => h.2, fun h => ⟨mem_classAssign.mpr (by
        rw [h]; exact mem_relabelOrbit.mpr ⟨σ, τ, rfl⟩), h⟩⟩
    rw [hset, card_assign_relabel S ξ σ τ]
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
    smul_eq_mul]

section Full

variable (S : Sample n) (hfullA : S.LA = Finset.univ) (hfullB : S.LB = Finset.univ)

include hfullA hfullB in
theorem both_eq_univ : S.both = Finset.univ := by
  rw [Sample.both, hfullA, hfullB, Finset.inter_self]

include hfullA hfullB in
theorem onlyA_eq_empty : S.onlyA = (∅ : Finset (Fin n)) := by
  rw [Sample.onlyA, hfullA, hfullB, Finset.sdiff_self]

include hfullA hfullB in
theorem onlyB_eq_empty : S.onlyB = (∅ : Finset (Fin n)) := by
  rw [Sample.onlyB, hfullA, hfullB, Finset.sdiff_self]

include hfullA hfullB in
theorem cfgOf_a_eq_zero (α : Fin n → Fin KA) (β : Fin n → Fin KB) (i : Fin KA) :
    (cfgOf S α β).a i = 0 := by
  rw [cfgOf_a, onlyA_eq_empty S hfullA hfullB, Finset.filter_empty, Finset.card_empty]

include hfullA hfullB in
theorem cfgOf_b_eq_zero (α : Fin n → Fin KA) (β : Fin n → Fin KB) (j : Fin KB) :
    (cfgOf S α β).b j = 0 := by
  rw [cfgOf_b, onlyB_eq_empty S hfullA hfullB, Finset.filter_empty, Finset.card_empty]

include hfullA hfullB in
theorem card_assign_mul_prod (ξ : Config KA KB)
    {p₀ : (Fin n → Fin KA) × (Fin n → Fin KB)} (hp₀ : p₀ ∈ assign S ξ) :
    (assign S ξ).card * ∏ i, ∏ j, Nat.factorial (ξ.c i j) = Nat.factorial n := by
  classical
  have hcfg : cfgOf S p₀.1 p₀.2 = ξ := mem_assign.mp hp₀
  have hboth : S.both = Finset.univ := both_eq_univ S hfullA hfullB
  have hmem : ∀ k : Fin n, k ∈ S.both := fun k => by rw [hboth]; exact Finset.mem_univ k
  have hfc : ∀ (γ : Fin n → Fin KA) (δ : Fin n → Fin KB) (i : Fin KA) (j : Fin KB),
      (cfgOf S γ δ).c i j = fibreCard (resC S γ δ) (i, j) := fun γ δ i j =>
    (fibreCard_resC S γ δ (i, j)).symm
  have hcard : (assign S ξ).card = (sameFibres (resC S p₀.1 p₀.2)).card := by
    refine Finset.card_bij (fun p _ => resC S p.1 p.2) ?_ ?_ ?_
    · intro p hp
      refine (mem_sameFibres_resC S p₀.1 p₀.2).mpr fun q => ?_
      rw [fibreCard_resC S p.1 p.2 q, mem_assign.mp hp, hcfg]
    · intro p _ p' _ heq
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact congrArg Prod.fst (congrFun heq ⟨k, hmem k⟩)
      · exact congrArg Prod.snd (congrFun heq ⟨k, hmem k⟩)
    · intro g hg
      have hgc := (mem_sameFibres_resC S p₀.1 p₀.2).mp hg
      have hres : resC S (fun k => (g ⟨k, hmem k⟩).1) (fun k => (g ⟨k, hmem k⟩).2) = g :=
        funext fun x => congrArg g (Subtype.ext rfl)
      refine ⟨(fun k => (g ⟨k, hmem k⟩).1, fun k => (g ⟨k, hmem k⟩).2), mem_assign.mpr ?_, hres⟩
      refine Config.ext (funext fun i => ?_) (funext fun j => ?_)
        (funext fun i => funext fun j => ?_)
      · rw [cfgOf_a_eq_zero S hfullA hfullB, ← hcfg, cfgOf_a_eq_zero S hfullA hfullB]
      · rw [cfgOf_b_eq_zero S hfullA hfullB, ← hcfg, cfgOf_b_eq_zero S hfullA hfullB]
      · rw [hfc, hres, hgc (i, j), hcfg]
  have hmul := card_assignC_mul S p₀.1 p₀.2
  rw [hcfg] at hmul
  have ht : ξ.t = n := by
    rw [← hcfg, t_cfgOf, hboth, Finset.card_univ, Fintype.card_fin]
  rw [hcard, hmul, ht]

end Full

section Pairs

variable (S : Sample n) (hfullA : S.LA = Finset.univ) (hfullB : S.LB = Finset.univ)

theorem surjective_of_mem_classAssign (ξ : Config KA KB) (hrow : ∀ i, 0 < ξ.cRow i)
    {p : (Fin n → Fin KA) × (Fin n → Fin KB)} (hp : p ∈ classAssign S ξ) (i : Fin KA) :
    ∃ k, p.1 k = i := by
  obtain ⟨σ, τ, hστ⟩ := mem_relabelOrbit.mp (mem_classAssign.mp hp)
  have hpos : 0 < (cfgOf S p.1 p.2).cRow i := by
    rw [← hστ, cRow_relabel]
    exact hrow (σ i)
  rw [cRow_cfgOf] at hpos
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

theorem surjective_of_mem_classAssign' (ξ : Config KA KB) (hcol : ∀ j, 0 < ξ.cCol j)
    {p : (Fin n → Fin KA) × (Fin n → Fin KB)} (hp : p ∈ classAssign S ξ) (j : Fin KB) :
    ∃ k, p.2 k = j := by
  obtain ⟨σ, τ, hστ⟩ := mem_relabelOrbit.mp (mem_classAssign.mp hp)
  have hpos : 0 < (cfgOf S p.1 p.2).cCol j := by
    rw [← hστ, cCol_relabel]
    exact hcol (τ j)
  rw [cCol_cfgOf] at hpos
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

include hfullA hfullB in
theorem card_fibre_classPairs (ξ : Config KA KB) (hrow : ∀ i, 0 < ξ.cRow i)
    (hcol : ∀ j, 0 < ξ.cCol j) {q : (Fin n → Fin n) × (Fin n → Fin n)}
    (hq : q ∈ classPairs S ξ) :
    ((classAssign S ξ).filter fun p => (repA S p.1, repB S p.2) = q).card
      = Nat.factorial KA * Nat.factorial KB := by
  classical
  obtain ⟨p₁, hp₁, hq₁⟩ := Finset.mem_image.mp hq
  have hall : ∀ k : Fin n, k ∈ S.LA := fun k => by rw [hfullA]; exact Finset.mem_univ k
  have hallB : ∀ k : Fin n, k ∈ S.LB := fun k => by rw [hfullB]; exact Finset.mem_univ k
  have hs1 : ∀ i, ∃ k, p₁.1 k = i := surjective_of_mem_classAssign S ξ hrow hp₁
  have hs2 : ∀ j, ∃ k, p₁.2 k = j := surjective_of_mem_classAssign' S ξ hcol hp₁
  have hcount : (Finset.univ : Finset (Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB))).card
      = Nat.factorial KA * Nat.factorial KB := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  rw [← hcount]
  refine (Finset.card_bij
    (fun r _ => ((fun k => r.1 (p₁.1 k) : Fin n → Fin KA), (fun k => r.2 (p₁.2 k)))) ?_ ?_ ?_).symm
  · intro r _
    have hA : repA S (fun k => r.1 (p₁.1 k)) = repA S p₁.1 :=
      funext fun k => repA_congr S _ (fun _ _ _ _ =>
        ⟨fun hh => r.1.injective hh, fun hh => congrArg r.1 hh⟩) (hall k)
    have hB : repB S (fun k => r.2 (p₁.2 k)) = repB S p₁.2 :=
      funext fun k => repB_congr S _ (fun _ _ _ _ =>
        ⟨fun hh => r.2.injective hh, fun hh => congrArg r.2 hh⟩) (hallB k)
    refine Finset.mem_filter.mpr ⟨mem_classAssign.mpr ?_, ?_⟩
    · rw [cfgOf_relabel S p₁.1 p₁.2 r.1 r.2]
      exact relabel_mem_relabelOrbit (mem_classAssign.mp hp₁) _ _
    · rw [hA, hB, hq₁]
  · intro r _ r' _ heq
    have h1 : (fun k => r.1 (p₁.1 k)) = fun k => r'.1 (p₁.1 k) := congrArg Prod.fst heq
    have h2 : (fun k => r.2 (p₁.2 k)) = fun k => r'.2 (p₁.2 k) := congrArg Prod.snd heq
    refine Prod.ext (Equiv.ext fun i => ?_) (Equiv.ext fun j => ?_)
    · obtain ⟨k, hk⟩ := hs1 i
      rw [← hk]
      exact congrFun h1 k
    · obtain ⟨k, hk⟩ := hs2 j
      rw [← hk]
      exact congrFun h2 k
  · intro p hp
    obtain ⟨hpc, hpq⟩ := Finset.mem_filter.mp hp
    have hsp1 : ∀ i, ∃ k, p.1 k = i := surjective_of_mem_classAssign S ξ hrow hpc
    have hsp2 : ∀ j, ∃ k, p.2 k = j := surjective_of_mem_classAssign' S ξ hcol hpc
    have hpair : (repA S p₁.1, repB S p₁.2) = (repA S p.1, repB S p.2) := hq₁.trans hpq.symm
    have hrepA : repA S p₁.1 = repA S p.1 := congrArg Prod.fst hpair
    have hrepB : repB S p₁.2 = repB S p.2 := congrArg Prod.snd hpair
    obtain ⟨σ, hσ⟩ := exists_perm_of_samePartA S hfullA hs1 hsp1
      (samePartA_of_repA_eq S hrepA)
    obtain ⟨τ, hτ⟩ := exists_perm_of_samePartB S hfullB hs2 hsp2
      (samePartB_of_repB_eq S hrepB)
    exact ⟨(σ, τ), Finset.mem_univ _,
      Prod.ext (funext fun k => (hσ k).symm) (funext fun k => (hτ k).symm)⟩

include hfullA hfullB in
theorem card_classPairs_mul (ξ : Config KA KB) (hrow : ∀ i, 0 < ξ.cRow i)
    (hcol : ∀ j, 0 < ξ.cCol j) :
    (classPairs S ξ).card * (Nat.factorial KA * Nat.factorial KB)
      = (classAssign S ξ).card := by
  classical
  have hmaps : ∀ p ∈ classAssign S ξ, (repA S p.1, repB S p.2) ∈ classPairs S ξ :=
    fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl fun q hq => card_fibre_classPairs S hfullA hfullB ξ hrow hcol hq,
    Finset.sum_const, smul_eq_mul]

include hfullA hfullB in
theorem card_classPairs_mul_card_aut (ξ : Config KA KB) (hrow : ∀ i, 0 < ξ.cRow i)
    (hcol : ∀ j, 0 < ξ.cCol j) {p₀ : (Fin n → Fin KA) × (Fin n → Fin KB)}
    (hp₀ : p₀ ∈ assign S ξ) :
    (classPairs S ξ).card * (aut ξ).card * ∏ i, ∏ j, Nat.factorial (ξ.c i j)
      = Nat.factorial n := by
  have horb : 0 < (relabelOrbit ξ).card :=
    Finset.card_pos.mpr ⟨ξ, self_mem_relabelOrbit ξ⟩
  have h1 : (classPairs S ξ).card * ((relabelOrbit ξ).card * (aut ξ).card)
      = (relabelOrbit ξ).card * (assign S ξ).card := by
    rw [card_relabelOrbit_mul_card_aut ξ,
      card_classPairs_mul S hfullA hfullB ξ hrow hcol, card_classAssign S ξ]
  have h2 : (relabelOrbit ξ).card * ((classPairs S ξ).card * (aut ξ).card)
      = (relabelOrbit ξ).card * (assign S ξ).card := by
    rw [← h1]; ring
  have h3 : (classPairs S ξ).card * (aut ξ).card = (assign S ξ).card :=
    Nat.eq_of_mul_eq_mul_left horb h2
  rw [h3]
  exact card_assign_mul_prod S hfullA hfullB ξ hp₀

end Pairs

end Rhone.Probability.OrbitCounts
