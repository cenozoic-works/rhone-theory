/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.SamplingDefs
public import Rhone.Probability.Multilinear.Basic
public import Rhone.Probability.Denominator.Insert

/-! # The labelled sample of a list of slots -/

@[expose] public section

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear Denominator

variable {KA : ℕ} {F : Type*} [Field F] {n m : ℕ}

def shA (M : Finset (Fin n × Fin m)) : Finset (Fin (n + 1) × Fin m) :=
  M.map ((Fin.succEmb n).prodMap (Function.Embedding.refl _))

def shB (M : Finset (Fin n × Fin m)) : Finset (Fin n × Fin (m + 1)) :=
  M.map ((Function.Embedding.refl _).prodMap (Fin.succEmb m))

def linkAB (M : Finset (Fin n × Fin m)) : Finset (Fin (n + 1) × Fin (m + 1)) :=
  insert (0, 0) (shA (shB M))

theorem mem_shA {M : Finset (Fin n × Fin m)} {p : Fin (n + 1) × Fin m} :
    p ∈ shA M ↔ ∃ u, p.1 = Fin.succ u ∧ (u, p.2) ∈ M := by
  simp only [shA, Finset.mem_map, Function.Embedding.coe_prodMap, Prod.map_apply,
    Fin.coe_succEmb, Function.Embedding.refl_apply, Prod.exists, Prod.ext_iff]
  constructor
  · rintro ⟨u, v, hv, h1, h2⟩
    exact ⟨u, h1.symm, by rw [← h2]; exact hv⟩
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, p.2, h2, h1.symm, rfl⟩

theorem mem_shB {M : Finset (Fin n × Fin m)} {p : Fin n × Fin (m + 1)} :
    p ∈ shB M ↔ ∃ v, p.2 = Fin.succ v ∧ (p.1, v) ∈ M := by
  simp only [shB, Finset.mem_map, Function.Embedding.coe_prodMap, Prod.map_apply,
    Fin.coe_succEmb, Function.Embedding.refl_apply, Prod.exists, Prod.ext_iff]
  constructor
  · rintro ⟨u, v, hv, h1, h2⟩
    exact ⟨v, h2.symm, by rw [← h1]; exact hv⟩
  · rintro ⟨v, h1, h2⟩
    exact ⟨p.1, v, h2, rfl, h1.symm⟩

theorem mem_linkAB {M : Finset (Fin n × Fin m)} {p : Fin (n + 1) × Fin (m + 1)} :
    p ∈ linkAB M ↔ p = (0, 0) ∨ ∃ u v, p = (Fin.succ u, Fin.succ v) ∧ (u, v) ∈ M := by
  rw [linkAB, Finset.mem_insert, mem_shA]
  constructor
  · rintro (h | ⟨u, h1, h2⟩)
    · exact Or.inl h
    · rw [mem_shB] at h2
      obtain ⟨v, h3, h4⟩ := h2
      exact Or.inr ⟨u, v, Prod.ext h1 h3, h4⟩
  · rintro (h | ⟨u, v, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨u, congrArg Prod.fst h1, ?_⟩
      rw [mem_shB]
      exact ⟨v, congrArg Prod.snd h1, h2⟩

theorem isMatching_shA {M : Finset (Fin n × Fin m)} (hM : IsMatching M) :
    IsMatching (shA M) := by
  constructor
  · intro p hp p' hp' h
    obtain ⟨u, hu, hu'⟩ := mem_shA.mp hp
    obtain ⟨u', hu1, hu1'⟩ := mem_shA.mp hp'
    have huu : u = u' := Fin.succ_injective _ (hu.symm.trans (h.trans hu1))
    have e := hM.fst _ hu' _ hu1' huu
    exact Prod.ext h (Prod.mk.inj e).2
  · intro p hp p' hp' h
    obtain ⟨u, hu, hu'⟩ := mem_shA.mp hp
    obtain ⟨u', hu1, hu1'⟩ := mem_shA.mp hp'
    have e := hM.snd _ hu' _ hu1' h
    exact Prod.ext (hu.trans ((congrArg Fin.succ (Prod.mk.inj e).1).trans hu1.symm)) h

theorem isMatching_shB {M : Finset (Fin n × Fin m)} (hM : IsMatching M) :
    IsMatching (shB M) := by
  constructor
  · intro p hp p' hp' h
    obtain ⟨v, hv, hv'⟩ := mem_shB.mp hp
    obtain ⟨v', hv1, hv1'⟩ := mem_shB.mp hp'
    have e := hM.fst _ hv' _ hv1' h
    exact Prod.ext h (hv.trans ((congrArg Fin.succ (Prod.mk.inj e).2).trans hv1.symm))
  · intro p hp p' hp' h
    obtain ⟨v, hv, hv'⟩ := mem_shB.mp hp
    obtain ⟨v', hv1, hv1'⟩ := mem_shB.mp hp'
    have hvv : v = v' := Fin.succ_injective _ (hv.symm.trans (h.trans hv1))
    have e := hM.snd _ hv' _ hv1' hvv
    exact Prod.ext (Prod.mk.inj e).1 h

theorem isMatching_linkAB {M : Finset (Fin n × Fin m)} (hM : IsMatching M) :
    IsMatching (linkAB M) := by
  have hA := isMatching_shA (isMatching_shB hM)
  constructor
  · intro p hp p' hp' h
    rw [linkAB, Finset.mem_insert] at hp hp'
    rcases hp with rfl | hp <;> rcases hp' with rfl | hp'
    · rfl
    · obtain ⟨u, hu, -⟩ := mem_shA.mp hp'
      exact absurd (h.trans hu) (Fin.succ_ne_zero _).symm
    · obtain ⟨u, hu, -⟩ := mem_shA.mp hp
      exact absurd (h.symm.trans hu) (Fin.succ_ne_zero _).symm
    · exact hA.fst p hp p' hp' h
  · intro p hp p' hp' h
    rw [linkAB, Finset.mem_insert] at hp hp'
    rcases hp with rfl | hp <;> rcases hp' with rfl | hp'
    · rfl
    · obtain ⟨u, -, hu⟩ := mem_shA.mp hp'
      obtain ⟨v, hv, -⟩ := mem_shB.mp hu
      exact absurd (h.trans hv) (Fin.succ_ne_zero _).symm
    · obtain ⟨u, -, hu⟩ := mem_shA.mp hp
      obtain ⟨v, hv, -⟩ := mem_shB.mp hu
      exact absurd (h.symm.trans hv) (Fin.succ_ne_zero _).symm
    · exact hA.snd p hp p' hp' h

theorem domA_shA (M : Finset (Fin n × Fin m)) :
    domA (shA M) = (domA M).map (Fin.succEmb n) := by
  ext x
  rw [mem_domA, Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [mem_shA, Fin.coe_succEmb]
    constructor
    · rintro ⟨v, u, h1, -⟩
      exact absurd h1 (Fin.succ_ne_zero _).symm
    · rintro ⟨u, -, h1⟩
      exact absurd h1 (Fin.succ_ne_zero _)
  · simp only [mem_shA, Fin.coe_succEmb, mem_domA, Fin.succ_inj]
    constructor
    · rintro ⟨v, u, h1, h2⟩
      exact ⟨u, ⟨v, h2⟩, h1.symm⟩
    · rintro ⟨u, ⟨v, h2⟩, h1⟩
      exact ⟨v, u, h1.symm, h2⟩

theorem domA_shB (M : Finset (Fin n × Fin m)) : domA (shB M) = domA M := by
  ext x
  rw [mem_domA, mem_domA]
  simp only [mem_shB]
  constructor
  · rintro ⟨v, w, -, h⟩
    exact ⟨w, h⟩
  · rintro ⟨w, h⟩
    exact ⟨w.succ, w, rfl, h⟩

theorem domA_linkAB (M : Finset (Fin n × Fin m)) :
    domA (linkAB M) = insert 0 ((domA M).map (Fin.succEmb n)) := by
  ext x
  rw [mem_domA, Finset.mem_insert, Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [true_or, iff_true]
    exact ⟨0, mem_linkAB.mpr (Or.inl rfl)⟩
  · simp only [Fin.succ_ne_zero, false_or, Fin.coe_succEmb, mem_domA, mem_linkAB,
      Prod.ext_iff, Fin.succ_inj]
    constructor
    · rintro ⟨v, h | ⟨u, w, ⟨h1, h2⟩, h3⟩⟩
      · exact h.1.elim
      · exact ⟨u, ⟨w, h3⟩, h1.symm⟩
    · rintro ⟨u, ⟨w, h3⟩, h1⟩
      exact ⟨w.succ, Or.inr ⟨u, w, ⟨h1.symm, rfl⟩, h3⟩⟩

theorem freeA_shA (M : Finset (Fin n × Fin m)) :
    freeA (shA M) = insert 0 ((freeA M).map (Fin.succEmb n)) := by
  ext x
  rw [Finset.mem_insert, Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [true_or, iff_true, mem_freeA, mem_shA]
    rintro v ⟨u, h, -⟩
    exact Fin.succ_ne_zero _ h.symm
  · simp only [Fin.succ_ne_zero, false_or, Fin.coe_succEmb, mem_freeA, mem_shA, Fin.succ_inj]
    constructor
    · intro h
      exact ⟨y, fun v hv => h v ⟨y, rfl, hv⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩ v ⟨u', h1, h2⟩
      subst h1
      exact hu v h2

theorem freeB_shA (M : Finset (Fin n × Fin m)) : freeB (shA M) = freeB M := by
  ext v
  simp only [mem_freeB, mem_shA]
  constructor
  · intro h u hu
    exact h u.succ ⟨u, rfl, hu⟩
  · rintro h x ⟨u, -, hu⟩
    exact h u hu

theorem freeB_shB (M : Finset (Fin n × Fin m)) :
    freeB (shB M) = insert 0 ((freeB M).map (Fin.succEmb m)) := by
  ext x
  rw [Finset.mem_insert, Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [true_or, iff_true, mem_freeB, mem_shB]
    rintro u ⟨v, h, -⟩
    exact Fin.succ_ne_zero _ h.symm
  · simp only [Fin.succ_ne_zero, false_or, Fin.coe_succEmb, mem_freeB, mem_shB, Fin.succ_inj]
    constructor
    · intro h
      exact ⟨y, fun u hu => h u ⟨y, rfl, hu⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩ u ⟨v', h1, h2⟩
      subst h1
      exact hv u h2

theorem freeA_shB (M : Finset (Fin n × Fin m)) : freeA (shB M) = freeA M := by
  ext u
  simp only [mem_freeA, mem_shB]
  constructor
  · intro h v hv
    exact h v.succ ⟨v, rfl, hv⟩
  · rintro h x ⟨v, -, hv⟩
    exact h v hv

theorem freeA_linkAB (M : Finset (Fin n × Fin m)) :
    freeA (linkAB M) = (freeA M).map (Fin.succEmb n) := by
  ext x
  rw [Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [Fin.coe_succEmb, mem_freeA]
    constructor
    · intro h
      exact absurd (mem_linkAB.mpr (Or.inl rfl)) (h 0)
    · rintro ⟨u, -, h⟩
      exact absurd h (Fin.succ_ne_zero _)
  · simp only [Fin.coe_succEmb, mem_freeA, mem_linkAB, Fin.succ_inj]
    constructor
    · intro h
      refine ⟨y, fun w hw => h w.succ (Or.inr ⟨y, w, rfl, hw⟩), rfl⟩
    · rintro ⟨u, hu, rfl⟩ v h
      rcases h with h | ⟨u', w, h1, h2⟩
      · exact Fin.succ_ne_zero _ (congrArg Prod.fst h)
      · rw [Prod.ext_iff, Fin.succ_inj] at h1
        obtain ⟨h1, -⟩ := h1
        subst h1
        exact hu w h2

theorem freeB_linkAB (M : Finset (Fin n × Fin m)) :
    freeB (linkAB M) = (freeB M).map (Fin.succEmb m) := by
  ext x
  rw [Finset.mem_map]
  refine Fin.cases ?_ (fun y => ?_) x
  · simp only [Fin.coe_succEmb, mem_freeB]
    constructor
    · intro h
      exact absurd (mem_linkAB.mpr (Or.inl rfl)) (h 0)
    · rintro ⟨u, -, h⟩
      exact absurd h (Fin.succ_ne_zero _)
  · simp only [Fin.coe_succEmb, mem_freeB, mem_linkAB, Fin.succ_inj]
    constructor
    · intro h
      refine ⟨y, fun w hw => h w.succ (Or.inr ⟨w, y, rfl, hw⟩), rfl⟩
    · rintro ⟨u, hu, rfl⟩ v h
      rcases h with h | ⟨u', w, h1, h2⟩
      · exact Fin.succ_ne_zero _ (congrArg Prod.snd h)
      · rw [Prod.ext_iff, Fin.succ_inj] at h1
        obtain ⟨-, h1⟩ := h1
        subst h1
        exact hu u' h2

theorem xi_shA (M : Finset (Fin n × Fin m)) (α : Fin n → Fin KA) (β : Fin m → Fin 2)
    (p : Fin KA) :
    xi (shA M) (Fin.cons p α : Fin (n + 1) → Fin KA) β = addA (xi M α β) p := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · have h0 : (0 : Fin (n + 1)) ∉ (freeA M).map (Fin.succEmb n) := by
      simp [Fin.succ_ne_zero]
    rw [xi_a, freeA_shA, card_filter_insert h0, Finset.filter_map, Finset.card_map]
    change _ = incf (xi M α β).a p i
    rw [incf_apply, xi_a]
    simp only [Fin.cons_zero, Function.comp_def, Fin.coe_succEmb, Fin.cons_succ]
    simp only [eq_comm (a := i)]
  · simp only [xi_b, freeB_shA, addA]
  · simp only [xi_c, addA, shA, Finset.filter_map, Finset.card_map]
    congr 1

theorem xi_shB (M : Finset (Fin n × Fin m)) (α : Fin n → Fin KA) (β : Fin m → Fin 2)
    (b : Fin 2) :
    xi (shB M) α (Fin.cons b β : Fin (m + 1) → Fin 2) = addB (xi M α β) b := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · simp only [xi_a, freeA_shB, addB]
  · have h0 : (0 : Fin (m + 1)) ∉ (freeB M).map (Fin.succEmb m) := by
      simp [Fin.succ_ne_zero]
    rw [xi_b, freeB_shB, card_filter_insert h0, Finset.filter_map, Finset.card_map]
    change _ = incf (xi M α β).b b j
    rw [incf_apply, xi_b]
    simp only [Fin.cons_zero, Function.comp_def, Fin.coe_succEmb, Fin.cons_succ]
    simp only [eq_comm (a := j)]
  · simp only [xi_c, addB, shB, Finset.filter_map, Finset.card_map]
    congr 1

theorem xi_linkAB (M : Finset (Fin n × Fin m)) (α : Fin n → Fin KA) (β : Fin m → Fin 2)
    (p : Fin KA) (b : Fin 2) :
    xi (linkAB M) (Fin.cons p α : Fin (n + 1) → Fin KA) (Fin.cons b β : Fin (m + 1) → Fin 2)
      = addC (xi M α β) p b := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · simp only [xi_a, freeA_linkAB, addC, Finset.filter_map, Finset.card_map]
    congr 1
  · simp only [xi_b, freeB_linkAB, addC, Finset.filter_map, Finset.card_map]
    congr 1
  · have h0 : ((0 : Fin (n + 1)), (0 : Fin (m + 1))) ∉ shA (shB M) := by
      intro h
      obtain ⟨u, hu, -⟩ := mem_shA.mp h
      exact Fin.succ_ne_zero _ hu.symm
    change _ = Config.incC (xi M α β).c p b i j
    rw [xi_c, linkAB, card_filter_insert h0, incC_apply]
    have : ((shA (shB M)).filter fun r : Fin (n + 1) × Fin (m + 1) =>
        (Fin.cons p α : Fin (n + 1) → Fin KA) r.1 = i
          ∧ (Fin.cons b β : Fin (m + 1) → Fin 2) r.2 = j).card
        = (M.filter fun r => α r.1 = i ∧ β r.2 = j).card := by
      simp only [shA, shB, Finset.map_map, Finset.filter_map, Finset.card_map]
      congr 1
    rw [this]
    simp only [Fin.cons_zero, xi_c]
    by_cases h1 : p = i <;> by_cases h2 : b = j <;> simp [h1, h2, eq_comm]

def Qc (q : Config KA 2 → F) :
    List (LinearAlgebra.BooleanLatticeInverse.Slot KA) → (n m : ℕ) → Finset (Fin n × Fin m) →
        (Fin n → Fin KA → F) →
      (Fin m → Fin 2 → F) → F
  | [], _, _, M, s, w => Q q M s w
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeA p :: r, n, m, M, s, w =>
    Qc q r (n + 1) m (shA M) (Fin.cons (Pi.single p 1) s : Fin (n + 1) → Fin KA → F) w
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeB b :: r, n, m, M, s, w =>
    Qc q r n (m + 1) (shB M) s (Fin.cons (Pi.single b 1) w : Fin (m + 1) → Fin 2 → F)
  | LinearAlgebra.BooleanLatticeInverse.Slot.pair p b :: r, n, m, M, s, w =>
    Qc q r (n + 1) (m + 1) (linkAB M)
      (Fin.cons (Pi.single p 1) s : Fin (n + 1) → Fin KA → F)
      (Fin.cons (Pi.single b 1) w : Fin (m + 1) → Fin 2 → F)

def addSlot (ξ : Config KA 2) : LinearAlgebra.BooleanLatticeInverse.Slot KA → Config KA 2
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeA p => addA ξ p
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeB b => addB ξ b
  | LinearAlgebra.BooleanLatticeInverse.Slot.pair p b => addC ξ p b

def addSlots (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) (ξ : Config KA 2) : Config KA
    2 := r.foldl addSlot ξ

theorem Qc_basis (q : Config KA 2 → F) (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (M : Finset (Fin n × Fin m))
    (α : Fin n → Fin KA) (β : Fin m → Fin 2) :
    Qc q r n m M (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1)
      = q (addSlots r (xi M α β)) := by
  induction r generalizing n m M α β with
  | nil => exact Q_basis q M α β
  | cons x r ih =>
    have hA : ∀ (n : ℕ) (α : Fin n → Fin KA) (p : Fin KA),
        (Fin.cons (Pi.single p 1) (fun u => Pi.single (α u) 1) : Fin (n + 1) → Fin KA → F)
          = fun u => Pi.single ((Fin.cons p α : Fin (n + 1) → Fin KA) u) 1 := by
      intro n α p
      funext u
      refine Fin.cases ?_ (fun y => ?_) u <;> simp
    have hB : ∀ (m : ℕ) (β : Fin m → Fin 2) (b : Fin 2),
        (Fin.cons (Pi.single b 1) (fun v => Pi.single (β v) 1) : Fin (m + 1) → Fin 2 → F)
          = fun v => Pi.single ((Fin.cons b β : Fin (m + 1) → Fin 2) v) 1 := by
      intro m β b
      funext v
      refine Fin.cases ?_ (fun y => ?_) v <;> simp
    cases x with
    | freeA p =>
      simp only [Qc]
      rw [hA, ih, xi_shA]
      rfl
    | freeB b =>
      simp only [Qc]
      rw [hB, ih, xi_shB]
      rfl
    | pair p b =>
      simp only [Qc]
      rw [hA, hB, ih, xi_linkAB]
      rfl

private def cntA (i : Fin KA) : LinearAlgebra.BooleanLatticeInverse.Slot KA → ℕ
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeA p => if i = p then 1 else 0
  | _ => 0

private def cntB (j : Fin 2) : LinearAlgebra.BooleanLatticeInverse.Slot KA → ℕ
  | LinearAlgebra.BooleanLatticeInverse.Slot.freeB b => if j = b then 1 else 0
  | _ => 0

private def cntC (i : Fin KA) (j : Fin 2) : LinearAlgebra.BooleanLatticeInverse.Slot KA → ℕ
  | LinearAlgebra.BooleanLatticeInverse.Slot.pair p b
      => if i = p then (if j = b then 1 else 0) else 0
  | _ => 0

private theorem addSlots_cons (x : LinearAlgebra.BooleanLatticeInverse.Slot KA)
    (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) (ξ : Config KA 2) :
    addSlots (x :: r) ξ = addSlots r (addSlot ξ x) := rfl

private theorem addSlots_a (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (ξ : Config KA 2) (i : Fin KA) :
    (addSlots r ξ).a i = ξ.a i + (r.map (cntA i)).sum := by
  induction r generalizing ξ with
  | nil => simp [addSlots]
  | cons x r ih =>
    rw [addSlots_cons, ih, List.map_cons, List.sum_cons]
    cases x <;> simp [addSlot, addA, addB, addC, cntA, incf_apply, Nat.add_assoc]

private theorem addSlots_b (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (ξ : Config KA 2) (j : Fin 2) :
    (addSlots r ξ).b j = ξ.b j + (r.map (cntB j)).sum := by
  induction r generalizing ξ with
  | nil => simp [addSlots]
  | cons x r ih =>
    rw [addSlots_cons, ih, List.map_cons, List.sum_cons]
    cases x <;> simp [addSlot, addA, addB, addC, cntB, incf_apply, Nat.add_assoc]

private theorem addSlots_c (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (ξ : Config KA 2) (i : Fin KA) (j : Fin 2) :
    (addSlots r ξ).c i j = ξ.c i j + (r.map (cntC i j)).sum := by
  induction r generalizing ξ with
  | nil => simp [addSlots]
  | cons x r ih =>
    rw [addSlots_cons, ih, List.map_cons, List.sum_cons]
    cases x <;> simp [addSlot, addA, addB, addC, cntC, incC_apply, Nat.add_assoc]

private theorem sum_map_flatMap {α β : Type*} (L : List α) (f : α → List β) (g : β → ℕ) :
    ((L.flatMap f).map g).sum = (L.map fun x => ((f x).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem addSlots_slots (ξ : Config KA 2) : addSlots (LinearAlgebra.BooleanLatticeInverse.slots ξ)
    0 = ξ := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_)
    (funext fun i => funext fun j => ?_)
  · rw [addSlots_a]
    simp only [LinearAlgebra.BooleanLatticeInverse.slots, List.map_append, List.sum_append,
        sum_map_flatMap, List.map_replicate,
      List.sum_replicate_nat]
    simp [cntA, ← Fin.sum_univ_def]
  · rw [addSlots_b]
    simp only [LinearAlgebra.BooleanLatticeInverse.slots, List.map_append, List.sum_append,
        sum_map_flatMap, List.map_replicate,
      List.sum_replicate_nat]
    simp [cntB, ← Fin.sum_univ_def]
  · rw [addSlots_c]
    simp only [LinearAlgebra.BooleanLatticeInverse.slots, List.map_append, List.sum_append,
        sum_map_flatMap, List.map_replicate,
      List.sum_replicate_nat]
    simp [cntC, ← Fin.sum_univ_def]

theorem Qc_slots (q : Config KA 2 → F) (ξ : Config KA 2) :
    Qc q (LinearAlgebra.BooleanLatticeInverse.slots ξ) 0 0 ∅ Fin.elim0 Fin.elim0 = q ξ := by
  have h1 : (Fin.elim0 : Fin 0 → Fin KA → F)
      = fun u => Pi.single ((Fin.elim0 : Fin 0 → Fin KA) u) 1 := funext fun u => u.elim0
  have h2 : (Fin.elim0 : Fin 0 → Fin 2 → F)
      = fun u => Pi.single ((Fin.elim0 : Fin 0 → Fin 2) u) 1 := funext fun u => u.elim0
  rw [h1, h2, Qc_basis]
  have hx : xi (∅ : Finset (Fin 0 × Fin 0)) (Fin.elim0 : Fin 0 → Fin KA)
      (Fin.elim0 : Fin 0 → Fin 2) = (0 : Config KA 2) := by
    refine Config.ext (funext fun i => ?_) (funext fun j => ?_)
      (funext fun i => funext fun j => ?_) <;> simp
  rw [hx, addSlots_slots]

end Rhone.Probability.BooleanLatticeInverse
