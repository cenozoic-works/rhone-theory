/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.State
public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Reading a configuration off a backward state of the two-locus genealogy -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ}

variable (σA : Fin n → Fin KA) (σB : Fin n → Fin KB)

def MonoA (p : Lin n) : Prop := ∀ k ∈ p.1, ∀ l ∈ p.1, σA k = σA l

def MonoB (p : Lin n) : Prop := ∀ k ∈ p.2, ∀ l ∈ p.2, σB k = σB l

def Clean (L : Finset (Lin n)) : Prop := ∀ p ∈ L, MonoA σA p ∧ MonoB σB p

variable {σA σB}

theorem Clean.monoA {L : Finset (Lin n)} (h : Clean σA σB L) {p : Lin n} (hp : p ∈ L) :
    MonoA σA p := (h p hp).1

theorem Clean.monoB {L : Finset (Lin n)} (h : Clean σA σB L) {p : Lin n} (hp : p ∈ L) :
    MonoB σB p := (h p hp).2

theorem Clean.subset {L M : Finset (Lin n)} (h : Clean σA σB L) (hML : M ⊆ L) : Clean σA σB M :=
  fun p hp => h p (hML hp)

theorem monoA_of_forall {p : Lin n} {i : Fin KA} (h : ∀ k ∈ p.1, σA k = i) : MonoA σA p :=
  fun k hk l hl => by rw [h k hk, h l hl]

theorem monoB_of_forall {p : Lin n} {j : Fin KB} (h : ∀ k ∈ p.2, σB k = j) : MonoB σB p :=
  fun k hk l hl => by rw [h k hk, h l hl]

theorem monoA_of_empty {p : Lin n} (h : p.1 = ∅) : MonoA σA p :=
  fun _ hk => absurd hk (by simp [h])

theorem monoB_of_empty {p : Lin n} (h : p.2 = ∅) : MonoB σB p :=
  fun _ hk => absurd hk (by simp [h])

theorem nonempty_of_not_monoA {p : Lin n} (h : ¬ MonoA σA p) : p.1.Nonempty := by
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty] at hc
  exact h (monoA_of_empty hc)

theorem nonempty_of_not_monoB {p : Lin n} (h : ¬ MonoB σB p) : p.2.Nonempty := by
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty] at hc
  exact h (monoB_of_empty hc)

theorem exists_colourA {p : Lin n} (hm : MonoA σA p) (hne : p.1.Nonempty) :
    ∃ i, ∀ k ∈ p.1, σA k = i := by
  obtain ⟨k₀, hk₀⟩ := hne
  exact ⟨σA k₀, fun k hk => hm k hk k₀ hk₀⟩

theorem exists_colourB {p : Lin n} (hm : MonoB σB p) (hne : p.2.Nonempty) :
    ∃ j, ∀ k ∈ p.2, σB k = j := by
  obtain ⟨k₀, hk₀⟩ := hne
  exact ⟨σB k₀, fun k hk => hm k hk k₀ hk₀⟩

variable (σA σB)

def IsA (i : Fin KA) (p : Lin n) : Prop := p.1.Nonempty ∧ p.2 = ∅ ∧ ∀ k ∈ p.1, σA k = i

def IsB (j : Fin KB) (p : Lin n) : Prop := p.1 = ∅ ∧ p.2.Nonempty ∧ ∀ k ∈ p.2, σB k = j

def IsC (i : Fin KA) (j : Fin KB) (p : Lin n) : Prop :=
  p.1.Nonempty ∧ p.2.Nonempty ∧ (∀ k ∈ p.1, σA k = i) ∧ (∀ k ∈ p.2, σB k = j)

instance (i : Fin KA) (p : Lin n) : Decidable (IsA σA i p) := by unfold IsA; infer_instance

instance (j : Fin KB) (p : Lin n) : Decidable (IsB σB j p) := by unfold IsB; infer_instance

instance (i : Fin KA) (j : Fin KB) (p : Lin n) : Decidable (IsC σA σB i j p) := by
  unfold IsC; infer_instance

variable {σA σB}

theorem IsA.unique {i i' : Fin KA} {p : Lin n} (h : IsA σA i p) (h' : IsA σA i' p) : i = i' := by
  obtain ⟨k₀, hk₀⟩ := h.1
  rw [← h.2.2 k₀ hk₀, ← h'.2.2 k₀ hk₀]

theorem IsB.unique {j j' : Fin KB} {p : Lin n} (h : IsB σB j p) (h' : IsB σB j' p) : j = j' := by
  obtain ⟨k₀, hk₀⟩ := h.2.1
  rw [← h.2.2 k₀ hk₀, ← h'.2.2 k₀ hk₀]

theorem IsC.unique {i i' : Fin KA} {j j' : Fin KB} {p : Lin n} (h : IsC σA σB i j p)
    (h' : IsC σA σB i' j' p) : i = i' ∧ j = j' := by
  obtain ⟨k₀, hk₀⟩ := h.1
  obtain ⟨l₀, hl₀⟩ := h.2.1
  exact ⟨by rw [← h.2.2.1 k₀ hk₀, ← h'.2.2.1 k₀ hk₀], by rw [← h.2.2.2 l₀ hl₀, ← h'.2.2.2 l₀ hl₀]⟩

variable (σA σB)

def uA (p : Lin n) : Fin KA → ℕ := fun i => if IsA σA i p then 1 else 0

def uB (p : Lin n) : Fin KB → ℕ := fun j => if IsB σB j p then 1 else 0

def uC (p : Lin n) : Fin KA → Fin KB → ℕ := fun i j => if IsC σA σB i j p then 1 else 0

variable {σA σB}

theorem uA_eq {i : Fin KA} {p : Lin n} (h : IsA σA i p) : uA σA p = eV i := by
  funext i'
  by_cases h' : i' = i
  · subst h'; simp [uA, h, eV]
  · have hn : ¬ IsA σA i' p := fun hc => h' (IsA.unique hc h)
    simp [uA, hn, eV_of_ne h']

theorem uA_eq_zero {p : Lin n} (h : ∀ i, ¬ IsA σA i p) : uA σA p = 0 := by
  funext i; simp [uA, h i]

theorem uB_eq {j : Fin KB} {p : Lin n} (h : IsB σB j p) : uB σB p = eV j := by
  funext j'
  by_cases h' : j' = j
  · subst h'; simp [uB, h, eV]
  · have hn : ¬ IsB σB j' p := fun hc => h' (IsB.unique hc h)
    simp [uB, hn, eV_of_ne h']

theorem uB_eq_zero {p : Lin n} (h : ∀ j, ¬ IsB σB j p) : uB σB p = 0 := by
  funext j; simp [uB, h j]

theorem uC_eq {i : Fin KA} {j : Fin KB} {p : Lin n} (h : IsC σA σB i j p) :
    uC σA σB p = eM i j := by
  funext i' j'
  by_cases h1 : i' = i
  · subst h1
    by_cases h2 : j' = j
    · subst h2; simp [uC, h, eM_apply]
    · have hn : ¬ IsC σA σB i' j' p := fun hc => h2 (IsC.unique hc h).2
      simp [uC, hn, eM_apply, h2]
  · have hn : ¬ IsC σA σB i' j' p := fun hc => h1 (IsC.unique hc h).1
    simp [uC, hn, eM_apply, h1]

theorem uC_eq_zero {p : Lin n} (h : ∀ i j, ¬ IsC σA σB i j p) : uC σA σB p = 0 := by
  funext i j; simp [uC, h i j]

theorem uA_eq_zero_of_carB {p : Lin n} (h : p.2.Nonempty) : uA σA p = 0 :=
  uA_eq_zero fun _ hc => (Finset.nonempty_iff_ne_empty.1 h) hc.2.1

theorem uB_eq_zero_of_carA {p : Lin n} (h : p.1.Nonempty) : uB σB p = 0 :=
  uB_eq_zero fun _ hc => (Finset.nonempty_iff_ne_empty.1 h) hc.1

theorem uC_eq_zero_of_emptyA {p : Lin n} (h : p.1 = ∅) : uC σA σB p = 0 :=
  uC_eq_zero fun _ _ hc => (Finset.nonempty_iff_ne_empty.1 hc.1) h

theorem uC_eq_zero_of_emptyB {p : Lin n} (h : p.2 = ∅) : uC σA σB p = 0 :=
  uC_eq_zero fun _ _ hc => (Finset.nonempty_iff_ne_empty.1 hc.2.1) h

theorem u_eq_zero_of_notMonoA {p : Lin n} (h : ¬ MonoA σA p) :
    uA σA p = 0 ∧ uB σB p = 0 ∧ uC σA σB p = 0 :=
  ⟨uA_eq_zero fun _ hc => h (monoA_of_forall hc.2.2), uB_eq_zero_of_carA (nonempty_of_not_monoA h),
    uC_eq_zero fun _ _ hc => h (monoA_of_forall hc.2.2.1)⟩

theorem u_eq_zero_of_notMonoB {p : Lin n} (h : ¬ MonoB σB p) :
    uA σA p = 0 ∧ uB σB p = 0 ∧ uC σA σB p = 0 :=
  ⟨uA_eq_zero_of_carB (nonempty_of_not_monoB h), uB_eq_zero fun _ hc => h (monoB_of_forall hc.2.2),
    uC_eq_zero fun _ _ hc => h (monoB_of_forall hc.2.2.2)⟩

variable (σA σB)

def cfgA (L : Finset (Lin n)) : Fin KA → ℕ := ∑ p ∈ L, uA σA p

def cfgB (L : Finset (Lin n)) : Fin KB → ℕ := ∑ p ∈ L, uB σB p

def cfgC (L : Finset (Lin n)) : Fin KA → Fin KB → ℕ := ∑ p ∈ L, uC σA σB p

def cfg (L : Finset (Lin n)) : Config KA KB := ⟨cfgA σA L, cfgB σB L, cfgC σA σB L⟩

@[simp] theorem cfg_a (L : Finset (Lin n)) : (cfg σA σB L).a = cfgA σA L := rfl
@[simp] theorem cfg_b (L : Finset (Lin n)) : (cfg σA σB L).b = cfgB σB L := rfl
@[simp] theorem cfg_c (L : Finset (Lin n)) : (cfg σA σB L).c = cfgC σA σB L := rfl

@[simp] theorem cfgA_empty : cfgA σA (∅ : Finset (Lin n)) = 0 := by simp [cfgA]
@[simp] theorem cfgB_empty : cfgB σB (∅ : Finset (Lin n)) = 0 := by simp [cfgB]
@[simp] theorem cfgC_empty : cfgC σA σB (∅ : Finset (Lin n)) = 0 := by simp [cfgC]

theorem cfg_empty : cfg σA σB (∅ : Finset (Lin n)) = 0 := by
  refine Config.ext ?_ ?_ ?_
  · funext i; simp [cfg]
  · funext j; simp [cfg]
  · funext i j; simp [cfg]

variable {σA σB}

theorem cfgA_insert {L : Finset (Lin n)} {p : Lin n} (h : p ∉ L) :
    cfgA σA (insert p L) = uA σA p + cfgA σA L := Finset.sum_insert h

theorem cfgB_insert {L : Finset (Lin n)} {p : Lin n} (h : p ∉ L) :
    cfgB σB (insert p L) = uB σB p + cfgB σB L := Finset.sum_insert h

theorem cfgC_insert {L : Finset (Lin n)} {p : Lin n} (h : p ∉ L) :
    cfgC σA σB (insert p L) = uC σA σB p + cfgC σA σB L := Finset.sum_insert h

theorem cfgA_erase {L : Finset (Lin n)} {p : Lin n} (h : p ∈ L) :
    cfgA σA L = uA σA p + cfgA σA (L.erase p) := (Finset.add_sum_erase _ _ h).symm

theorem cfgB_erase {L : Finset (Lin n)} {p : Lin n} (h : p ∈ L) :
    cfgB σB L = uB σB p + cfgB σB (L.erase p) := (Finset.add_sum_erase _ _ h).symm

theorem cfgC_erase {L : Finset (Lin n)} {p : Lin n} (h : p ∈ L) :
    cfgC σA σB L = uC σA σB p + cfgC σA σB (L.erase p) := (Finset.add_sum_erase _ _ h).symm

end Rhone.Coalescent.TwoLocusGenealogy
