/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.StructuredCoalescent
public import Rhone.MarkovChain.RateReach
public import Rhone.MarkovChain.ClosedHitting

/-!
# The structured coalescent reaches one lineage

Source: notohara1990, sec. 3, Lemma 5, p. 65. -/

@[expose] public section

namespace Rhone.Coalescent.Structured

open Finset MeasureTheory

variable {n d : ℕ}

def lineages (x : State n d) : ℕ := (univ.filter fun k => (x k).isRight = true).card

def single (n d : ℕ) : Finset (State n d) := univ.filter fun x => lineages x ≤ 1

theorem mem_single {x : State n d} : x ∈ single n d ↔ lineages x ≤ 1 := by
  simp [single]

theorem lineages_migrate (x : State n d) {i : Fin n} {a : Fin d} (hi : x i = Sum.inr a)
    (b : Fin d) : lineages (migrate x i b) = lineages x := by
  unfold lineages
  congr 1
  ext k
  simp only [mem_filter, mem_univ, true_and]
  by_cases hk : k = i
  · subst hk
    simp [migrate_apply_self, hi]
  · rw [migrate_apply_of_ne x hk]

theorem lineages_merge (x : State n d) (i : Fin n) {j : Fin n} {b : Fin d}
    (hj : x j = Sum.inr b) : lineages (merge x i j) + 1 = lineages x := by
  have hfilter : (univ.filter fun k => (merge x i j k).isRight = true) =
      (univ.filter fun k => (x k).isRight = true).erase j := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    by_cases hk : k = j
    · subst hk
      simp [merge_apply_self]
    · by_cases hx : x k = Sum.inl j
      · simp [merge, hx, hk]
      · simp [merge, hx, hk]
  unfold lineages
  rw [hfilter, Finset.card_erase_add_one]
  simp [hj]

theorem isClosedSet_single (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) :
    (chain n M c hM hc).jumpChain.IsClosedSet (single n d) := by
  intro x hx y hy
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  have hQ : (chain n M c hM hc).Q x y = 0 := by
    change generator M c x y = 0
    rw [generator, ite_eq_right hxy, sub_zero]
    by_contra hne
    apply hy
    rw [mem_single] at hx ⊢
    rcases exists_event_of_eventRate_ne_zero M c hne with ⟨i, a, b, hi, -, rfl⟩ |
      ⟨i, j, a, -, -, hj, rfl⟩
    · rw [lineages_migrate x hi]
      exact hx
    · have := lineages_merge x i hj
      omega
  simp [Rhone.MarkovChain.RateChain.jumpChain_P, Rhone.MarkovChain.RateChain.jumpMatrix, hxy, hQ]

theorem adj_migrate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) {i : Fin n}
    {a b : Fin d} (hi : x i = Sum.inr a) (hab : MigAdj M a b) :
    (chain n M c hM hc).Adj x (migrate x i b) :=
  ⟨migrate_ne x hi hab.1, by rw [chain_Q_migrate M c hM hc x hi hab.1]; exact hab.2⟩

theorem adj_merge (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) {i j : Fin n}
    {a : Fin d} (hij : i < j) (hi : x i = Sum.inr a) (hj : x j = Sum.inr a) (hca : 0 < c a) :
    (chain n M c hM hc).Adj x (merge x i j) :=
  ⟨merge_ne x i hj, by rw [chain_Q_merge M c hM hc x hij hi hj]; exact hca⟩

theorem reflTransGen_migrate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (x : State n d) {i : Fin n}
    {a b : Fin d} (hi : x i = Sum.inr a) (hab : Relation.ReflTransGen (MigAdj M) a b) :
    Relation.ReflTransGen (chain n M c hM hc).Adj x (migrate x i b) := by
  induction hab with
  | refl =>
    rw [migrate, ← hi, Function.update_eq_self]
  | @tail b' b'' _ hbc ih =>
    refine ih.tail ?_
    have h := adj_migrate M c hM hc (migrate x i b') (migrate_apply_self x i b') hbc
    rwa [migrate, migrate, Function.update_idem] at h

theorem exists_reflTransGen_lineages (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (x : State n d) {i j : Fin n} {a b : Fin d} (hij : i < j) (hi : x i = Sum.inr a)
    (hj : x j = Sum.inr b) :
    ∃ y, Relation.ReflTransGen (chain n M c hM fun a => (hc a).le).Adj x y ∧
      lineages y + 1 = lineages x := by
  have hj' : migrate x i b j = Sum.inr b := by
    rw [migrate_apply_of_ne x hij.ne', hj]
  refine ⟨merge (migrate x i b) i j, ?_, ?_⟩
  · exact (reflTransGen_migrate M c hM _ x hi (hirr a b)).tail
      (adj_merge M c hM _ _ hij (migrate_apply_self x i b) hj' (hc b))
  · rw [lineages_merge _ i hj', lineages_migrate x hi]

theorem reaches_single (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a) :
    (chain n M c hM fun a => (hc a).le).jumpChain.Reaches (single n d) := by
  apply Rhone.MarkovChain.RateChain.reaches_of_reflTransGen
  have key : ∀ k (x : State n d), lineages x ≤ k → ∃ y ∈ single n d,
      Relation.ReflTransGen (chain n M c hM fun a => (hc a).le).Adj x y := by
    intro k
    induction k with
    | zero => exact fun x hx => ⟨x, mem_single.2 (by omega), Relation.ReflTransGen.refl⟩
    | succ k ih =>
      intro x hx
      by_cases h1 : lineages x ≤ 1
      · exact ⟨x, mem_single.2 h1, Relation.ReflTransGen.refl⟩
      · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (not_le.1 h1)
        obtain ⟨a, ha⟩ := Sum.isRight_iff.1 (Finset.mem_filter.1 hi).2
        obtain ⟨b, hb⟩ := Sum.isRight_iff.1 (Finset.mem_filter.1 hj).2
        obtain ⟨y, hxy, hy⟩ : ∃ y,
            Relation.ReflTransGen (chain n M c hM fun a => (hc a).le).Adj x y ∧
              lineages y + 1 = lineages x := by
          rcases lt_or_gt_of_ne hij with h | h
          · exact exists_reflTransGen_lineages M c hM hirr hc x h ha hb
          · exact exists_reflTransGen_lineages M c hM hirr hc x h hb ha
        obtain ⟨z, hz, hyz⟩ := ih y (by omega)
        exact ⟨z, hz, hxy.trans hyz⟩
  exact fun x => key (lineages x) x le_rfl

instance stateDiscreteMeasurableSpace (n d : ℕ) : DiscreteMeasurableSpace (State n d) :=
  haveI : DiscreteMeasurableSpace (Fin n ⊕ Fin d) :=
    ⟨fun s => by
      rw [measurableSet_sum_iff]
      exact ⟨.of_discrete, .of_discrete⟩⟩
  ⟨fun s => (Set.toFinite s).measurableSet⟩

theorem ae_eventually_single (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (x : State n d) :
    ∀ᵐ ω ∂(chain n M c hM fun a => (hc a).le).jumpChain.pathLaw x,
      ∃ k, ∀ m, k ≤ m → lineages (ω m) ≤ 1 := by
  filter_upwards [(isClosedSet_single M c hM fun a => (hc a).le).ae_eventually_mem
    (reaches_single M c hM hirr hc) x] with ω ⟨k, hk⟩
  exact ⟨k, fun m hm => mem_single.1 (hk m hm)⟩

end Rhone.Coalescent.Structured
