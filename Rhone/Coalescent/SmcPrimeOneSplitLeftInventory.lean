/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtractionPartitions

/-! # Correspondence between old lineage identifiers and left carriers by sample class -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

def ARGLeftInventory {N : ℕ} (s : State) (f : Fin N → ℕ) (d : Option ℕ) : Prop :=
  (∀ a, ∃ i, (s.2.2.2 i).1 = f a) ∧
  (∀ i, (∃ a, f a = (s.2.2.2 i).1) ∨ d = some (s.2.2.2 i).1) ∧
  (∀ b, d = some b → (∃ i, (s.2.2.2 i).1 = b) ∧ ∀ a, f a ≠ b)

def ExtractionInventory {N : ℕ} (z : OneSplitExtractionState N) (s : State) : Prop :=
  Valid z.old.1 ∧ ARGLeftInventory s z.argLabels z.detached ∧
  (∀ a, ∃ i, (z.old.1.2.2.2 i).1 = z.oldLabels a) ∧
  (∀ i, ∃ a, z.oldLabels a = (z.old.1.2.2.2 i).1) ∧
  SameLeftPartition z.argLabels z.oldLabels

theorem extractionInitial_inventory (N : ℕ) :
    ExtractionInventory (extractionInitial N) (initialState N) := by
  refine ⟨SmcSupport.initialState_valid N, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a
    exact ⟨a, rfl⟩
  · intro i
    exact Or.inl ⟨i, rfl⟩
  · intro b h
    cases h
  · intro a
    exact ⟨a, rfl⟩
  · intro i
    exact ⟨i, rfl⟩
  · intro i j
    rfl

theorem ARGLeftInventory.clade_nonempty {N : ℕ} {s : State} {f : Fin N → ℕ}
    {d : Option ℕ} (h : ARGLeftInventory s f d) (i : Fin s.2.2.1)
    (hi : d ≠ some (s.2.2.2 i).1) :
    (extractionClade f (s.2.2.2 i).1).Nonempty := by
  classical
  rcases h.2.1 i with ⟨a, ha⟩ | hd
  · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  · exact False.elim (hi hd)

theorem ExtractionInventory.old_uid_unique {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (hs : Valid s)
    (i : Fin z.old.1.2.2.1) :
    ∃! j : Fin s.2.2.1,
      extractionClade z.argLabels (s.2.2.2 j).1 =
        extractionClade z.oldLabels (z.old.1.2.2.2 i).1 := by
  classical
  obtain ⟨a, ha⟩ := h.2.2.2.1 i
  obtain ⟨j, hj⟩ := h.2.1.1 a
  have he : extractionClade z.argLabels (s.2.2.2 j).1 =
      extractionClade z.oldLabels (z.old.1.2.2.2 i).1 := by
    ext b
    simp only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hj, ← ha]
    exact h.2.2.2.2 b a
  refine ⟨j, he, ?_⟩
  intro k hk
  have hamem : a ∈ extractionClade z.oldLabels (z.old.1.2.2.2 i).1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
  rw [← hk] at hamem
  have hak := (Finset.mem_filter.mp hamem).2
  exact hs.2.2.2 (hak.symm.trans hj.symm)

end Rhone.Coalescent.SmcPrime
