/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeEpochs

/-!
# Extant branch multiplicity retains individual finite-array indices

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeActiveUnique {N : ℕ} (T : Tree N) : Prop :=
  ∀ q, 0 ≤ q → ∀ i ∈ activeBranches T q, ∀ j ∈ activeBranches T q,
    (T.2 i).1 = (T.2 j).1 → i = j

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem active_branches_epoch_predecessor {N : ℕ} (T : Tree N)
    (q : ℝ) (hq : 0 ≤ q) :
    activeBranches T q = activeBranches T (epochPredecessor T q) := by
  classical
  obtain ⟨_, hpq, _, hgreat⟩ := epoch_predecessor_bounds T q hq
  have hcmp (e : ℝ) (he : e ∈ treeEpochs T) : e ≤ q ↔ e ≤ epochPredecessor T q :=
    ⟨hgreat e he, fun h => h.trans hpq⟩
  ext i
  have hlo := hcmp (T.2 i).2.1 (by
    apply List.mem_append.mpr
    exact Or.inr (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩))
  have hhi := hcmp (T.2 i).2.2 (by
    apply List.mem_append.mpr
    exact Or.inr (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩))
  have hstrict : q < (T.2 i).2.2 ↔ epochPredecessor T q < (T.2 i).2.2 := by
    rw [← not_le, ← not_le, hhi]
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, hlo, hstrict]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tree_active_unique_iff_epochs {N : ℕ} (T : Tree N) :
    TreeActiveUnique T ↔ ∀ q ∈ treeEpochs T, 0 ≤ q →
      ∀ i ∈ activeBranches T q, ∀ j ∈ activeBranches T q,
        (T.2 i).1 = (T.2 j).1 → i = j := by
  constructor
  · intro h q _ hq
    exact h q hq
  · intro h q hq
    obtain ⟨hp0, _, hpmem, _⟩ := epoch_predecessor_bounds T q hq
    rw [active_branches_epoch_predecessor T q hq]
    exact h _ hpmem hp0

end Rhone.Coalescent.SmcPrime
