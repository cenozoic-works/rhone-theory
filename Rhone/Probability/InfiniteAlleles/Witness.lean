/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Relabel

/-! # The shape-pair sum is strictly coarser than Golding's configuration object -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

def cWit1 : Config 2 2 := ⟨fun _ => 0, fun _ => 0, ![![2, 0], ![0, 1]]⟩

def cWit2 : Config 2 2 := ⟨fun _ => 0, fun _ => 0, ![![1, 1], ![1, 0]]⟩

theorem cWit1_n : cWit1.n = 3 := by decide

theorem cWit2_n : cWit2.n = 3 := by decide

theorem mA_eq : cWit1.mA = cWit2.mA := by decide

theorem mB_eq : cWit1.mB = cWit2.mB := by decide

theorem cWit2_entry_ne_two : ∀ i j : Fin 2, cWit2.c i j ≠ 2 := by decide

theorem not_relabel (s : Equiv.Perm (Fin 2)) (t : Equiv.Perm (Fin 2)) :
    relabel s t cWit1 ≠ cWit2 := by
  intro h
  have h2 : (relabel s t cWit1).c (s.symm 0) (t.symm 0) = 2 := by
    simp [relabel, cWit1]
  rw [h] at h2
  exact cWit2_entry_ne_two _ _ h2

theorem shape_pair_strictly_coarser :
    cWit1.mA = cWit2.mA ∧ cWit1.mB = cWit2.mB ∧
      ∀ σ τ : Equiv.Perm (Fin 2), relabel σ τ cWit1 ≠ cWit2 :=
  ⟨mA_eq, mB_eq, not_relabel⟩

end Rhone.Probability.InfiniteAlleles
