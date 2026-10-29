/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.StationaryLaw

/-! # Reachability for the jump chain from paths in the rate graph -/

@[expose] public section

namespace Rhone.MarkovChain.RateChain

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {R : RateChain S}

omit [DecidableEq S] in
theorem rate_pos_of_adj {x y : S} (h : R.Adj x y) : 0 < R.rate x := by
  classical
  rw [R.rate_eq_sum]
  exact lt_of_lt_of_le h.2 (Finset.single_le_sum (f := fun z => R.Q x z)
    (fun z hz => R.off_diag_nonneg x z (Finset.ne_of_mem_erase hz).symm)
    (Finset.mem_erase.2 ⟨h.1.symm, Finset.mem_univ y⟩))

theorem jumpChain_P_pos_of_adj {x y : S} (h : R.Adj x y) : 0 < R.jumpChain.P x y := by
  rw [jumpChain_P_of_ne (rate_pos_of_adj h).ne' h.1]
  exact div_pos h.2 (rate_pos_of_adj h)

theorem exists_stepN_pos_of_reflTransGen {x y : S} (h : Relation.ReflTransGen R.Adj x y) :
    ∃ k, 0 < R.jumpChain.stepN k x y := by
  induction h with
  | refl => exact ⟨0, by simp [FinChain.stepN_zero]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [FinChain.stepN_add_apply]
    have hpos : 0 < R.jumpChain.stepN k x b * R.jumpChain.stepN 1 b c :=
      mul_pos hk (by rw [FinChain.stepN_one]; exact jumpChain_P_pos_of_adj hbc)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun z => R.jumpChain.stepN k x z * R.jumpChain.stepN 1 z c)
      (fun z _ => mul_nonneg (R.jumpChain.stepN_nonneg k x z) (R.jumpChain.stepN_nonneg 1 z c))
      (mem_univ b))

theorem reaches_of_reflTransGen {A : Finset S}
    (h : ∀ x, ∃ a ∈ A, Relation.ReflTransGen R.Adj x a) : R.jumpChain.Reaches A := by
  intro x
  obtain ⟨a, ha, hxa⟩ := h x
  obtain ⟨k, hk⟩ := exists_stepN_pos_of_reflTransGen hxa
  exact ⟨k, a, ha, hk⟩

omit [DecidableEq S] in
theorem rate_pos_of_reflTransGen_of_ne {x y : S} (h : Relation.ReflTransGen R.Adj x y)
    (hxy : x ≠ y) : 0 < R.rate x := by
  rcases h.cases_head with h | ⟨z, hz, -⟩
  · exact absurd h hxy
  · exact rate_pos_of_adj hz

end Rhone.MarkovChain.RateChain
