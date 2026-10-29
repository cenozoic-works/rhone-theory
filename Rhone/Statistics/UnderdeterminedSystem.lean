/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Normed.Field.Basic

/-! # A nonzero solution of an underdetermined linear system -/

@[expose] public section

namespace Rhone.Statistics

theorem exists_ne_zero_sum_mul_eq_zero (K : ℕ) (w : ℕ → ℕ → ℝ) :
    ∃ b : ℕ → ℝ, (∃ e, e ≤ K ∧ b e ≠ 0) ∧
      ∀ m, m < K → ∑ e ∈ Finset.range (K + 1), b e * w m e = 0 := by
  let f : (Fin (K + 1) → ℝ) →ₗ[ℝ] (Fin K → ℝ) :=
    { toFun := fun v m => ∑ e : Fin (K + 1), v e * w m e
      map_add' := by
        intro u v
        funext m
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r v
        funext m
        simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
  refine ⟨fun e => if h : e < K + 1 then v ⟨e, h⟩ else 0, ?_, ?_⟩
  · obtain ⟨e, he⟩ := Function.ne_iff.1 hv0
    have he' : (e : ℕ) < K + 1 := e.2
    exact ⟨e, Nat.lt_succ_iff.1 e.2, by simpa [he'] using he⟩
  · intro m hm
    have h := congrFun (LinearMap.mem_ker.1 hv) ⟨m, hm⟩
    rw [Finset.sum_range]
    have hterm : ∀ e : Fin (K + 1),
        (if h : (e : ℕ) < K + 1 then v ⟨e, h⟩ else 0) * w m e = v e * w m e := by
      intro e
      have he' : (e : ℕ) < K + 1 := e.2
      simp [he']
    simp only [hterm]
    simpa [f] using h

end Rhone.Statistics
