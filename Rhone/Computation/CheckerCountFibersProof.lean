/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.InfiniteAlleles.Count

/-! # Realization and cardinality of count profiles -/

@[expose] public section
namespace Rhone.Computation.CheckerSpec

open Finset Probability.InfiniteAlleles

theorem exists_fibreCard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (counts : ι → Nat) {n : Nat} (h : ∑ i, counts i = n) :
    ∃ f : Fin n → ι, ∀ i, fibreCard f i = counts i := by
  classical
  let e : Fin n ≃ ((i : ι) × Fin (counts i)) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_sigma] using h.symm)
  refine ⟨fun x => (e x).1, ?_⟩
  intro i
  simp only [fibreCard, Finset.card_filter]
  calc (∑ x : Fin n, if (e x).1 = i then 1 else 0)
      = ∑ y : ((j : ι) × Fin (counts j)), if y.1 = i then 1 else 0 :=
        Equiv.sum_comp e (fun y => if y.1 = i then 1 else 0)
    _ = counts i := by
      rw [Fintype.sum_sigma]
      calc (∑ j, ∑ _k : Fin (counts j), if j = i then 1 else 0)
          = ∑ j, if j = i then counts j else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j = i <;> simp [hj]
        _ = counts i := by simp

theorem card_profile_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (counts : ι → Nat) {n : Nat} (h : ∑ i, counts i = n) :
    (univ.filter fun f : Fin n → ι => ∀ i, fibreCard f i = counts i).card *
      ∏ i, Nat.factorial (counts i) = Nat.factorial n := by
  classical
  obtain ⟨f, hf⟩ := exists_fibreCard counts h
  have hs : (univ.filter fun g : Fin n → ι => ∀ i, fibreCard g i = counts i) =
      sameFibres f := by
    ext g
    simp only [mem_filter, mem_univ, true_and, mem_sameFibres, hf]
  rw [hs]
  simpa only [hf, Fintype.card_fin] using card_sameFibres_mul f

end Rhone.Computation.CheckerSpec
