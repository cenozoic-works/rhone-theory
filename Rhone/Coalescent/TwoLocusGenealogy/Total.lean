/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Absorb

/-! # The sampling probabilities of the ordered typed samples sum to one -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def consEquiv (α : Type*) (n : ℕ) : α × (Fin n → α) ≃ (Fin (n + 1) → α) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by simp
  right_inv f := by
    funext i
    induction i using Fin.cases <;> simp

theorem sum_reorder4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (X : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, X a b c d) = ∑ b, ∑ d, ∑ c, ∑ a, X a b c d := by
  calc (∑ a, ∑ b, ∑ c, ∑ d, X a b c d)
      = ∑ b, ∑ a, ∑ c, ∑ d, X a b c d := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, X a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ a, ∑ c, X a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ c, ∑ a, X a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem cSample_cons {n : ℕ} (i : Fin KA) (j : Fin KB) (σA : Fin n → Fin KA)
    (σB : Fin n → Fin KB) :
    cSample (Fin.cons i σA) (Fin.cons j σB) = Probability.Denominator.addC (cSample σA σB) i j := by
  refine Config.ext rfl rfl ?_
  funext i' j'
  change ((Finset.univ.filter fun k : Fin (n + 1) =>
      (Fin.cons i σA : Fin (n + 1) → Fin KA) k = i'
        ∧ (Fin.cons j σB : Fin (n + 1) → Fin KB) k = j').card : ℕ)
    = Config.incC (cSample σA σB).c i j i' j'
  rw [incC_eq_add]
  change _ = eM i j i' j' + (Finset.univ.filter fun k : Fin n => σA k = i' ∧ σB k = j').card
  rw [Finset.card_filter, Fin.sum_univ_succ, Finset.card_filter, eM_apply]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  by_cases h1 : i' = i
  · by_cases h2 : j' = j
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

theorem sum_q_cSample (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hsA : ∑ i, πA i = 1)
    (hsB : ∑ j, πB j = 1) (n : ℕ) :
    (∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
      LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)) = 1 := by
  induction n with
  | zero =>
    have hc : ∀ (σA : Fin 0 → Fin KA) (σB : Fin 0 → Fin KB),
        cSample σA σB = (0 : Config KA KB) := by
      intro σA σB
      refine Config.ext rfl rfl ?_
      funext i j
      simp [cSample]
    simp [hc, (q_isSolution hθA hθB hρ).empty]
  | succ n ih =>
    have hq := q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
    have hsplitA : ∀ g : (Fin (n + 1) → Fin KA) → ℝ,
        (∑ σA : Fin (n + 1) → Fin KA, g σA)
          = ∑ i : Fin KA, ∑ σA : Fin n → Fin KA, g (Fin.cons i σA) := by
      intro g
      rw [← Equiv.sum_comp (consEquiv (Fin KA) n) g, Fintype.sum_prod_type]
      rfl
    have hsplitB : ∀ g : (Fin (n + 1) → Fin KB) → ℝ,
        (∑ σB : Fin (n + 1) → Fin KB, g σB)
          = ∑ j : Fin KB, ∑ σB : Fin n → Fin KB, g (Fin.cons j σB) := by
      intro g
      rw [← Equiv.sum_comp (consEquiv (Fin KB) n) g, Fintype.sum_prod_type]
      rfl
    calc (∑ σA : Fin (n + 1) → Fin KA, ∑ σB : Fin (n + 1) → Fin KB,
            LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB))
        = ∑ i : Fin KA, ∑ σA : Fin n → Fin KA, ∑ j : Fin KB, ∑ σB : Fin n → Fin KB,
            LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Probability.Denominator.addC (cSample σA σB) i j) := by
          rw [hsplitA]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σA _ => ?_
          rw [hsplitB]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σB _ => by
            rw [cSample_cons]
      _ = ∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB, ∑ j : Fin KB, ∑ i : Fin KA,
            LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Probability.Denominator.addC (cSample σA σB) i j) := by
          exact sum_reorder4 fun (i : Fin KA) (σA : Fin n → Fin KA) (j : Fin KB)
            (σB : Fin n → Fin KB) => LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Probability.Denominator.addC (cSample σA σB) i j)
      _ = ∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
            LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB) := by
          refine Finset.sum_congr rfl fun σA _ => Finset.sum_congr rfl fun σB _ => ?_
          have h1 : ∀ j : Fin KB,
              (∑ i : Fin KA, LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
                (Probability.Denominator.addC (cSample σA σB) i j))
                = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
                    (Probability.Denominator.addB (cSample σA σB) j) :=
            fun j => Probability.Denominator.marginalise_C hθA hθB hρ hsA hq (cSample σA σB) j
          simp only [h1]
          exact Probability.Denominator.marginalise_B hθA hθB hρ hsB hq (cSample σA σB)
      _ = 1 := ih

end Rhone.Coalescent.TwoLocusGenealogy
