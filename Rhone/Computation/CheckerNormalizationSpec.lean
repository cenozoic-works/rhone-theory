/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Total

/-! # Ordered-sample normalization over an ordered field -/

@[expose] public section
namespace Rhone.Computation.CheckerSpec

open Finset Coalescent Rhone.LinearAlgebra Probability LinearAlgebra.Recursion
    Coalescent.TwoLocusGenealogy

variable {KA KB : Nat} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem sum_q_ordered (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hsA : ∑ i, πA i = 1)
    (hsB : ∑ j, πB j = 1) (n : ℕ) :
    (∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
      Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)) = 1 := by
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
    have hsplitA : ∀ g : (Fin (n + 1) → Fin KA) → F,
        (∑ σA : Fin (n + 1) → Fin KA, g σA)
          = ∑ i : Fin KA, ∑ σA : Fin n → Fin KA, g (Fin.cons i σA) := by
      intro g
      rw [← Equiv.sum_comp (consEquiv (Fin KA) n) g, Fintype.sum_prod_type]
      rfl
    have hsplitB : ∀ g : (Fin (n + 1) → Fin KB) → F,
        (∑ σB : Fin (n + 1) → Fin KB, g σB)
          = ∑ j : Fin KB, ∑ σB : Fin n → Fin KB, g (Fin.cons j σB) := by
      intro g
      rw [← Equiv.sum_comp (consEquiv (Fin KB) n) g, Fintype.sum_prod_type]
      rfl
    calc (∑ σA : Fin (n + 1) → Fin KA, ∑ σB : Fin (n + 1) → Fin KB,
            Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB))
        = ∑ i : Fin KA, ∑ σA : Fin n → Fin KA, ∑ j : Fin KB, ∑ σB : Fin n → Fin KB,
            Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Denominator.addC (cSample σA σB) i j) := by
          rw [hsplitA]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σA _ => ?_
          rw [hsplitB]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σB _ => by
            rw [cSample_cons]
      _ = ∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB, ∑ j : Fin KB, ∑ i : Fin KA,
            Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Denominator.addC (cSample σA σB) i j) := by
          exact sum_reorder4 fun (i : Fin KA) (σA : Fin n → Fin KA) (j : Fin KB)
            (σB : Fin n → Fin KB) => Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
              (Denominator.addC (cSample σA σB) i j)
      _ = ∑ σA : Fin n → Fin KA, ∑ σB : Fin n → Fin KB,
            Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB) := by
          refine Finset.sum_congr rfl fun σA _ => Finset.sum_congr rfl fun σB _ => ?_
          have h1 : ∀ j : Fin KB,
              (∑ i : Fin KA, Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
                (Denominator.addC (cSample σA σB) i j))
                = Recursion.q (πA := πA) (πB := πB) hθA hθB hρ
                    (Denominator.addB (cSample σA σB) j) :=
            fun j => Denominator.marginalise_C hθA hθB hρ hsA hq (cSample σA σB) j
          simp only [h1]
          exact Denominator.marginalise_B hθA hθB hρ hsB hq (cSample σA σB)
      _ = 1 := ih

end Rhone.Computation.CheckerSpec
