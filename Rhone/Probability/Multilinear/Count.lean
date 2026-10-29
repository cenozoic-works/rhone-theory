/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Delete

/-! # Slot sums as type sums, and the multilinear-recursion terms on basis vectors -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

section Fiber

variable {F : Type*} [CommRing F] (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)

theorem sum_fiber_freeA (g : Fin KA -> F) :
    (∑ k ∈ freeA M, g (α k)) = ∑ i, ((xi M α β).a i : F) * g i := by
  rw [← Finset.sum_fiberwise' (freeA M) α g]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_const, nsmul_eq_mul, xi_a]

theorem sum_fiber_freeB (g : Fin KB -> F) :
    (∑ l ∈ freeB M, g (β l)) = ∑ j, ((xi M α β).b j : F) * g j := by
  rw [← Finset.sum_fiberwise' (freeB M) β g]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_const, nsmul_eq_mul, xi_b]

theorem sum_fiber_cRow (g : Fin KA -> F) :
    (∑ p ∈ M, g (α p.1)) = ∑ i, ((xi M α β).cRow i : F) * g i := by
  rw [← Finset.sum_fiberwise' M (fun p => α p.1) g]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_const, nsmul_eq_mul, cRow_xi]

theorem sum_fiber_cCol (g : Fin KB -> F) :
    (∑ p ∈ M, g (β p.2)) = ∑ j, ((xi M α β).cCol j : F) * g j := by
  rw [← Finset.sum_fiberwise' M (fun p => β p.2) g]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_const, nsmul_eq_mul, cCol_xi]

theorem sum_fiber_M (g : Fin KA → Fin KB → F) :
    (∑ p ∈ M, g (α p.1) (β p.2))
      = ∑ i, ∑ j, (((xi M α β).c i j : ℕ) : F) * g i j := by
  rw [← Finset.sum_fiberwise' M (fun p => (α p.1, β p.2)) (fun y => g y.1 y.2),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hfil : (M.filter fun p => (α p.1, β p.2) = (i, j))
      = M.filter fun p => α p.1 = i ∧ β p.2 = j :=
    Finset.filter_congr fun p _ => by simp [Prod.ext_iff]
  rw [Finset.sum_const, nsmul_eq_mul, hfil, xi_c]

omit [Fintype SA] [Fintype SB] [DecidableEq SB] in
theorem sum_domA_eq (hM : IsMatching M) (g : SA → F) :
    (∑ u ∈ domA M, g u) = ∑ p ∈ M, g p.1 :=
  Finset.sum_image fun p hp p' hp' he => hM.fst p hp p' hp' he

omit [Fintype SA] [DecidableEq SA] [Fintype SB] in
theorem sum_domB_eq (hM : IsMatching M) (g : SB → F) :
    (∑ v ∈ domB M, g v) = ∑ p ∈ M, g p.2 :=
  Finset.sum_image fun p hp p' hp' he => hM.snd p hp p' hp' he

omit [Fintype SB] [DecidableEq SB] in
theorem sum_univ_split_A (g : SA → F) :
    (∑ u : SA, g u) = (∑ u ∈ freeA M, g u) + ∑ u ∈ domA M, g u :=
  (Finset.sum_sdiff (Finset.subset_univ (domA M))).symm

omit [Fintype SA] [DecidableEq SA] in
theorem sum_univ_split_B (g : SB → F) :
    (∑ v : SB, g v) = (∑ v ∈ freeB M, g v) + ∑ v ∈ domB M, g v :=
  (Finset.sum_sdiff (Finset.subset_univ (domB M))).symm

end Fiber

section Merge

variable {F : Type*} [CommRing F]

omit [Fintype SA] in
theorem hadA_basis (α : SA → Fin KA) {a b : SA} (hab : a ≠ b) :
    hadA a b (fun u => (Pi.single (α u) 1 : Fin KA → F))
      = if α a = α b then Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) b 1
        else Function.update
          (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) b 1) a 0 := by
  simp only [hadA, LinearAlgebra.Multilinear.single_mul_single]
  by_cases h : α a = α b
  · rw [ite_eq_left h, ite_eq_left h, Function.update_eq_self]
  · rw [ite_eq_right h, ite_eq_right h, Function.update_comm hab]

omit [Fintype SB] in
theorem hadB_basis (β : SB → Fin KB) {a b : SB} (hab : a ≠ b) :
    hadB a b (fun v => (Pi.single (β v) 1 : Fin KB → F))
      = if β a = β b then Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) b 1
        else Function.update
          (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) b 1) a 0 := by
  simp only [hadB, LinearAlgebra.Multilinear.single_mul_single]
  by_cases h : β a = β b
  · rw [ite_eq_left h, ite_eq_left h, Function.update_eq_self]
  · rw [ite_eq_right h, ite_eq_right h, Function.update_comm hab]

end Merge

section Table

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)
include hθA hθB hρ hq

theorem Q_hadA_basis (hπA : ∑ i, πA i = 1) {a b : SA} (hab : a ≠ b) (hb : b ∈ freeA M) :
    Q q M (hadA a b fun u => (Pi.single (α u) 1 : Fin KA → F))
        (fun v => Pi.single (β v) 1)
      = if α a = α b then q ((xi M α β).dropA (α b)) else 0 := by
  rw [hadA_basis α hab]
  by_cases h : α a = α b
  · rw [ite_eq_left h, ite_eq_left h]
    exact Q_kill_freeA hθA hθB hρ hq M α β hπA hb
  · rw [ite_eq_right h, ite_eq_right h]
    exact (Q_isMultiA q M _).eq_zero_of_slot _ a

theorem Q_hadB_basis (hπB : ∑ j, πB j = 1) {a b : SB} (hab : a ≠ b) (hb : b ∈ freeB M) :
    Q q M (fun u => Pi.single (α u) 1)
        (hadB a b fun v => (Pi.single (β v) 1 : Fin KB → F))
      = if β a = β b then q ((xi M α β).dropB (β b)) else 0 := by
  rw [hadB_basis β hab]
  by_cases h : β a = β b
  · rw [ite_eq_left h, ite_eq_left h]
    exact Q_kill_freeB hθA hθB hρ hq M α β hπB hb
  · rw [ite_eq_right h, ite_eq_right h]
    exact (Q_isMultiB q M _).eq_zero_of_slot _ a

theorem Q_hadAB_basis (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hM : IsMatching M)
    {p p' : SA × SB} (hp : p ∈ M) (hp' : p' ∈ M) (hpp' : p ≠ p') :
    Q q M (hadA p.1 p'.1 fun u => (Pi.single (α u) 1 : Fin KA → F))
        (hadB p.2 p'.2 fun v => (Pi.single (β v) 1 : Fin KB → F))
      = if α p.1 = α p'.1 ∧ β p.2 = β p'.2
        then q ((xi M α β).dropC (α p'.1) (β p'.2)) else 0 := by
  have h1 : p.1 ≠ p'.1 := fun hc => hpp' (hM.fst p hp p' hp' hc)
  have h2 : p.2 ≠ p'.2 := fun hc => hpp' (hM.snd p hp p' hp' hc)
  rw [hadA_basis α h1, hadB_basis β h2]
  by_cases hA : α p.1 = α p'.1
  · by_cases hB : β p.2 = β p'.2
    · rw [ite_eq_left hA, ite_eq_left hB,
        ite_eq_left (show α p.1 = α p'.1 ∧ β p.2 = β p'.2 from ⟨hA, hB⟩)]
      exact Q_kill_pair hθA hθB hρ hq M α β hπA hπB hM hp'
    · rw [ite_eq_left hA, ite_eq_right hB,
        ite_eq_right (show ¬(α p.1 = α p'.1 ∧ β p.2 = β p'.2) from fun hc => hB hc.2)]
      exact (Q_isMultiB q M _).eq_zero_of_slot _ p.2
  · rw [ite_eq_right hA,
      ite_eq_right (show ¬(α p.1 = α p'.1 ∧ β p.2 = β p'.2) from fun hc => hA hc.1)]
    exact (Q_isMultiA q M _).eq_zero_of_slot _ p.1

end Table

end Rhone.Probability.Multilinear
