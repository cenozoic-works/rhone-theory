/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Push
public import Rhone.LinearAlgebra.Recursion.Exist

/-! # The two support-reduction theorems -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB K L : ℕ} (e : Fin KA ↪ Fin K) (f : Fin KB ↪ Fin L)

section Ring

variable {F : Type*} [CommRing F] (θA θB ρ : F)

theorem diag_push (ξ : Config KA KB) :
    diag θA θB ρ (push e f ξ) = diag θA θB ρ ξ := by
  simp [Rhone.LinearAlgebra.Recursion.diag]

theorem rhsIA_push (h : Config K L → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ h (push e f ξ) = rhsIA θA θB ρ (fun η => h (push e f η)) ξ := by
  have e1 : (∑ i', (((push e f ξ).coalA i' : ℕ) : F) * h ((push e f ξ).dropA i'))
      = ∑ i, ((ξ.coalA i : ℕ) : F) * h (push e f (ξ.dropA i)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => by rw [coalA_push_off e f ξ hi']; simp]
    exact Finset.sum_congr rfl fun i _ => by rw [coalA_push, push_dropA]
  have e2 : (∑ j', (((push e f ξ).coalB j' : ℕ) : F) * h ((push e f ξ).dropB j'))
      = ∑ j, ((ξ.coalB j : ℕ) : F) * h (push e f (ξ.dropB j)) := by
    rw [sum_eq_sum_emb f _ fun j' hj' => by rw [coalB_push_off e f ξ hj']; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalB_push, push_dropB]
  have e3 : (∑ i', ∑ j', (((push e f ξ).coalC i' j' : ℕ) : F) * h ((push e f ξ).dropC i' j'))
      = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (push e f (ξ.dropC i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [Config.coalC_eq_zero_of _ (push_c_off_left e f ξ hi' j')]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by
      rw [Config.coalC_eq_zero_of _ (push_c_off_right e f ξ (e i) hj')]; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalC_push, push_dropC]
  have e4 : (∑ i', ∑ j', (((push e f ξ).coalAB i' j' : ℕ) : F) * h ((push e f ξ).mergeAB i' j'))
      = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (push e f (ξ.mergeAB i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [Config.coalAB_eq_zero_left _ j' (push_a_off e f ξ hi')]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by
      rw [Config.coalAB_eq_zero_right _ (e i) (push_b_off e f ξ hj')]; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalAB_push, push_mergeAB]
  have e5 : (∑ i', (((dropIndA (push e f ξ) i' : ℕ) : F) * h ((push e f ξ).dropA i')
        + ∑ j', ((killIndA (push e f ξ) i' j' : ℕ) : F) * h ((push e f ξ).killA i' j')))
      = ∑ i, (((dropIndA ξ i : ℕ) : F) * h (push e f (ξ.dropA i))
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * h (push e f (ξ.killA i j))) := by
    have hoff : ∀ i' : Fin K, (∀ i, e i ≠ i') →
        (((dropIndA (push e f ξ) i' : ℕ) : F) * h ((push e f ξ).dropA i')
          + ∑ j', ((killIndA (push e f ξ) i' j' : ℕ) : F) * h ((push e f ξ).killA i' j')) = 0 := by
      intro i' hi'
      rw [dropIndA_push_off e f ξ hi', Finset.sum_congr rfl fun j' _ => by
        rw [killIndA_eq_zero_of _ (push_c_off_left e f ξ hi' j')]]
      simp
    rw [sum_eq_sum_emb e _ hoff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dropIndA_push, push_dropA]
    refine congrArg _ ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by
      rw [killIndA_eq_zero_of _ (push_c_off_right e f ξ (e i) hj')]; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [killIndA_push, push_killA]
  have e6 : (∑ j', (((dropIndB (push e f ξ) j' : ℕ) : F) * h ((push e f ξ).dropB j')
        + ∑ i', ((killIndB (push e f ξ) i' j' : ℕ) : F) * h ((push e f ξ).killB i' j')))
      = ∑ j, (((dropIndB ξ j : ℕ) : F) * h (push e f (ξ.dropB j))
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * h (push e f (ξ.killB i j))) := by
    have hoff : ∀ j' : Fin L, (∀ j, f j ≠ j') →
        (((dropIndB (push e f ξ) j' : ℕ) : F) * h ((push e f ξ).dropB j')
          + ∑ i', ((killIndB (push e f ξ) i' j' : ℕ) : F) * h ((push e f ξ).killB i' j')) = 0 := by
      intro j' hj'
      rw [dropIndB_push_off e f ξ hj', Finset.sum_congr rfl fun i' _ => by
        rw [killIndB_eq_zero_of _ (push_c_off_right e f ξ i' hj')]]
      simp
    rw [sum_eq_sum_emb f _ hoff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dropIndB_push, push_dropB]
    refine congrArg _ ?_
    rw [sum_eq_sum_emb e _ fun i' hi' => by
      rw [killIndB_eq_zero_of _ (push_c_off_left e f ξ hi' (f j))]; simp]
    exact Finset.sum_congr rfl fun i _ => by rw [killIndB_push, push_killB]
  have e7 : (∑ i', ∑ j', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).split i' j'))
      = ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (push e f (ξ.split i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [push_c_off_left e f ξ hi' j']; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by rw [push_c_off_right e f ξ (e i) hj']; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [push_c, push_split]
  simp only [rhsIA, e1, e2, e3, e4, e5, e6, e7]

theorem rhs_push (πA : Fin K → F) (πB : Fin L → F) (h : Config K L → F) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB h (push e f ξ)
      = rhs θA θB ρ (fun i => πA (e i)) (fun j => πB (f j)) (fun η => h (push e f η)) ξ := by
  have e1 : (∑ i', (((push e f ξ).coalA i' : ℕ) : F) * h ((push e f ξ).dropA i'))
      = ∑ i, ((ξ.coalA i : ℕ) : F) * h (push e f (ξ.dropA i)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => by rw [coalA_push_off e f ξ hi']; simp]
    exact Finset.sum_congr rfl fun i _ => by rw [coalA_push, push_dropA]
  have e2 : (∑ j', (((push e f ξ).coalB j' : ℕ) : F) * h ((push e f ξ).dropB j'))
      = ∑ j, ((ξ.coalB j : ℕ) : F) * h (push e f (ξ.dropB j)) := by
    rw [sum_eq_sum_emb f _ fun j' hj' => by rw [coalB_push_off e f ξ hj']; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalB_push, push_dropB]
  have e3 : (∑ i', ∑ j', (((push e f ξ).coalC i' j' : ℕ) : F) * h ((push e f ξ).dropC i' j'))
      = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (push e f (ξ.dropC i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [Config.coalC_eq_zero_of _ (push_c_off_left e f ξ hi' j')]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by
      rw [Config.coalC_eq_zero_of _ (push_c_off_right e f ξ (e i) hj')]; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalC_push, push_dropC]
  have e4 : (∑ i', ∑ j', (((push e f ξ).coalAB i' j' : ℕ) : F) * h ((push e f ξ).mergeAB i' j'))
      = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (push e f (ξ.mergeAB i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [Config.coalAB_eq_zero_left _ j' (push_a_off e f ξ hi')]; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by
      rw [Config.coalAB_eq_zero_right _ (e i) (push_b_off e f ξ hj')]; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [coalAB_push, push_mergeAB]
  have e5 : (∑ i', πA i' * ((((push e f ξ).a i' : ℕ) : F) * h ((push e f ξ).dropA i')
        + ∑ j', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).killA i' j')))
      = ∑ i, πA (e i) * (((ξ.a i : ℕ) : F) * h (push e f (ξ.dropA i))
        + ∑ j, ((ξ.c i j : ℕ) : F) * h (push e f (ξ.killA i j))) := by
    have hoff : ∀ i' : Fin K, (∀ i, e i ≠ i') →
        πA i' * ((((push e f ξ).a i' : ℕ) : F) * h ((push e f ξ).dropA i')
          + ∑ j', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).killA i' j')) = 0 := by
      intro i' hi'
      rw [push_a_off e f ξ hi', Finset.sum_congr rfl fun j' _ => by
        rw [push_c_off_left e f ξ hi' j']]
      simp
    rw [sum_eq_sum_emb e _ hoff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [push_a, push_dropA]
    refine congrArg _ (congrArg _ ?_)
    rw [sum_eq_sum_emb f _ fun j' hj' => by rw [push_c_off_right e f ξ (e i) hj']; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [push_c, push_killA]
  have e6 : (∑ j', πB j' * ((((push e f ξ).b j' : ℕ) : F) * h ((push e f ξ).dropB j')
        + ∑ i', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).killB i' j')))
      = ∑ j, πB (f j) * (((ξ.b j : ℕ) : F) * h (push e f (ξ.dropB j))
        + ∑ i, ((ξ.c i j : ℕ) : F) * h (push e f (ξ.killB i j))) := by
    have hoff : ∀ j' : Fin L, (∀ j, f j ≠ j') →
        πB j' * ((((push e f ξ).b j' : ℕ) : F) * h ((push e f ξ).dropB j')
          + ∑ i', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).killB i' j')) = 0 := by
      intro j' hj'
      rw [push_b_off e f ξ hj', Finset.sum_congr rfl fun i' _ => by
        rw [push_c_off_right e f ξ i' hj']]
      simp
    rw [sum_eq_sum_emb f _ hoff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [push_b, push_dropB]
    refine congrArg _ (congrArg _ ?_)
    rw [sum_eq_sum_emb e _ fun i' hi' => by rw [push_c_off_left e f ξ hi' (f j)]; simp]
    exact Finset.sum_congr rfl fun i _ => by rw [push_c, push_killB]
  have e7 : (∑ i', ∑ j', (((push e f ξ).c i' j' : ℕ) : F) * h ((push e f ξ).split i' j'))
      = ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (push e f (ξ.split i j)) := by
    rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ => by
      rw [push_c_off_left e f ξ hi' j']; simp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_eq_sum_emb f _ fun j' hj' => by rw [push_c_off_right e f ξ (e i) hj']; simp]
    exact Finset.sum_congr rfl fun j _ => by rw [push_c, push_split]
  simp only [rhs, e1, e2, e3, e4, e5, e6, e7]

end Ring

section Ordered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem isSolutionIA_push {q : Config K L → F} (hq : IsSolutionIA θA θB ρ q) :
    IsSolutionIA θA θB ρ (fun ξ : Config KA KB => q (push e f ξ)) where
  empty := by rw [push_zero]; exact hq.empty
  bdryA i := by rw [push_eA]; exact hq.bdryA _
  bdryB j := by rw [push_eB]; exact hq.bdryB _
  recursion ξ hξ := by
    have hlev : 2 ≤ (push e f ξ).nA + (push e f ξ).nB := by
      rw [nA_push, nB_push]; exact hξ
    rw [← diag_push e f θA θB ρ ξ, hq.recursion _ hlev, rhsIA_push]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem isSolution_push {πA : Fin K → F} {πB : Fin L → F} {q : Config K L → F}
    (hq : IsSolution θA θB ρ πA πB q) :
    IsSolution θA θB ρ (fun i => πA (e i)) (fun j => πB (f j))
      (fun ξ : Config KA KB => q (push e f ξ)) where
  empty := by rw [push_zero]; exact hq.empty
  bdryA i := by rw [push_eA]; exact hq.bdryA _
  bdryB j := by rw [push_eB]; exact hq.bdryB _
  bdryC i j := by rw [push_eC]; exact hq.bdryC _ _
  recursion ξ hξ := by
    have hn : 2 ≤ (push e f ξ).n := by rw [n_push]; exact hξ
    rw [← diag_push e f θA θB ρ ξ, hq.recursion _ hn, rhs_push]

theorem q_push (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (πA : Fin K → F) (πB : Fin L → F)
    (ξ : Config KA KB) :
    LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (push e f ξ)
      = LinearAlgebra.Recursion.q (πA := fun i => πA (e i)) (πB := fun j => πB (f j)) hθA hθB hρ
          ξ :=
  congrFun (LinearAlgebra.Recursion.q_unique hθA hθB hρ
    (isSolution_push e f (LinearAlgebra.Recursion.q_isSolution hθA hθB hρ))) ξ

theorem PIA_push (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB) :
    PIA (KA := K) (KB := L) hθA hθB hρ (push e f ξ) = PIA (KA := KA) (KB := KB) hθA hθB hρ ξ :=
  congrFun (PIA_unique hθA hθB hρ (isSolutionIA_push e f (PIA_isSolutionIA hθA hθB hρ))) ξ

end Ordered

end Rhone.Probability.InfiniteAlleles
