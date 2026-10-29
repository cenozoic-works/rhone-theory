/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TwoLocusGenealogy.Prob
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.CorrectnessProof
public import Rhone.Computation.CheckerSoundnessProof

/-! # Rational computation and the ancestral probability law -/
@[expose] public section

open Rhone.LinearAlgebra.Recursion
namespace Rhone.Computation.QProbability

theorem rat_q_cast {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho)
    (xi : Rhone.LinearAlgebra.Recursion.Config KA KB) :
    ((Rhone.LinearAlgebra.Recursion.q (πA := piA) (πB := piB) hA hB hR xi : Rat) : Real) =
      Rhone.LinearAlgebra.Recursion.q
        (πA := fun i => (piA i : Real)) (πB := fun j => (piB j : Real))
        (show 0 < (thetaA : Real) by exact_mod_cast hA)
        (show 0 < (thetaB : Real) by exact_mod_cast hB)
        (show 0 ≤ (rho : Real) by exact_mod_cast hR) xi := by
  have hs := q_isSolution (πA := piA) (πB := piB) hA hB hR
  let qr := fun x : Rhone.LinearAlgebra.Recursion.Config KA KB =>
    ((Rhone.LinearAlgebra.Recursion.q (πA := piA) (πB := piB) hA hB hR x : Rat) : Real)
  have hsol : IsSolution (thetaA : Real) (thetaB : Real) (rho : Real)
      (fun i => (piA i : Real)) (fun j => (piB j : Real)) qr := by
    constructor
    · change ((_ : Rat) : Real) = 1
      rw [hs.empty]; norm_num
    · intro i
      change ((_ : Rat) : Real) = _
      rw [hs.bdryA]
    · intro j
      change ((_ : Rat) : Real) = _
      rw [hs.bdryB]
    · intro i j
      change ((_ : Rat) : Real) = _
      rw [hs.bdryC, Rat.cast_mul]
    · intro x hx
      have hr := congrArg (fun v : Rat => (v : Real)) (hs.recursion x hx)
      simpa only [diag, rhs, qr, Rat.cast_add, Rat.cast_mul, Rat.cast_sum,
        Rat.cast_natCast] using hr
  exact congrFun (q_unique
    (show 0 < (thetaA : Real) by exact_mod_cast hA)
    (show 0 < (thetaB : Real) by exact_mod_cast hB)
    (show 0 ≤ (rho : Real) by exact_mod_cast hR) hsol) xi

theorem rat_q_probability {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho)
    (hpiA : ∀ i, 0 ≤ piA i) (hsA : ∑ i, piA i = 1)
    (hpiB : ∀ j, 0 ≤ piB j) (hsB : ∑ j, piB j = 1)
    (xi : Rhone.LinearAlgebra.Recursion.Config KA KB) :
    ((Rhone.LinearAlgebra.Recursion.q (πA := piA) (πB := piB) hA hB hR xi : Rat) : Real) =
      Rhone.Coalescent.TwoLocusGenealogy.qProb (thetaA : Real) (thetaB : Real) (rho : Real)
        (fun i => (piA i : Real)) (fun j => (piB j : Real)) xi := by
  rw [rat_q_cast thetaA thetaB rho piA piB hA hB hR xi]
  exact (congrFun (Rhone.Coalescent.TwoLocusGenealogy.qProb_eq_q
    (show 0 < (thetaA : Real) by exact_mod_cast hA)
    (show 0 < (thetaB : Real) by exact_mod_cast hB)
    (show 0 ≤ (rho : Real) by exact_mod_cast hR)
    (fun i => by exact_mod_cast hpiA i)
    (show ∑ i, (piA i : Real) = 1 by exact_mod_cast hsA)
    (fun j => by exact_mod_cast hpiB j)
    (show ∑ j, (piB j : Real) = 1 by exact_mod_cast hsB)) xi).symm

end Rhone.Computation.QProbability

namespace Rhone.Computation.QProbability

theorem compute_q_probability (p : Params) (c : Rhone.Computation.Config)
    (hp : p.valid = true) (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4) :
    ∃ v : Rat, Rhone.Computation.q p c = .ok v ∧
      (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (p.thetaA : Real) (p.thetaB : Real) (p.rho : Real)
        (fun i : Fin 2 => (p.piA.getD i.val 0 : Real))
        (fun j : Fin 2 => (p.piB.getD j.val 0 : Real))
        (CheckerEncoding.decode c) := by
  obtain ⟨hA, hB, hR, _, _, hpiA, hpiB, hsA, hsB⟩ := (Params.valid_iff p).mp hp
  refine ⟨Rhone.LinearAlgebra.Recursion.q
    (πA := fun i : Fin 2 => p.piA.getD i.val 0)
    (πB := fun j : Fin 2 => p.piB.getD j.val 0) hA hB hR
    (CheckerEncoding.decode c), q_eq_recursion p c hp ha hb hc hA hB hR, ?_⟩
  exact rat_q_probability p.thetaA p.thetaB p.rho
    (fun i : Fin 2 => p.piA.getD i.val 0)
    (fun j : Fin 2 => p.piB.getD j.val 0) hA hB hR
    (fun i => (hpiA i).le) hsA (fun j => (hpiB j).le) hsB _

theorem checked_table_probability {p : Params} {n : Nat}
    {rows : Array (Rhone.Computation.Config × Rat)} (h : checkTable p n rows = true) :
    ∀ entry ∈ rows, (entry.2 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
      (p.thetaA : Real) (p.thetaB : Real) (p.rho : Real)
      (fun i : Fin 2 => (p.piA.getD i.val 0 : Real))
      (fun j : Fin 2 => (p.piB.getD j.val 0 : Real))
      (CheckerEncoding.decode entry.1) := by
  obtain ⟨hA, hB, hR, hrows⟩ := checkTable_sound h
  obtain ⟨_, _, hp, _⟩ := checkTable_true_iff.mp h
  obtain ⟨_, _, _, _, _, hpiA, hpiB, hsA, hsB⟩ := (Params.valid_iff p).mp hp
  intro entry hmem
  rw [hrows entry hmem]
  exact rat_q_probability p.thetaA p.thetaB p.rho
    (fun i : Fin 2 => p.piA.getD i.val 0)
    (fun j : Fin 2 => p.piB.getD j.val 0) hA hB hR
    (fun i => (hpiA i).le) hsA (fun j => (hpiB j).le) hsB _
end Rhone.Computation.QProbability
