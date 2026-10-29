/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Count

/-! # The multilinear recursion -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

section Ind

variable {ι : Type*} [DecidableEq ι] {F : Type*} [CommRing F]

omit [DecidableEq ι] in
theorem sum_ite_count (s : Finset ι) (P : ι → Prop) [DecidablePred P] (c : F) :
    (∑ m ∈ s, if P m then c else 0) = (((s.filter P).card : ℕ) : F) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem sum_ite_erase {s : Finset ι} {k : ι} (hk : k ∈ s) (P : ι → Prop) [DecidablePred P]
    (hPk : P k) (c : F) :
    (∑ m ∈ s.erase k, if P m then c else 0) = ((((s.filter P).card - 1 : ℕ)) : F) * c := by
  have h := card_filter_erase_add hk P
  rw [ite_eq_left hPk] at h
  have hc : ((s.erase k).filter P).card = (s.filter P).card - 1 := by omega
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc]

end Ind

section Statement

variable {F : Type*} [CommRing F]

def dgQ (θA θB ρ : F) (nA nB t : ℕ) : F :=
  (((nA + nB - t) * (nA + nB - t - 1) : ℕ) : F) + θA * nA + θB * nB + ρ * t

def rhsQ (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (M : Finset (SA × SB)) (s : SA → Fin KA → F) (w : SB → Fin KB → F) : F :=
  (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k, Q q M (hadA k m s) w)
  + 2 * (∑ k ∈ freeA M, ∑ p ∈ M, Q q M (hadA p.1 k s) w)
  + (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l, Q q M s (hadB l n w))
  + 2 * (∑ l ∈ freeB M, ∑ p ∈ M, Q q M s (hadB p.2 l w))
  + (∑ p ∈ M, ∑ p' ∈ M.erase p, Q q M (hadA p.1 p'.1 s) (hadB p.2 p'.2 w))
  + 2 * (∑ k ∈ freeA M, ∑ l ∈ freeB M, Q q (insert (k, l) M) s w)
  + θA * (∑ u : SA, mean πA (s u) * Q q M (Function.update s u 1) w)
  + θB * (∑ v : SB, mean πB (w v) * Q q M s (Function.update w v 1))
  + ρ * (∑ p ∈ M, Q q (M.erase p) s w)

variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
variable (M : Finset (SA × SB))

theorem rhsQ_isMultiA (hM : IsMatching M) (w : SB → Fin KB → F) :
    LinearAlgebra.Multilinear.IsMulti (fun s => rhsQ θA θB ρ πA πB q M s w) := by
  have hne : ∀ p ∈ M, ∀ p' ∈ M.erase p, p.1 ≠ p'.1 := fun p hp p' hp' hc =>
    (Finset.mem_erase.mp hp').1 (hM.fst p hp p' (Finset.mem_erase.mp hp').2 hc).symm
  have h1 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      ∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k, Q q M (hadA k m s) w) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k _ => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun m hm =>
      Q_hadA_isMultiA q M w (Ne.symm (Finset.mem_erase.mp hm).1)
  have h2 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      2 * ∑ k ∈ freeA M, ∑ p ∈ M, Q q M (hadA p.1 k s) w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k hk => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun p hp =>
      Q_hadA_isMultiA q M w (fst_ne_of_mem_freeA hk hp))
  have h3 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      ∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l, Q q M s (hadB l n w)) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun l _ => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun n _ => Q_isMultiA q M _
  have h4 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      2 * ∑ l ∈ freeB M, ∑ p ∈ M, Q q M s (hadB p.2 l w)) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun l _ => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun p _ => Q_isMultiA q M _)
  have h5 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      ∑ p ∈ M, ∑ p' ∈ M.erase p, Q q M (hadA p.1 p'.1 s) (hadB p.2 p'.2 w)) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun p hp => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun p' hp' =>
      Q_hadA_isMultiA q M _ (hne p hp p' hp')
  have h6 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      2 * ∑ k ∈ freeA M, ∑ l ∈ freeB M, Q q (insert (k, l) M) s w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k _ => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun l _ => Q_isMultiA q _ w)
  have h7 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      θA * ∑ u : SA, mean πA (s u) * Q q M (Function.update s u 1) w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun u _ => Q_mutA_isMultiA q M πA w u)
  have h8 : LinearAlgebra.Multilinear.IsMulti (fun s : SA → Fin KA → F =>
      θB * ∑ v : SB, mean πB (w v) * Q q M s (Function.update w v 1)) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun v _ =>
        LinearAlgebra.Multilinear.IsMulti.const_mul _ (Q_isMultiA q M _))
  have h9 : LinearAlgebra.Multilinear.IsMulti
      (fun s : SA → Fin KA → F => ρ * ∑ p ∈ M, Q q (M.erase p) s w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun p _ => Q_isMultiA q _ w)
  exact (((((((h1.add' h2).add' h3).add' h4).add' h5).add' h6).add' h7).add' h8).add' h9

theorem rhsQ_isMultiB (hM : IsMatching M) (s : SA → Fin KA → F) :
    LinearAlgebra.Multilinear.IsMulti (fun w => rhsQ θA θB ρ πA πB q M s w) := by
  have hne : ∀ p ∈ M, ∀ p' ∈ M.erase p, p.2 ≠ p'.2 := fun p hp p' hp' hc =>
    (Finset.mem_erase.mp hp').1 (hM.snd p hp p' (Finset.mem_erase.mp hp').2 hc).symm
  have h1 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      ∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k, Q q M (hadA k m s) w) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k _ => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun m _ => Q_isMultiB q M _
  have h2 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      2 * ∑ k ∈ freeA M, ∑ p ∈ M, Q q M (hadA p.1 k s) w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k _ => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun p _ => Q_isMultiB q M _)
  have h3 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      ∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l, Q q M s (hadB l n w)) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun l _ => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun n hn =>
      Q_hadB_isMultiB q M s (Ne.symm (Finset.mem_erase.mp hn).1)
  have h4 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      2 * ∑ l ∈ freeB M, ∑ p ∈ M, Q q M s (hadB p.2 l w)) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun l hl => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun p hp =>
      Q_hadB_isMultiB q M s (snd_ne_of_mem_freeB hl hp))
  have h5 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      ∑ p ∈ M, ∑ p' ∈ M.erase p, Q q M (hadA p.1 p'.1 s) (hadB p.2 p'.2 w)) :=
    LinearAlgebra.Multilinear.IsMulti.sum _ _ fun p hp => LinearAlgebra.Multilinear.IsMulti.sum _ _
        fun p' hp' =>
      Q_hadB_isMultiB q M _ (hne p hp p' hp')
  have h6 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      2 * ∑ k ∈ freeA M, ∑ l ∈ freeB M, Q q (insert (k, l) M) s w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun k _ => LinearAlgebra.Multilinear.IsMulti.sum
        _ _ fun l _ => Q_isMultiB q _ s)
  have h7 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      θA * ∑ u : SA, mean πA (s u) * Q q M (Function.update s u 1) w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun u _ =>
        LinearAlgebra.Multilinear.IsMulti.const_mul _ (Q_isMultiB q M _))
  have h8 : LinearAlgebra.Multilinear.IsMulti (fun w : SB → Fin KB → F =>
      θB * ∑ v : SB, mean πB (w v) * Q q M s (Function.update w v 1)) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun v _ => Q_mutB_isMultiB q M πB s v)
  have h9 : LinearAlgebra.Multilinear.IsMulti
      (fun w : SB → Fin KB → F => ρ * ∑ p ∈ M, Q q (M.erase p) s w) :=
    LinearAlgebra.Multilinear.IsMulti.const_mul _
        (LinearAlgebra.Multilinear.IsMulti.sum _ _ fun p _ => Q_isMultiB q _ s)
  exact (((((((h1.add' h2).add' h3).add' h4).add' h5).add' h6).add' h7).add' h8).add' h9

theorem lhsQ_isMultiA (w : SB → Fin KB → F) (nA nB t : ℕ) :
    LinearAlgebra.Multilinear.IsMulti (fun s => dgQ θA θB ρ nA nB t * Q q M s w) :=
  LinearAlgebra.Multilinear.IsMulti.const_mul _ (Q_isMultiA q M w)

theorem lhsQ_isMultiB (s : SA → Fin KA → F) (nA nB t : ℕ) :
    LinearAlgebra.Multilinear.IsMulti (fun w => dgQ θA θB ρ nA nB t * Q q M s w) :=
  LinearAlgebra.Multilinear.IsMulti.const_mul _ (Q_isMultiB q M s)

section BasisValue

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)
include hθA hθB hρ hq

theorem basis_coalAA (hπA : ∑ i, πA i = 1) :
    (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k,
        Q q M (hadA k m fun u => (Pi.single (α u) 1 : Fin KA → F))
          (fun v => Pi.single (β v) 1))
      = ∑ i, ((xi M α β).a i : F)
          * ((((xi M α β).a i - 1 : ℕ) : F) * q ((xi M α β).dropA i)) := by
  rw [← sum_fiber_freeA M α β
    (fun i => (((xi M α β).a i - 1 : ℕ) : F) * q ((xi M α β).dropA i))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : (∑ m ∈ (freeA M).erase k,
        Q q M (hadA k m fun u => (Pi.single (α u) 1 : Fin KA → F))
          (fun v => Pi.single (β v) 1))
      = ∑ m ∈ (freeA M).erase k, if α m = α k then q ((xi M α β).dropA (α k)) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
    have hmf : m ∈ freeA M := (Finset.mem_erase.mp hm).2
    rw [Q_hadA_basis hθA hθB hρ hq M α β hπA (Ne.symm hmk) hmf]
    by_cases h : α k = α m
    · rw [ite_eq_left h, ite_eq_left h.symm, h]
    · rw [ite_eq_right h, ite_eq_right fun hc => h hc.symm]
  rw [h1, sum_ite_erase hk (fun m => α m = α k) rfl, xi_a]

theorem basis_coalAC (hπA : ∑ i, πA i = 1) :
    (∑ k ∈ freeA M, ∑ p ∈ M,
        Q q M (hadA p.1 k fun u => (Pi.single (α u) 1 : Fin KA → F))
          (fun v => Pi.single (β v) 1))
      = ∑ i, ((xi M α β).a i : F)
          * (((xi M α β).cRow i : F) * q ((xi M α β).dropA i)) := by
  rw [← sum_fiber_freeA M α β
    (fun i => ((xi M α β).cRow i : F) * q ((xi M α β).dropA i))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : (∑ p ∈ M, Q q M (hadA p.1 k fun u => (Pi.single (α u) 1 : Fin KA → F))
        (fun v => Pi.single (β v) 1))
      = ∑ p ∈ M, if α p.1 = α k then q ((xi M α β).dropA (α k)) else 0 :=
    Finset.sum_congr rfl fun p hp => by
      rw [Q_hadA_basis hθA hθB hρ hq M α β hπA (fst_ne_of_mem_freeA hk hp) hk]
  rw [h1, sum_ite_count M (fun p => α p.1 = α k), cRow_xi]

theorem basis_coalBB (hπB : ∑ j, πB j = 1) :
    (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l,
        Q q M (fun u => Pi.single (α u) 1)
          (hadB l n fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ j, ((xi M α β).b j : F)
          * ((((xi M α β).b j - 1 : ℕ) : F) * q ((xi M α β).dropB j)) := by
  rw [← sum_fiber_freeB M α β
    (fun j => (((xi M α β).b j - 1 : ℕ) : F) * q ((xi M α β).dropB j))]
  refine Finset.sum_congr rfl fun l hl => ?_
  have h1 : (∑ n ∈ (freeB M).erase l, Q q M (fun u => Pi.single (α u) 1)
        (hadB l n fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ n ∈ (freeB M).erase l, if β n = β l then q ((xi M α β).dropB (β l)) else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnl : n ≠ l := (Finset.mem_erase.mp hn).1
    have hnf : n ∈ freeB M := (Finset.mem_erase.mp hn).2
    rw [Q_hadB_basis hθA hθB hρ hq M α β hπB (Ne.symm hnl) hnf]
    by_cases h : β l = β n
    · rw [ite_eq_left h, ite_eq_left h.symm, h]
    · rw [ite_eq_right h, ite_eq_right fun hc => h hc.symm]
  rw [h1, sum_ite_erase hl (fun n => β n = β l) rfl, xi_b]

theorem basis_coalBC (hπB : ∑ j, πB j = 1) :
    (∑ l ∈ freeB M, ∑ p ∈ M,
        Q q M (fun u => Pi.single (α u) 1)
          (hadB p.2 l fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ j, ((xi M α β).b j : F)
          * (((xi M α β).cCol j : F) * q ((xi M α β).dropB j)) := by
  rw [← sum_fiber_freeB M α β
    (fun j => ((xi M α β).cCol j : F) * q ((xi M α β).dropB j))]
  refine Finset.sum_congr rfl fun l hl => ?_
  have h1 : (∑ p ∈ M, Q q M (fun u => Pi.single (α u) 1)
        (hadB p.2 l fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ p ∈ M, if β p.2 = β l then q ((xi M α β).dropB (β l)) else 0 :=
    Finset.sum_congr rfl fun p hp => by
      rw [Q_hadB_basis hθA hθB hρ hq M α β hπB (snd_ne_of_mem_freeB hl hp) hl]
  rw [h1, sum_ite_count M (fun p => β p.2 = β l), cCol_xi]

theorem basis_coalCC (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hM : IsMatching M) :
    (∑ p ∈ M, ∑ r ∈ M.erase p,
        Q q M (hadA p.1 r.1 fun u => (Pi.single (α u) 1 : Fin KA → F))
          (hadB p.2 r.2 fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ i, ∑ j, ((xi M α β).c i j : F)
          * ((((xi M α β).c i j - 1 : ℕ) : F) * q ((xi M α β).dropC i j)) := by
  rw [← sum_fiber_M M α β
    (fun i j => (((xi M α β).c i j - 1 : ℕ) : F) * q ((xi M α β).dropC i j))]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : (∑ r ∈ M.erase p,
        Q q M (hadA p.1 r.1 fun u => (Pi.single (α u) 1 : Fin KA → F))
          (hadB p.2 r.2 fun v => (Pi.single (β v) 1 : Fin KB → F)))
      = ∑ r ∈ M.erase p, if α r.1 = α p.1 ∧ β r.2 = β p.2
          then q ((xi M α β).dropC (α p.1) (β p.2)) else 0 := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hpr : p ≠ r := fun hc => (Finset.mem_erase.mp hr).1 hc.symm
    rw [Q_hadAB_basis hθA hθB hρ hq M α β hπA hπB hM hp (Finset.mem_erase.mp hr).2 hpr]
    by_cases hA : α p.1 = α r.1
    · by_cases hB : β p.2 = β r.2
      · rw [ite_eq_left (show α p.1 = α r.1 ∧ β p.2 = β r.2 from ⟨hA, hB⟩),
          ite_eq_left (show α r.1 = α p.1 ∧ β r.2 = β p.2 from ⟨hA.symm, hB.symm⟩), hA, hB]
      · rw [ite_eq_right (show ¬(α p.1 = α r.1 ∧ β p.2 = β r.2) from fun hc => hB hc.2),
          ite_eq_right (show ¬(α r.1 = α p.1 ∧ β r.2 = β p.2) from fun hc => hB hc.2.symm)]
    · rw [ite_eq_right (show ¬(α p.1 = α r.1 ∧ β p.2 = β r.2) from fun hc => hA hc.1),
        ite_eq_right (show ¬(α r.1 = α p.1 ∧ β r.2 = β p.2) from fun hc => hA hc.1.symm)]
  rw [h1, sum_ite_erase hp (fun r => α r.1 = α p.1 ∧ β r.2 = β p.2) ⟨rfl, rfl⟩, xi_c]

omit [LinearOrder F] [IsStrictOrderedRing F] hθA hθB hρ hq in
theorem basis_coalAB :
    (∑ k ∈ freeA M, ∑ l ∈ freeB M,
        Q q (insert (k, l) M) (fun u => (Pi.single (α u) 1 : Fin KA → F))
          (fun v => Pi.single (β v) 1))
      = ∑ i, ((xi M α β).a i : F)
          * ∑ j, ((xi M α β).b j : F) * q ((xi M α β).mergeAB i j) := by
  rw [← sum_fiber_freeA M α β
    (fun i => ∑ j, ((xi M α β).b j : F) * q ((xi M α β).mergeAB i j))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← sum_fiber_freeB M α β (fun j => q ((xi M α β).mergeAB (α k) j))]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Q_basis, xi_insert α β hk hl]

theorem basis_mutA (hπA : ∑ i, πA i = 1) (hM : IsMatching M) :
    (∑ u : SA, mean πA ((Pi.single (α u) 1 : Fin KA → F))
        * Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u 1)
          (fun v => Pi.single (β v) 1))
      = (∑ i, ((xi M α β).a i : F) * (πA i * q ((xi M α β).dropA i)))
        + ∑ i, ∑ j, ((xi M α β).c i j : F) * (πA i * q ((xi M α β).killA i j)) := by
  rw [sum_univ_split_A M, sum_domA_eq M hM]
  congr 1
  · rw [← sum_fiber_freeA M α β (fun i => πA i * q ((xi M α β).dropA i))]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [mean_single, Q_kill_freeA hθA hθB hρ hq M α β hπA hu]
  · rw [← sum_fiber_M M α β (fun i j => πA i * q ((xi M α β).killA i j))]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mean_single, Q_kill_domA hθA hθB hρ hq M α β hπA hM hp]

theorem basis_mutB (hπB : ∑ j, πB j = 1) (hM : IsMatching M) :
    (∑ v : SB, mean πB ((Pi.single (β v) 1 : Fin KB → F))
        * Q q M (fun u => Pi.single (α u) 1)
          (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v 1))
      = (∑ j, ((xi M α β).b j : F) * (πB j * q ((xi M α β).dropB j)))
        + ∑ i, ∑ j, ((xi M α β).c i j : F) * (πB j * q ((xi M α β).killB i j)) := by
  rw [sum_univ_split_B M, sum_domB_eq M hM]
  congr 1
  · rw [← sum_fiber_freeB M α β (fun j => πB j * q ((xi M α β).dropB j))]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [mean_single, Q_kill_freeB hθA hθB hρ hq M α β hπB hv]
  · rw [← sum_fiber_M M α β (fun i j => πB j * q ((xi M α β).killB i j))]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [mean_single, Q_kill_domB hθA hθB hρ hq M α β hπB hM hp]

omit [LinearOrder F] [IsStrictOrderedRing F] hθA hθB hρ hq in
theorem basis_rec (hM : IsMatching M) :
    (∑ p ∈ M, Q q (M.erase p) (fun u => (Pi.single (α u) 1 : Fin KA → F))
        (fun v => Pi.single (β v) 1))
      = ∑ i, ∑ j, ((xi M α β).c i j : F) * q ((xi M α β).split i j) := by
  rw [← sum_fiber_M M α β (fun i j => q ((xi M α β).split i j))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Q_basis, xi_erase α β hM hp]

end BasisValue

section Main

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem dgQ_eq_diag (hM : IsMatching M) :
    dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card = LinearAlgebra.Recursion.diag θA θB ρ
        (xi M α β) := by
  have hn : (xi M α β).n = Fintype.card SA + Fintype.card SB - M.card := by
    have h := n_xi M α β hM
    omega
  simp only [dgQ, LinearAlgebra.Recursion.diag, hn, nA_xi M α β hM, nB_xi M α β hM, t_xi]

include hθA hθB hρ hq

theorem rhsQ_basis (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hM : IsMatching M) :
    rhsQ θA θB ρ πA πB q M (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1)
      = rhs θA θB ρ πA πB q (xi M α β) := by
  have g1 : (∑ i, ((xi M α β).a i : F)
        * ((((xi M α β).a i - 1 : ℕ) : F) * q ((xi M α β).dropA i)))
      + 2 * (∑ i, ((xi M α β).a i : F)
        * (((xi M α β).cRow i : F) * q ((xi M α β).dropA i)))
      = ∑ i, (((xi M α β).coalA i : ℕ) : F) * q ((xi M α β).dropA i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Config.coalA]
    push_cast
    ring
  have g2 : (∑ j, ((xi M α β).b j : F)
        * ((((xi M α β).b j - 1 : ℕ) : F) * q ((xi M α β).dropB j)))
      + 2 * (∑ j, ((xi M α β).b j : F)
        * (((xi M α β).cCol j : F) * q ((xi M α β).dropB j)))
      = ∑ j, (((xi M α β).coalB j : ℕ) : F) * q ((xi M α β).dropB j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Config.coalB]
    push_cast
    ring
  have g3 : (∑ i, ∑ j, ((xi M α β).c i j : F)
        * ((((xi M α β).c i j - 1 : ℕ) : F) * q ((xi M α β).dropC i j)))
      = ∑ i, ∑ j, (((xi M α β).coalC i j : ℕ) : F) * q ((xi M α β).dropC i j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [Config.coalC]; push_cast; ring
  have g4 : 2 * (∑ i, ((xi M α β).a i : F)
        * ∑ j, ((xi M α β).b j : F) * q ((xi M α β).mergeAB i j))
      = ∑ i, ∑ j, (((xi M α β).coalAB i j : ℕ) : F) * q ((xi M α β).mergeAB i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Config.coalAB]
    push_cast
    ring
  have g5 : (∑ i, ((xi M α β).a i : F) * (πA i * q ((xi M α β).dropA i)))
      + (∑ i, ∑ j, ((xi M α β).c i j : F) * (πA i * q ((xi M α β).killA i j)))
      = ∑ i, πA i * (((xi M α β).a i : F) * q ((xi M α β).dropA i)
          + ∑ j, ((xi M α β).c i j : F) * q ((xi M α β).killA i j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have g6 : (∑ j, ((xi M α β).b j : F) * (πB j * q ((xi M α β).dropB j)))
      + (∑ i, ∑ j, ((xi M α β).c i j : F) * (πB j * q ((xi M α β).killB i j)))
      = ∑ j, πB j * (((xi M α β).b j : F) * q ((xi M α β).dropB j)
          + ∑ i, ((xi M α β).c i j : F) * q ((xi M α β).killB i j)) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp only [rhsQ, rhs]
  rw [basis_coalAA hθA hθB hρ hq M α β hπA, basis_coalAC hθA hθB hρ hq M α β hπA,
    basis_coalBB hθA hθB hρ hq M α β hπB, basis_coalBC hθA hθB hρ hq M α β hπB,
    basis_coalCC hθA hθB hρ hq M α β hπA hπB hM, basis_coalAB (q := q) M α β,
    basis_mutA hθA hθB hρ hq M α β hπA hM, basis_mutB hθA hθB hρ hq M α β hπB hM,
    basis_rec (q := q) M α β hM, ← g1, ← g2, ← g3, ← g4, ← g5, ← g6]
  ring

theorem dgQ_mul_Q_eq_rhsQ (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hM : IsMatching M)
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) :
    dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card * Q q M s w
      = rhsQ θA θB ρ πA πB q M s w := by
  refine LinearAlgebra.Multilinear.eq_of_basis
    (G := fun s w => dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card * Q q M s w)
    (H := fun s w => rhsQ θA θB ρ πA πB q M s w)
    (fun w => lhsQ_isMultiA θA θB ρ q M w _ _ _)
    (fun s => lhsQ_isMultiB θA θB ρ q M s _ _ _)
    (fun w => rhsQ_isMultiA θA θB ρ πA πB q M hM w)
    (fun s => rhsQ_isMultiB θA θB ρ πA πB q M hM s) ?_ s w
  intro α β
  rw [Q_basis, dgQ_eq_diag M α β hM, rhsQ_basis hθA hθB hρ hq M α β hπA hπB hM]
  exact recursion_all hθA hθB hρ hq (xi M α β)

end Main

end Statement

end Rhone.Probability.Multilinear
