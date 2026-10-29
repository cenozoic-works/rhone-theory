/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatInjective
public import Rhone.Coalescent.SmcSupport.SamplerValidity

/-! # Valid flat coordinates run through supported ARG transitions to supported prefixes -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem argFlatValid_run_valid (N : ℕ) (p : ARGFlatCoordinate N) (hp : argFlatValid N p)
    (k : ℕ) (hk : k ≤ N + 1) :
    Valid (argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 k).1 := by
  induction k with
  | zero => exact initialState_valid N
  | succ k ih =>
    have hkn : k < N + 1 := by omega
    let j : Fin (N + 1) := ⟨k, hkn⟩
    let z := argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 k
    have hz : Valid z.1 := ih (by omega)
    have hj := hp.2.2.1 j
    change 1 < z.1.2.2.1 ∧ argFlatActionValid z.1 (p.1 j) ∧ z.1.1 < p.2.1 j at hj
    have ht : 0 ≤ p.2.1 j := hz.1.trans hj.2.2.le
    rw [argFlatRun, dite_eq_left hkn]
    change Valid (argFlatActionStep z (p.1 j) (p.2.1 j) p.2.2).1
    cases ha : p.1 j with
    | inl ij =>
      have hidx : ij.1 < ij.2 ∧ ij.2 < z.1.2.2.1 := by
        simpa only [ha, argFlatActionValid] using hj.2.1
      simp only [argFlatActionStep, coalSuccessorNat,
        dite_eq_left (hidx.1.trans hidx.2), dite_eq_left hidx.2]
      exact atTime_valid _ (coalSuccessor_valid z.1 hz _ _) _ ht
    | inr i =>
      have hi : i < z.1.2.2.1 := by
        simpa only [ha, argFlatActionValid] using hj.2.1
      obtain ⟨s, ⟨a, hs⟩, hpair⟩ := hp.1
      have hjs : j = s := by
        by_contra hne
        obtain ⟨ij, hij⟩ := hpair j hne
        rw [ha] at hij
        cases hij
      subst s
      have hzero := argFlatRun_preSplit_zeroSplit N p.1 p.2.1 p.2.2 j
        (fun b hb => hpair b (by intro he; have := congrArg Fin.val he; omega)) k le_rfl
      simp only [argFlatActionStep, splitSuccessorNat, dite_eq_left hi]
      exact atTime_valid _ (splitSuccessor_full_valid z.1 hz (zeroSplit_full hzero)
        ⟨i, hi⟩ _ hp.2.1.1 hp.2.1.2) _ ht

theorem argFlatValid_transition (N : ℕ) (p : ARGFlatCoordinate N) (hp : argFlatValid N p)
    (j : Fin (N + 1)) :
    ARGTransition
      (argFlatRebuild N p ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩,
        argFlatRebuild N p ⟨j.val + 1, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩) := by
  let z := argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 j.val
  have hj := hp.2.2.1 j
  change 1 < z.1.2.2.1 ∧ argFlatActionValid z.1 (p.1 j) ∧ z.1.1 < p.2.1 j at hj
  have hm : 2 ≤ z.1.2.2.1 := by omega
  change ARGTransition (z, argFlatRun (initialState N, (0, .inl ()))
    p.1 p.2.1 p.2.2 (j.val + 1))
  rw [argFlatRun, dite_eq_left j.isLt]
  change ARGTransition (z, argFlatActionStep z (p.1 j) (p.2.1 j) p.2.2)
  cases ha : p.1 j with
  | inl ij =>
    have hidx : ij.1 < ij.2 ∧ ij.2 < z.1.2.2.1 := by
      simpa only [ha, argFlatActionValid] using hj.2.1
    apply Or.inl
    rw [KingmanTransition, ite_eq_left hm]
    exact ⟨ij, hidx.1, hidx.2, rfl, rfl, hj.2.2⟩
  | inr i =>
    have hi : i < z.1.2.2.1 := by
      simpa only [ha, argFlatActionValid] using hj.2.1
    obtain ⟨s, ⟨a, hs⟩, hpair⟩ := hp.1
    have hjs : j = s := by
      by_contra hne
      obtain ⟨ij, hij⟩ := hpair j hne
      rw [ha] at hij
      cases hij
    subst s
    obtain ⟨hlo,hhi⟩ := argFlatRun_split_hull N p.1 p.2.1 p.2.2 j hpair i hi
    change lineageHullEndpoint false z.1 i = 0 at hlo
    change lineageHullEndpoint true z.1 i = 1 at hhi
    apply Or.inr
    refine ⟨hm, i, hi, rfl, ?_, ?_, rfl, hj.2.2⟩
    · simpa only [argFlatActionStep, genealogyEventCode, hlo] using hp.2.1.1
    · simpa only [argFlatActionStep, genealogyEventCode, hhi] using hp.2.1.2

theorem argFlatValid_prefix_supported (N : ℕ) (p : ARGFlatCoordinate N)
    (hp : argFlatValid N p) : OneSplitPrefixSupported N (argFlatRebuild N p) := by
  refine ⟨rfl, ?_, argFlatValid_transition N p hp, ?_, ?_⟩
  · intro k
    exact argFlatValid_run_valid N p hp k.val (Finset.mem_Iic.mp k.property)
  · intro k
    by_cases hk : k.val = 0
    · simp only [argFlatRebuild, hk, argFlatRun]
      rfl
    · have hpos : 0 < k.val := by omega
      let j : Fin (N + 1) := ⟨k.val - 1, by have := Finset.mem_Iic.mp k.property; omega⟩
      have he : k.val = j.val + 1 := by dsimp [j]; omega
      unfold argFlatRebuild
      rw [he, argFlatRun, dite_eq_left j.isLt]
      cases p.1 j <;> rfl
  · apply argWordSector_implies_prefix N _ p.1 hp.1 _ hp.2.2.2
    intro j
    simp only [argFiniteWord_eval, argActionFiber, Set.mem_ofPred_eq, argFlatRebuild_event]
    cases p.1 j <;> rfl
end Rhone.Coalescent.SmcPrime
