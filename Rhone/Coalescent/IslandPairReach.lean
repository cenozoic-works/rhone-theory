/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairRatesSum

/-! # Labelled island pair absorption is reachable in at most two jumps -/

@[expose] public section
namespace Rhone.Coalescent.IslandPair
open Finset

theorem rate_some_pos (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) :
    0 < (chain d m c hm.le hc.le).rate (some (a,b)) := by
  rw [rate_some d hd]
  split_ifs <;> linarith

theorem jump_coalesce_pos (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a : Fin d) :
    0 < (chain d m c hm.le hc.le).jumpChain.P (some (a,a)) none := by
  rw [Rhone.MarkovChain.RateChain.jumpChain_P_of_ne
    (ne_of_gt (rate_some_pos d hd m c hm hc a a)) (by simp)]
  have hq : (chain d m c hm.le hc.le).Q (some (a,a)) none = c := by
    simp [chain, generator, eventRate]
  rw [hq]
  exact div_pos hc (rate_some_pos d hd m c hm hc a a)

theorem jump_meet_pos (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) (hab : a ≠ b) :
    0 < (chain d m c hm.le hc.le).jumpChain.P (some (a,b)) (some (b,b)) := by
  have hst : (some (a,b) : State d) ≠ some (b,b) := by
    intro h
    exact hab (Prod.mk.inj (Option.some.inj h)).1
  rw [Rhone.MarkovChain.RateChain.jumpChain_P_of_ne
    (ne_of_gt (rate_some_pos d hd m c hm hc a b)) hst]
  have hq : (chain d m c hm.le hc.le).Q (some (a,b)) (some (b,b)) =
      destinationRate d m := by
    simp [chain, generator, eventRate, hab]
  rw [hq]
  have hk : 0 < destinationRate d m := by
    apply div_pos hm
    exact Nat.cast_pos.mpr (show 0 < d - 1 by omega)
  exact div_pos hk (rate_some_pos d hd m c hm hc a b)

theorem reaches_within_two (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (s : State d) :
    ∃ n, n ≤ 2 ∧ 0 < (chain d m c hm.le hc.le).jumpChain.stepN n s none := by
  let R := chain d m c hm.le hc.le
  cases s with
  | none =>
    refine ⟨0, by omega, ?_⟩
    simp [Rhone.MarkovChain.FinChain.stepN_zero]
  | some p =>
    rcases p with ⟨a,b⟩
    by_cases hab : a = b
    · subst b
      refine ⟨1, by omega, ?_⟩
      simpa only [Rhone.MarkovChain.FinChain.stepN_one] using jump_coalesce_pos d hd m c hm hc a
    · refine ⟨2, le_rfl, ?_⟩
      rw [show 2 = 1 + 1 from rfl, Rhone.MarkovChain.FinChain.stepN_add_apply]
      have hterm : 0 < R.jumpChain.stepN 1 (some (a,b)) (some (b,b)) *
          R.jumpChain.stepN 1 (some (b,b)) none := by
        simpa only [Rhone.MarkovChain.FinChain.stepN_one] using
          mul_pos (jump_meet_pos d hd m c hm hc a b hab)
            (jump_coalesce_pos d hd m c hm hc b)
      apply lt_of_lt_of_le hterm
      change R.jumpChain.stepN 1 (some (a,b)) (some (b,b)) *
          R.jumpChain.stepN 1 (some (b,b)) none ≤
        ∑ z, R.jumpChain.stepN 1 (some (a,b)) z * R.jumpChain.stepN 1 z none
      exact single_le_sum (s := univ) (a := some (b,b))
        (f := fun z => R.jumpChain.stepN 1 (some (a,b)) z * R.jumpChain.stepN 1 z none)
        (fun z _ => mul_nonneg (R.jumpChain.stepN_nonneg 1 _ z)
          (R.jumpChain.stepN_nonneg 1 z _)) (mem_univ _)

theorem reaches (d : Nat) (hd : 2 ≤ d) (m c : Real) (hm : 0 < m) (hc : 0 < c) :
    (chain d m c hm.le hc.le).jumpChain.Reaches {none} := by
  intro s
  obtain ⟨n, hn, hpos⟩ := reaches_within_two d hd m c hm hc s
  exact ⟨n, none, mem_singleton_self _, hpos⟩

theorem absorbing_set (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    (chain d m c hm hc).jumpChain.IsAbsorbingSet {none} := by
  intro s hs
  have hs0 : s = none := mem_singleton.mp hs
  subst s
  exact none_absorbing d m c hm hc

end Rhone.Coalescent.IslandPair
