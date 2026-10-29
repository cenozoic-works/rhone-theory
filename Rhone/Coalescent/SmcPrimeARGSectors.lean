/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGFewSplitsCompletion
public import Rhone.Coalescent.SmcPrimeARGZeroSectorLaw
public import Rhone.Coalescent.SmcPrimeEventTwoSplits

/-! # Zero-split and one-split partition of unrestricted ARG paths -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem arg_noSplit_event_iff (z : AugmentedState) :
    z ∈ argNoSplitEvent ↔ z.2.2 ∉ splitSet := by
  cases he : z.2.2 with
  | inl u => simp [argNoSplitEvent, he, genealogyEventCode, splitSet]
  | inr a => cases a <;> simp [argNoSplitEvent, he, genealogyEventCode, splitSet]

theorem not_eventTwoSplits_iff_unique (ω : EventPath) : ω ∉ eventTwoSplits ↔
    ∀ i j, (ω (i + 1)).2.2 ∈ splitSet → (ω (j + 1)).2.2 ∈ splitSet → i = j := by
  constructor
  · intro hn i j hi hj
    by_contra he
    rcases lt_or_gt_of_ne he with hij | hji
    · exact hn ⟨i, j, hij, hi, hj⟩
    · exact hn ⟨j, i, hji, hj, hi⟩
  · rintro hu ⟨i, j, hij, hi, hj⟩
    exact (Nat.ne_of_lt hij) (hu i j hi hj)

theorem arg_path_one_split_prefix (N : ℕ) (hN : 0 < N) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hstep : ∀ k, ARGTransition (ω k, ω (k + 1)))
    (huniq : ∀ i j, (ω (i + 1)).2.2 ∈ splitSet → (ω (j + 1)).2.2 ∈ splitSet → i = j)
    (hex : ∃ c, (ω (c + 1)).2.2 ∈ splitSet) :
    (fun k : Finset.Iic (N + 1) => ω k.val) ∈ oneSplitPrefixSector N := by
  classical
  have hfinal := arg_path_few_splits_terminal N hN ω hinit hstep huniq
  obtain ⟨c, hc⟩ := hex
  have hcb : c < N + 1 := by
    by_contra hn
    have he := arg_path_stopped_event ω hstep (N + 1) c (by omega) hfinal.le
    rw [he] at hc
    cases hc
  have hcount : finiteARGSplitCount ω (N + 1) = 1 := by
    have hlo := Finset.single_le_sum (s := Finset.range (N + 1))
      (f := fun l => if (ω (l + 1)).2.2 ∈ splitSet then (1 : ℕ) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hcb)
    rw [ite_eq_left hc] at hlo
    have hhi := arg_path_splitCount_le_one ω huniq (N + 1)
    exact le_antisymm hhi hlo
  have hstops : finiteARGIdleCount ω (N + 1) = 0 := by
    have hb := arg_path_count_balance N ω hinit hstep (N + 1)
    rw [hfinal, hcount] at hb
    omega
  have hnostop (k : Fin (N + 1)) : (ω (k.val + 1)).2.2 ≠ .inl () := by
    intro he
    have hlo := Finset.single_le_sum (s := Finset.range (N + 1))
      (f := fun l => if (ω (l + 1)).2.2 = .inl () then (1 : ℕ) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr k.isLt)
    rw [ite_eq_left he] at hlo
    change 1 ≤ finiteARGIdleCount ω (N + 1) at hlo
    omega
  refine ⟨⟨⟨c, hcb⟩, hc, ?_⟩, hfinal⟩
  intro k hk
  have hns : (ω (k.val + 1)).2.2 ∉ splitSet := by
    intro he
    exact hk (Fin.ext (huniq k.val c he hc))
  rcases (hstep k.val).count_cases with ⟨he, _, _⟩ | ⟨he, _, _⟩ | ⟨he, _, _⟩
  · exact False.elim (hnostop k he)
  · exact he
  · exact False.elim (hns he)

theorem arg_path_one_prefix_unique (N : ℕ) (ω : EventPath)
    (hstep : ∀ k, ARGTransition (ω k, ω (k + 1)))
    (hp : (fun k : Finset.Iic (N + 1) => ω k.val) ∈ oneSplitPrefixSector N) :
    ∀ i j, (ω (i + 1)).2.2 ∈ splitSet → (ω (j + 1)).2.2 ∈ splitSet → i = j := by
  obtain ⟨⟨c, _, hother⟩, hfinal⟩ := hp
  have hcut (i : ℕ) (hi : (ω (i + 1)).2.2 ∈ splitSet) : i = c.val := by
    by_cases hib : i < N + 1
    · by_contra hne
      have hcoal := hother ⟨i, hib⟩ (fun he => hne (congrArg Fin.val he))
      change (ω (i + 1)).2.2 ∈ coalSet at hcoal
      cases he : (ω (i + 1)).2.2 with
      | inl u => rw [he] at hi; cases hi
      | inr a => cases a with
        | inl ij => rw [he] at hi; cases hi
        | inr ix => rw [he] at hcoal; cases hcoal
    · have hs : (ω (N + 1)).1.2.2.1 ≤ 1 := le_of_eq hfinal
      have he := arg_path_stopped_event ω hstep (N + 1) i (by omega) hs
      rw [he] at hi
      cases hi
  intro i j hi hj
  exact (hcut i hi).trans (hcut j hj).symm

theorem arg_path_sector_partition (N : ℕ) (hN : 0 < N) (ω : EventPath)
    (hinit : ω 0 = (initialState N, (0, .inl ())))
    (hstep : ∀ k, ARGTransition (ω k, ω (k + 1))) :
    ω ∉ eventTwoSplits ↔ ω ∈ argNoSplitPathSet ∨
      (fun k : Finset.Iic (N + 1) => ω k.val) ∈ oneSplitPrefixSector N := by
  rw [not_eventTwoSplits_iff_unique]
  constructor
  · intro hu
    by_cases hz : ω ∈ argNoSplitPathSet
    · exact Or.inl hz
    · apply Or.inr
      apply arg_path_one_split_prefix N hN ω (congrArg Prod.fst hinit) hstep hu
      change ¬ ∀ k, ω k ∈ argNoSplitEvent at hz
      obtain ⟨k, hk⟩ := not_forall.mp hz
      cases k with
      | zero => simp [hinit, argNoSplitEvent, genealogyEventCode] at hk
      | succ k => exact ⟨k, not_not.mp ((arg_noSplit_event_iff _).not.mp hk)⟩
  · rintro (hz | hp)
    · intro i j hi _
      exact False.elim ((arg_noSplit_event_iff _).mp (hz (i + 1)) hi)
    · exact arg_path_one_prefix_unique N ω hstep hp

end Rhone.Coalescent.SmcPrime
