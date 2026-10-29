/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Tracked
public import Rhone.Coalescent.SmcSupport.ContactClosure
public import Rhone.Coalescent.SmcSupport.SamplerValidity
public import Rhone.Coalescent.SmcSupport.Selector

/-! # Structural support of the capped-phase sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

def Good (z : TrackedState) : Prop :=
  match z.2.1 with
  | .zero => Valid z.1 ∧ AllMaterials FullAtoms z.1 ∧ 1 ≤ z.1.2.2.1
  | .one => Valid z.1 ∧
      (∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) ∧ 1 ≤ z.1.2.2.1
  | .two => True

theorem trackedInitial_good (n : ℕ) (hn : 0 < n) : Good (trackedInitial n) := by
  refine ⟨initialState_valid n, ?_, ?_⟩
  · intro i j
    rfl
  · exact hn

theorem trackedSampleStep_good (mode : Mode) (R : ℝ) (z : TrackedState)
    (hz : Good z) (u : Noise) (hu0 : 0 ≤ u 0) (hu1 : u 0 < 1)
    (ht0 : 0 ≤ u 1) (ht1 : u 1 ≤ 1) (hc0 : 0 < u 2) (hc1 : u 2 < 1) :
    Good (trackedSampleStep mode R z u) := by
  classical
  rcases z with ⟨s, p, last⟩
  cases p with
  | two => simp [trackedSampleStep, Good, advancePhase]
  | zero =>
    rcases hz with ⟨hs, hf, hm⟩
    change 1 ≤ s.2.2.1 at hm
    have htime := sampler_clock_nonneg mode R s hs u ht0 ht1
    unfold trackedSampleStep sampleStep
    split_ifs with hstop
    · exact ⟨hs, hf, hm⟩
    · change ¬ (s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0) at hstop
      have hn : 2 ≤ s.2.2.1 := by omega
      have htotal : 0 < totalRate mode R s := by
        exact lt_of_le_of_ne (by positivity) (Ne.symm (fun h => hstop (Or.inr h)))
      obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive mode R s u hu0 hu1 htotal
      rw [ha]
      cases a with
      | inl ij =>
        have hcount := coalSuccessor_count s ij.1 ij.2
          (positive_pair_order mode R s ij hp)
        refine ⟨atTime_valid _ (coalSuccessor_valid s hs ij.1 ij.2) _ htime, ?_, ?_⟩
        · exact coalSuccessor_all FullAtoms s hf
            (fun a b ha hb => mergeMaterial_full a b ha hb) ij.1 ij.2
        · change 1 ≤ (coalSuccessor s ij.1 ij.2).2.2.1
          omega
      | inr i =>
        obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ 0 1 (by norm_num) (hf i)
        have hlen : hullLength (s.2.2.2 i).2 = 1 := by simp [hullLength, hlo, hhi]
        simp only [hlo, hlen, zero_add, one_mul]
        refine ⟨atTime_valid _ (splitSuccessor_full_valid s hs hf i (u 2) hc0 hc1)
          _ htime, ?_, ?_⟩
        · exact splitFull_contacts s hf i (u 2) hc0 hc1
        · change 1 ≤ (splitSuccessor s i (u 2)).2.2.1
          rw [splitSuccessor_count]
          omega
  | one =>
    rcases hz with ⟨hs, hf, hm⟩
    change 1 ≤ s.2.2.1 at hm
    have htime := sampler_clock_nonneg mode R s hs u ht0 ht1
    unfold trackedSampleStep sampleStep
    split_ifs with hstop
    · exact ⟨hs, hf, hm⟩
    · change ¬ (s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0) at hstop
      have hn : 2 ≤ s.2.2.1 := by omega
      have htotal : 0 < totalRate mode R s := by
        exact lt_of_le_of_ne (by positivity) (Ne.symm (fun h => hstop (Or.inr h)))
      obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive mode R s u hu0 hu1 htotal
      rw [ha]
      cases a with
      | inl ij =>
        have hcount := coalSuccessor_count s ij.1 ij.2
          (positive_pair_order mode R s ij hp)
        refine ⟨atTime_valid _ (coalSuccessor_valid s hs ij.1 ij.2) _ htime, ?_, ?_⟩
        · exact coalSuccessor_contacts s (by omega) hf ij.1 ij.2
        · change 1 ≤ (coalSuccessor s ij.1 ij.2).2.2.1
          omega
      | inr i => trivial

end Rhone.Coalescent.SmcSupport
