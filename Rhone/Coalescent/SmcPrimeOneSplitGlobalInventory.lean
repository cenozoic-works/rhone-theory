/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitOldPairInventory
public import Rhone.Coalescent.SmcPrimeOneSplitUnaryInventory
public import Rhone.Coalescent.SmcPrimeOneSplitTransitionCases

/-! # The extracted old-to-left lineage inventory along the ARG prefix -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_detached_none_pair {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (hd : z.detached = none)
    (he : next.2.2 ∈ coalSet) : (extractionStep z pre next).detached = none := by
  classical
  cases hev : next.2.2 with
  | inl u => rw [hev] at he; cases he
  | inr a =>
    cases a with
    | inl ij => simp only [extractionStep, hev, hd, reduceCtorEq, false_and,
        exists_false, ite_false]
    | inr ix => rw [hev] at he; cases he

theorem extractionRun_detached_before_split (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (s : Fin (N + 1))
    (hcoal : ∀ k : Fin (N + 1), k ≠ s →
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2 ∈ coalSet)
    (n : ℕ) (hn : n ≤ s.val) : (extractionRun N h n).detached = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [extractionRun_succ N h n (by have := s.isLt; omega)]
    apply extractionStep_detached_none_pair _ _ _ (ih (by omega))
    apply hcoal ⟨n, by have := s.isLt; omega⟩
    intro he
    have heval := congrArg Fin.val he
    change n = s.val at heval
    omega

theorem extractionRun_inventory (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n ≤ N + 1) :
    ExtractionInventory (extractionRun N h n)
      (h ⟨n, Finset.mem_Iic.mpr hn⟩).1 := by
  obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
  induction n with
  | zero =>
    rw [extractionRun_zero, hs.1]
    exact extractionInitial_inventory N
  | succ n ih =>
    have hlt : n < N + 1 := by omega
    let hk : Fin (N + 1) := ⟨n, hlt⟩
    have hpre := hs.2.1 ⟨n, Finset.mem_Iic.mpr (by omega)⟩
    have hnext := hs.2.1 ⟨n + 1, Finset.mem_Iic.mpr hn⟩
    have htrans := hs.2.2.1 hk
    rw [extractionRun_succ N h n hlt]
    by_cases he : hk = s
    · have hsplit' : (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩).2.2 ∈ splitSet := by
        simpa only [← he] using hsplit
      obtain ⟨i, x, hx, _, hev, hnxt, _⟩ := htrans.split_case hpre hsplit'
      apply extractionStep_split_inventory _ _ _ (ih (by omega)) hpre _ i x hx hev hnxt
      apply extractionRun_detached_before_split N h s hcoal n
      exact le_of_eq (congrArg Fin.val he)
    · obtain ⟨i, j, hij, hev, hnxt, _⟩ := htrans.coal_case (hcoal hk he)
      by_cases hd : (extractionRun N h n).detached = some ((h
          ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 i).1 ∨
          (extractionRun N h n).detached = some ((h
          ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.2 j).1
      · exact extractionStep_attachment_inventory _ _ _ (ih (by omega))
          hpre i j hij hev hnxt hd
      · exact extractionStep_old_pair_inventory _ _ _ (ih (by omega))
          hpre hnext.1 i j hij hev hnxt
          (fun hi => hd (Or.inl hi)) (fun hj => hd (Or.inr hj))

end Rhone.Coalescent.SmcPrime
