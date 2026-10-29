/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuild

/-! # Successful lineage lookups and successor records when rebuilding from an event trace -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem rebuildUIDIndex_live (s : State) (hs : Valid s) (i : Fin s.2.2.1) :
    rebuildUIDIndex s (s.2.2.2 i).1 = i.val := by
  classical
  unfold rebuildUIDIndex
  generalize he : (List.finRange s.2.2.1).find?
    (fun j => decide ((s.2.2.2 j).1 = (s.2.2.2 i).1)) = o
  cases o with
  | none =>
    have hex : ((List.finRange s.2.2.1).find?
        (fun j => decide ((s.2.2.2 j).1 = (s.2.2.2 i).1))).isSome := by
      exact List.find?_isSome.mpr ⟨i, by simp, by simp⟩
    simp [he] at hex
  | some j =>
    have hji : (s.2.2.2 j).1 = (s.2.2.2 i).1 := by
      simpa using List.find?_some he
    have hij : j = i := hs.2.2.2 hji
    exact congrArg Fin.val hij

theorem rebuildSampleUID_eq {N : ℕ} (f : Fin N → ℕ) (c : Finset (Fin N))
    (hc : c.Nonempty) (a : ℕ) (hf : ∀ i ∈ c, f i = a) :
    rebuildSampleUID f c = a := by
  classical
  unfold rebuildSampleUID
  generalize he : (List.finRange N).find? (fun i => decide (i ∈ c)) = o
  cases o with
  | none =>
    obtain ⟨i, hi⟩ := hc
    have hex : ((List.finRange N).find? (fun i => decide (i ∈ c))).isSome :=
      List.find?_isSome.mpr ⟨i, by simp, by simpa using hi⟩
    simp [he] at hex
  | some i =>
    exact hf i (by simpa using List.find?_some he)

theorem rebuildCoal_live {N : ℕ} (z : RebuildState N) (hz : Valid z.1.1)
    (t : ℝ) (i j : Fin z.1.1.2.2.1) (hij : i.val < j.val) :
    (rebuildCoal z t (z.1.1.2.2.2 i).1 (z.1.1.2.2.2 j).1).1 =
      (atTime t (coalSuccessor z.1.1 i j), (t, .inr (.inl (i.val, j.val)))) := by
  simp only [rebuildCoal, rebuildUIDIndex_live z.1.1 hz,
    min_eq_left hij.le, max_eq_right hij.le, coalSuccessorNat,
    dite_eq_left i.isLt, dite_eq_left j.isLt]

theorem rebuildSplit_live {N : ℕ} (z : RebuildState N) (hz : Valid z.1.1)
    (t x : ℝ) (i : Fin z.1.1.2.2.1) :
    (rebuildSplit z t x (z.1.1.2.2.2 i).1).1 =
      (atTime t (splitSuccessor z.1.1 i x), (t, .inr (.inr (i.val, x)))) := by
  simp only [rebuildSplit, rebuildUIDIndex_live z.1.1 hz, dite_eq_left i.isLt]

end Rhone.Coalescent.SmcPrime
