/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGToEtaCoordinates
public import Rhone.Coalescent.SmcPrimeOneSplitMarkerClocks
public import Rhone.Coalescent.SmcPrimeOneSplitHistorySupport
/-! # Decoding old pair histories from finite flat coordinates -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess
theorem oldPairHistory_decoded (N : ℕ) (hN : 0 < N) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h)
    (hc : ∀ k, (h k).2.1 = (h k).1.1) :
    oldPairHistory N (etaHistoryPairWord N h)
      (fun j => (h ⟨j.val + 1, by have := j.isLt; omega⟩).1.1) = h := by
  have hr : ∀ k, ∀ hk : k < N,
      argFlatRun (initialState N, (0, .inl ()))
        (fun j => .inl (etaHistoryPairWord N h j))
        (fun j => (h ⟨j.val + 1, by have := j.isLt; omega⟩).1.1) 0 k = h ⟨k,hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact (hs.2.1 hk).symm
    | succ k ih =>
      intro hk
      have hk' : k < N - 1 := by omega
      let j : Fin (N - 1) := ⟨k,hk'⟩
      have hp := hs.2.2 j
      have hcount := (hs.1 (⟨k,by omega⟩ : Fin N)).2
      change (h ⟨k,by omega⟩).1.2.2.1 = N - k at hcount
      have htwo : 2 ≤ (h ⟨k,by omega⟩).1.2.2.1 := by
        rw [hcount]; omega
      unfold KingmanTransition at hp
      rw [ite_eq_left htwo] at hp
      obtain ⟨ij,hij,hbound,he,ht,hlt⟩ := hp
      change (h ⟨k+1,hk⟩).2.2 = .inr (.inl ij) at he
      have hw : etaHistoryPairWord N h j = ij := by
        change ((genealogyEventCode (h ⟨k+1,hk⟩).2.2).2.1,
          (genealogyEventCode (h ⟨k+1,hk⟩).2.2).2.2.1) = ij
        rw [he]
        rfl
      rw [argFlatRun, dite_eq_left hk', ih (by omega)]
      change argFlatActionStep (h ⟨k,by omega⟩)
        (.inl (etaHistoryPairWord N h j)) (h ⟨k+1,hk⟩).1.1 0 = h ⟨k+1,hk⟩
      rw [hw]
      apply Prod.ext
      · exact ht.symm
      · apply Prod.ext
        · exact (hc _).symm
        · exact he.symm
  funext k
  exact hr k.val k.isLt
end Rhone.Coalescent.SmcPrime
