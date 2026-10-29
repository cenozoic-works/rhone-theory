/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeHistoryTrace
/-! # Extend a ranked Kingman history by one merger and read off its endpoint -/
@[expose] public section
namespace Rhone.Combinatorics
noncomputable def historyAppend {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → (h : RankedForestHistory F t) →
    (G : Finset (Finset L)) → G ∈ ADR11.merges (historyEnd F t h) →
    RankedForestHistory F (t+1)
  | 0, _, G, hG => ⟨⟨G, hG⟩, PUnit.unit⟩
  | t+1, h, G, hG => ⟨h.1, historyAppend h.1.1 t h.2 G hG⟩
theorem historyAt_historyAppend {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : RankedForestHistory F t)
    (G : Finset (Finset L)) (hG : G ∈ ADR11.merges (historyEnd F t h))
    (k : ℕ) (hk : k ≤ t) :
    historyAt F (t+1) (historyAppend F t h G hG) k = historyAt F t h k := by
  induction t generalizing F k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    rfl
  | succ t ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih h.1.1 h.2 hG k (by omega)
theorem historyEnd_historyAppend {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : RankedForestHistory F t)
    (G : Finset (Finset L)) (hG : G ∈ ADR11.merges (historyEnd F t h)) :
    historyEnd F (t+1) (historyAppend F t h G hG) = G := by
  induction t generalizing F with
  | zero => rfl
  | succ t ih => exact ih h.1.1 h.2 hG
end Rhone.Combinatorics
