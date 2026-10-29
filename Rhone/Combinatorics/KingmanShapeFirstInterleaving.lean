/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeInterleaving
/-!
# Interleavings containing the first slot, counted by `C(a+b-1, a-1)`

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
def FirstHistoryInterleaving (a b : ℕ) :=
  {s : HistoryInterleaving a b // 0 ∈ s.1.image Fin.val}
noncomputable instance (a b : ℕ) : Fintype (FirstHistoryInterleaving a b) := by
  unfold FirstHistoryInterleaving
  exact Fintype.ofFinite _
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem card_firstHistoryInterleaving (a b : ℕ) (ha : 1 ≤ a) :
    Fintype.card (FirstHistoryInterleaving a b) = (a+b-1).choose (a-1) := by
  classical
  let z : Fin (a+b) := ⟨0, by omega⟩
  have hm (s : FirstHistoryInterleaving a b) : z ∈ s.1.1 := by
    obtain ⟨i, hi, he⟩ := mem_image.mp s.2
    have hiz : i = z := Fin.ext he
    exact hiz ▸ hi
  have hzn (p : ((univ : Finset (Fin (a+b))).erase z).powersetCard (a-1)) : z ∉ p.1 := by
    intro hz
    exact (mem_erase.mp ((mem_powersetCard.mp p.2).1 hz)).1 rfl
  let e : FirstHistoryInterleaving a b ≃
      ((univ : Finset (Fin (a+b))).erase z).powersetCard (a-1) :=
    { toFun := fun s => ⟨s.1.1.erase z, mem_powersetCard.mpr ⟨by
        intro i hi
        exact mem_erase.mpr ⟨(mem_erase.mp hi).1, mem_univ _⟩,
        by rw [card_erase_of_mem (hm s), s.1.2]⟩⟩
      invFun := fun p => ⟨⟨insert z p.1, by
        rw [card_insert_of_notMem (hzn p), (mem_powersetCard.mp p.2).2]
        omega⟩, mem_image.mpr ⟨z, mem_insert_self _ _, rfl⟩⟩
      left_inv := fun s => Subtype.ext (Subtype.ext (insert_erase (hm s)))
      right_inv := fun p => Subtype.ext (erase_insert (hzn p)) }
  rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard,
    card_erase_of_mem (mem_univ z), card_univ, Fintype.card_fin]
end Rhone.Combinatorics
