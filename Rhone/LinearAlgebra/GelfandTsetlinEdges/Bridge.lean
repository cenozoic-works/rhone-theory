/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GelfandTsetlinEdges.Edges

/-! # The finite edge certificate stated with the field-algebra `sectorLaw` -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

open Finset

theorem cast_listProd_range (f : ℕ → ℤ) (m : ℕ) :
    ((((List.range m).map f).prod : ℤ) : ℚ) = ∏ i : Fin m, ((f i : ℤ) : ℚ) := by
  push_cast
  rw [Fin.prod_univ_eq_prod_range (fun i => ((f i : ℤ) : ℚ)) m, List.map_map]
  rfl

theorem prod_ite_erase {m : ℕ} (r : Fin m) (h : ℕ → ℚ) :
    ∏ s : Fin m, (if (s : ℕ) = (r : ℕ) then (1 : ℚ) else h s) = ∏ s ∈ univ.erase r, h s := by
  rw [← Finset.mul_prod_erase univ (fun s : Fin m => if (s : ℕ) = (r : ℕ) then (1 : ℚ) else h s)
    (mem_univ r)]
  have h0 : (if ((r : ℕ)) = ((r : ℕ)) then (1 : ℚ) else h r) = 1 := by simp
  rw [h0, one_mul]
  refine Finset.prod_congr rfl fun s hs => ?_
  have hne : (s : ℕ) ≠ (r : ℕ) := fun hc => Finset.ne_of_mem_erase hs (Fin.val_injective hc)
  rw [ite_eq_right hne]

theorem lawAt_eq_sectorLaw (e : Edge) (m : ℕ) (r : Fin (m + 1)) (hr : (r : ℕ) = e.r) :
    lawAt e (m + 1) = sectorLaw (bQ e.lam (m + 1)) (bQ e.mu (m + 1)) (bQ e.nu (m + 1)) r := by
  obtain ⟨blk, lam, mu, nu, er, R, pn, pd, o⟩ := e
  dsimp only at hr ⊢
  subst hr
  have hnum : ((numerAt ⟨blk, lam, mu, nu, r, R, pn, pd, o⟩ (m + 1) : ℤ) : ℚ)
      = (bQ nu (m + 1) r + 1) *
        ∏ s, ((bQ lam (m + 1) s - bQ nu (m + 1) r) * (bQ mu (m + 1) s - bQ nu (m + 1) r)) := by
    rw [numerAt, Int.cast_mul, Int.cast_mul, Int.cast_add, Int.cast_one, cast_listProd_range,
      cast_listProd_range, Finset.prod_mul_distrib]
    simp only [bQ]
    push_cast
    ring
  have hden : ((denomAt ⟨blk, lam, mu, nu, r, R, pn, pd, o⟩ (m + 1) : ℤ) : ℚ)
      = ∏ s ∈ univ.erase r, ((bQ nu (m + 1) s - bQ nu (m + 1) r) *
        (bQ nu (m + 1) s - bQ nu (m + 1) r - 1)) := by
    rw [denomAt, cast_listProd_range]
    dsimp only
    simp only [bQ]
    rw [← prod_ite_erase r fun t : ℕ =>
      (((betaAt nu (m + 1) t : ℤ) : ℚ) - ((betaAt nu (m + 1) (r : ℕ) : ℤ) : ℚ)) *
        (((betaAt nu (m + 1) t : ℤ) : ℚ) - ((betaAt nu (m + 1) (r : ℕ) : ℤ) : ℚ) - 1)]
    refine Finset.prod_congr rfl fun s _ => ?_
    by_cases hs : (s : ℕ) = (r : ℕ)
    · rw [ite_eq_left hs, ite_eq_left hs]
      norm_num
    · rw [ite_eq_right hs, ite_eq_right hs]
      push_cast
      ring
  rw [lawAt, sectorLaw, hnum, hden]

theorem edge_sectorLaw {e : Edge} (he : e ∈ edges) {d m : ℕ} (hd : d < 3)
    (hm : e.R + d = m + 1) (r : Fin (m + 1)) (hr : (r : ℕ) = e.r) :
    sectorLaw (bQ e.lam (m + 1)) (bQ e.mu (m + 1)) (bQ e.nu (m + 1)) r = measured e := by
  rw [← lawAt_eq_sectorLaw e m r hr, ← hm]
  exact edge_law he hd

end Rhone.LinearAlgebra.GelfandTsetlinEdges
