/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Hierarchy

/-! # `χ` is not completely monotone: an exact witness -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Matrix LinearAlgebra.Tridiag LinearAlgebra.Propagation Propagation

def seed : ℕ → ℚ := fun t => if t = 0 then 1 / 8 else if t = 1 then 1 / 4 else if t = 2 then 1
  else 0

def chi32 : ℕ → ℚ := fun t => if t = 0 then 63 / 404 else if t = 1 then 53 / 202
  else if t = 2 then 64 / 101 else 0

def chi42 : ℕ → ℚ := fun t => if t = 0 then 40743 / 259772 else if t = 1 then 30645 / 129886
  else if t = 2 then 28894 / 64943 else 0

noncomputable def chi (i j t : ℕ) : ℚ := w (1 : ℚ) 1 (-4) 0 1 0 1 2 2 seed i j t

theorem E22_eq_zero : E ℚ 2 2 1 1 (-4) = 0 := by
  rw [E_eq_cont]
  norm_num [cont, dcoef, bcoef, ccoef]

theorem E32_eq : E ℚ 3 2 1 1 (-4) = 1919 := by
  rw [E_eq_cont]
  norm_num [cont, dcoef, bcoef, ccoef]

theorem E42_eq : E ℚ 4 2 1 1 (-4) = 10288 := by
  rw [E_eq_cont]
  norm_num [cont, dcoef, bcoef, ccoef]

theorem seed_kernel :
    T ℚ 2 2 1 1 (-4) *ᵥ (fun s : Fin (min 2 2 + 1) => seed (s : ℕ)) = 0 := by
  funext s
  rw [Rhone.Probability.SlotDeletion.T_mulVec_apply]
  fin_cases s <;> norm_num [seed, dcoef]

theorem seed_normalised : seed (min 2 2) = 1 := by norm_num [seed]

theorem chi_src_row (i : ℕ) (t : ℕ) :
    src (0 : ℚ) 1 0 1 (w (1 : ℚ) 1 (-4) 0 1 0 1 2 2 seed) i 2 t
      = ((lamA i t : ℕ) : ℚ) * w (1 : ℚ) 1 (-4) 0 1 0 1 2 2 seed (i - 1) 2 t := by
  rw [src_row_collapse (p := 2) (q := 2) (i := i) (1 : ℚ) 0 1
    (w (1 : ℚ) 1 (-4) 0 1 0 1 2 2 seed) (by norm_num) (fun a b u h => w_off h u) t]
  ring

theorem chi_row32_eq (t : ℕ) (ht : t ≤ 2) : chi 3 2 t = chi32 t := by
  have hE : E ℚ 3 2 1 1 (-4) ≠ 0 := by rw [E32_eq]; norm_num
  have hlhs : T ℚ 3 2 1 1 (-4) *ᵥ (fun s : Fin (min 3 2 + 1) => chi 3 2 (s : ℕ))
      = fun s : Fin (min 3 2 + 1) => ((lamA 3 (s : ℕ) : ℕ) : ℚ) * seed (s : ℕ) := by
    simp only [chi]
    rw [w_rec (by norm_num) (by norm_num) (by simp) (by norm_num) (by norm_num) hE]
    funext s
    rw [chi_src_row 3 (s : ℕ), w_base_le (by have := s.isLt; omega)]
  have hrhs : T ℚ 3 2 1 1 (-4) *ᵥ (fun s : Fin (min 3 2 + 1) => chi32 (s : ℕ))
      = fun s : Fin (min 3 2 + 1) => ((lamA 3 (s : ℕ) : ℕ) : ℚ) * seed (s : ℕ) := by
    funext s
    rw [Rhone.Probability.SlotDeletion.T_mulVec_apply]
    fin_cases s <;> norm_num [chi32, seed, dcoef, lamA]
  have hcancel := mulVec_left_cancel (isUnit_iff_ne_zero.2 hE) (hlhs.trans hrhs.symm)
  exact congrFun hcancel ⟨t, by omega⟩

theorem chi_row42_eq (t : ℕ) (ht : t ≤ 2) : chi 4 2 t = chi42 t := by
  have hE : E ℚ 4 2 1 1 (-4) ≠ 0 := by rw [E42_eq]; norm_num
  have hlhs : T ℚ 4 2 1 1 (-4) *ᵥ (fun s : Fin (min 4 2 + 1) => chi 4 2 (s : ℕ))
      = fun s : Fin (min 4 2 + 1) => ((lamA 4 (s : ℕ) : ℕ) : ℚ) * chi32 (s : ℕ) := by
    simp only [chi]
    rw [w_rec (by norm_num) (by norm_num) (by simp) (by norm_num) (by norm_num) hE]
    funext s
    rw [chi_src_row 4 (s : ℕ)]
    have : w (1 : ℚ) 1 (-4) 0 1 0 1 2 2 seed (4 - 1) 2 (s : ℕ) = chi32 (s : ℕ) :=
      chi_row32_eq (s : ℕ) (by have := s.isLt; omega)
    rw [this]
  have hrhs : T ℚ 4 2 1 1 (-4) *ᵥ (fun s : Fin (min 4 2 + 1) => chi42 (s : ℕ))
      = fun s : Fin (min 4 2 + 1) => ((lamA 4 (s : ℕ) : ℕ) : ℚ) * chi32 (s : ℕ) := by
    funext s
    rw [Rhone.Probability.SlotDeletion.T_mulVec_apply]
    fin_cases s <;> norm_num [chi42, chi32, dcoef, lamA]
  have hcancel := mulVec_left_cancel (isUnit_iff_ne_zero.2 hE) (hlhs.trans hrhs.symm)
  exact congrFun hcancel ⟨t, by omega⟩

theorem chi_values : chi 2 2 0 = 1 / 8 ∧ chi 3 2 0 = 63 / 404
    ∧ chi 4 2 0 = 40743 / 259772 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [chi]
    rw [w_base_le (by norm_num)]
    norm_num [seed]
  · rw [chi_row32_eq 0 (by norm_num)]
    norm_num [chi32]
  · rw [chi_row42_eq 0 (by norm_num)]
    norm_num [chi42]

theorem chi_not_completely_monotone :
    0 < chi 3 2 0 - chi 2 2 0
      ∧ 0 < chi 4 2 0 - chi 3 2 0
      ∧ (chi 4 2 0 - chi 3 2 0) - (chi 3 2 0 - chi 2 2 0) < 0 := by
  obtain ⟨h2, h3, h4⟩ := chi_values
  rw [h2, h3, h4]
  norm_num

theorem chi_differences :
    chi 3 2 0 - chi 2 2 0 = 25 / 808
      ∧ chi 4 2 0 - chi 3 2 0 = 117 / 129886
      ∧ (chi 4 2 0 - chi 3 2 0) - (chi 3 2 0 - chi 2 2 0) = -(15607 / 519544) := by
  obtain ⟨h2, h3, h4⟩ := chi_values
  rw [h2, h3, h4]
  norm_num

end Rhone.Probability.Assembly
