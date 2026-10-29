/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.SharpnessTransfer

/-! # DL‑4 at the smallest block, `(n_A, n_B) = (2,2)` -/

@[expose] public section

namespace Rhone.Probability.Denominator

open LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

theorem E_two_two_eq {R : Type*} [CommRing R] (a b r : R) :
    LinearAlgebra.Tridiag.E R 2 2 a b r
      = (4 * (a + b) + 8) * r ^ 2 + (12 * (a + b) ^ 2 + 76 * (a + b) + 104) * r
        + (8 * (a + b) ^ 3 + 80 * (a + b) ^ 2 + 216 * (a + b) + 144) := by
  rw [LinearAlgebra.Tridiag.E, LinearAlgebra.Tridiag.T_two_two_generic, Matrix.det_fin_three]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

section Instance

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}

theorem dvdIn_E_two_two_of_clears (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hA : ξ.nA = 2) (hB : ξ.nB = 2)
    (hH : Algebra.Denominator.IsRedDenom A (Phi q πA πB 2 2 ξ.t) (Dfull θA θB ρ 2 2))
    {d : F} (hd : Algebra.Denominator.Clears A (q ξ) d) :
    Algebra.Denominator.DvdIn A ((4 * (θA + θB) + 8) * ρ ^ 2
      + (12 * (θA + θB) ^ 2 + 76 * (θA + θB) + 104) * ρ
      + (8 * (θA + θB) ^ 3 + 80 * (θA + θB) ^ 2 + 216 * (θA + θB) + 144)) d := by
  have h := dvdIn_E_of_clears hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ (by omega) (by omega)
    (by rw [hA, hB]; exact hH) hd
  rwa [hA, hB, E_two_two_eq] at h

end Instance

end Rhone.Probability.Denominator
