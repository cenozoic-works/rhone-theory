/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.SharpnessTransfer

/-! # Why DL‑4 needs `2 ≤ n_A` and `2 ≤ n_B`: the block `(1,1)` -/

@[expose] public section

namespace Rhone.Probability.Denominator

open LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

section Ring

variable {R : Type*} [CommRing R]

@[simp] theorem Dfull_one_one (a b r : R) : Dfull a b r 1 1 = 1 := by
  simp [Dfull]

theorem T_one_one_generic (a b r : R) :
    LinearAlgebra.Tridiag.T R 1 1 a b r = !![2 + a + b, -2; -r, a + b + r] := by
  refine Matrix.ext fun p q => ?_
  fin_cases p <;> fin_cases q <;>
    norm_num [LinearAlgebra.Tridiag.T, LinearAlgebra.Tridiag.trid, LinearAlgebra.Tridiag.tridEntry,
        LinearAlgebra.Tridiag.dcoef, LinearAlgebra.Tridiag.bcoef,
      LinearAlgebra.Tridiag.ccoef]

theorem E_one_one_eq (a b r : R) :
    LinearAlgebra.Tridiag.E R 1 1 a b r = (2 + a + b) * (a + b + r) - 2 * r := by
  rw [LinearAlgebra.Tridiag.E, T_one_one_generic, Matrix.det_fin_two_of]
  ring

end Ring

section Zero

variable {F : Type*} [Field F]

theorem isRedDenom_zero_one (A : Subring F) : Algebra.Denominator.IsRedDenom A 0 1 where
  clears := ⟨A.one_mem, by rw [mul_zero]; exact A.zero_mem⟩
  min d hd := ⟨d, hd.1, (one_mul d).symm⟩

end Zero

section OneOne

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}

theorem hypothesis_H_at_one_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (A : Subring F) (t : ℕ) :
    Algebra.Denominator.IsRedDenom A (Phi q πA πB 1 1 t) (Dfull θA θB ρ 1 1) := by
  rw [Phi_i_one hθA hθB hρ hq hπA, Dfull_one_one]
  exact isRedDenom_zero_one A

theorem q_mem_of_block_one_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hA : ξ.nA = 1) (hB : ξ.nB = 1) :
    q ξ ∈ A := by
  have h := Dfull_mul_q_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ
  rwa [hA, hB, Dfull_one_one, one_mul] at h

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem dvdIn_one_of_mem {A : Subring F} {x E : F} (hx : x ∈ A)
    (hconcl : ∀ d, Algebra.Denominator.Clears A x d → Algebra.Denominator.DvdIn A E d) :
        Algebra.Denominator.DvdIn A E 1 :=
  hconcl 1 ⟨A.one_mem, by rwa [one_mul]⟩

theorem dvdIn_one_of_clears_one_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hA : ξ.nA = 1) (hB : ξ.nB = 1)
    (hconcl : ∀ d, Algebra.Denominator.Clears A (q ξ) d → Algebra.Denominator.DvdIn A
        (LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ) d) :
    Algebra.Denominator.DvdIn A ((2 + θA + θB) * (θA + θB + ρ) - 2 * ρ) 1 := by
  have h := dvdIn_one_of_mem
    (q_mem_of_block_one_one hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ hA hB) hconcl
  rwa [hA, hB, E_one_one_eq] at h

end OneOne

end Rhone.Probability.Denominator
