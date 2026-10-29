/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DenominatorEquation.Cramer
public import Rhone.LinearAlgebra.SlotDeletion.Denom

/-! # Polynomial numerators for the four mixed blocks through (3,3) -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators

open Matrix

section Defs
variable {R : Type*} [CommRing R]

noncomputable def c22 (a b : R) : R := (a + 1) * (b + 1)
noncomputable def d22 (a b r : R) : R := c22 a b * LinearAlgebra.Tridiag.E R 2 2 a b r
noncomputable def s22 (a b : R) : Fin 3 → R :=
  ![2 * ((a + 1) + (b + 1)), 2 * ((a + 1) + (b + 1)), 2 * c22 a b]
noncomputable def n22 (a b r : R) : Fin 3 → R :=
  Analysis.DenominatorEquation.U R 2 2 a b r *ᵥ s22 a b

noncomputable def c23 (a b r : R) : R :=
  (a + 1) * (b + 1) * (b + 2) * LinearAlgebra.Tridiag.E R 2 2 a b r
noncomputable def d23 (a b r : R) : R := c23 a b r * LinearAlgebra.Tridiag.E R 2 3 a b r
noncomputable def s23 (a b r : R) : Fin 3 → R :=
  ![4 * (a + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r + 6 * (b + 2) * n22 a b r 0,
    4 * (a + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r + 6 * (b + 2) * n22 a b r 1,
    2 * (a + 1) * (b + 2) * LinearAlgebra.Tridiag.E R 2 2 a b r + 4 * (b + 2) * n22 a b r 2]
noncomputable def n23 (a b r : R) : Fin 3 → R :=
  Analysis.DenominatorEquation.U R 2 3 a b r *ᵥ s23 a b r

noncomputable def c32 (a b r : R) : R :=
  (a + 1) * (a + 2) * (b + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r
noncomputable def d32 (a b r : R) : R := c32 a b r * LinearAlgebra.Tridiag.E R 3 2 a b r
noncomputable def s32 (a b r : R) : Fin 3 → R :=
  ![4 * (b + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r + 6 * (a + 2) * n22 a b r 0,
    4 * (b + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r + 6 * (a + 2) * n22 a b r 1,
    2 * (a + 2) * (b + 1) * LinearAlgebra.Tridiag.E R 2 2 a b r + 4 * (a + 2) * n22 a b r 2]
noncomputable def n32 (a b r : R) : Fin 3 → R :=
  Analysis.DenominatorEquation.U R 3 2 a b r *ᵥ s32 a b r

noncomputable def c33 (a b r : R) : R :=
  (a + 1) * (a + 2) * (b + 1) * (b + 2) * LinearAlgebra.Tridiag.E R 2 2 a b r
    * LinearAlgebra.Tridiag.E R 2 3 a b r * LinearAlgebra.Tridiag.E R 3 2 a b r
noncomputable def d33 (a b r : R) : R := c33 a b r * LinearAlgebra.Tridiag.E R 3 3 a b r
noncomputable def s33 (a b r : R) : Fin 4 → R :=
  ![6 * ((a + 2) * LinearAlgebra.Tridiag.E R 3 2 a b r * n23 a b r 0
         + (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * n32 a b r 0),
    6 * ((a + 2) * LinearAlgebra.Tridiag.E R 3 2 a b r * n23 a b r 1
         + (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * n32 a b r 1),
    4 * ((a + 2) * LinearAlgebra.Tridiag.E R 3 2 a b r * n23 a b r 2
         + (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * n32 a b r 2)
      + 2 * (a + 2) * (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * LinearAlgebra.Tridiag.E R 3 2
          a b r
          * n22 a b r 1,
    6 * (a + 2) * (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * LinearAlgebra.Tridiag.E R 3 2 a b
        r
          * n22 a b r 2]
noncomputable def n33 (a b r : R) : Fin 4 → R :=
  Analysis.DenominatorEquation.U R 3 3 a b r *ᵥ s33 a b r

end Defs

section Denominators
variable {R : Type*} [CommRing R] (a b r : R)

theorem d33_eq_Dfull : d33 a b r = LinearAlgebra.SlotDeletion.Dfull a b r 3 3 := by
  simp only [d33, c33, LinearAlgebra.SlotDeletion.Dfull, LinearAlgebra.SlotDeletion.poch,
      LinearAlgebra.SlotDeletion.Erect]
  norm_num [Finset.prod_Ico_succ_top]
  ring

theorem c33_eq_Dcut : c33 a b r = LinearAlgebra.SlotDeletion.Dcut a b r 3 3 := by
  simp only [c33, LinearAlgebra.SlotDeletion.Dcut, LinearAlgebra.SlotDeletion.poch,
      LinearAlgebra.SlotDeletion.Erect]
  norm_num [Finset.prod_Ico_succ_top]
  ring

end Denominators

end Rhone.Probability.SamplingNumerators
