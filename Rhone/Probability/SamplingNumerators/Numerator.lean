/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Basic

/-! # The explicit polynomial numerator for the sampling witness at p=r=1/3 -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators

section Numerator
variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def lowerNumerator (a b r : R) : R :=
  algebraMap ℚ R (1/729) * c33 a b r
    + algebraMap ℚ R (2/243) * (a + 2) * (b + 1) * (b + 2)
        * LinearAlgebra.Tridiag.E R 2 2 a b r * LinearAlgebra.Tridiag.E R 2 3 a b r *
            LinearAlgebra.Tridiag.E R 3 2 a b r
    + algebraMap ℚ R (4/729) * (b + 1) * (b + 2)
        * LinearAlgebra.Tridiag.E R 2 2 a b r * LinearAlgebra.Tridiag.E R 2 3 a b r *
            LinearAlgebra.Tridiag.E R 3 2 a b r
    + algebraMap ℚ R (2/243) * (a + 1) * (a + 2) * (b + 2)
        * LinearAlgebra.Tridiag.E R 2 2 a b r * LinearAlgebra.Tridiag.E R 2 3 a b r *
            LinearAlgebra.Tridiag.E R 3 2 a b r
    + algebraMap ℚ R (4/729) * (a + 1) * (a + 2)
        * LinearAlgebra.Tridiag.E R 2 2 a b r * LinearAlgebra.Tridiag.E R 2 3 a b r *
            LinearAlgebra.Tridiag.E R 3 2 a b r
    + algebraMap ℚ R (4/81) * (a + 2) * (b + 2)
        * LinearAlgebra.Tridiag.E R 2 3 a b r * LinearAlgebra.Tridiag.E R 3 2 a b r * n22 a b r 0
    + algebraMap ℚ R (4/243) * (a + 2) * LinearAlgebra.Tridiag.E R 3 2 a b r * n23 a b r 0
    + algebraMap ℚ R (4/243) * (b + 2) * LinearAlgebra.Tridiag.E R 2 3 a b r * n32 a b r 0

noncomputable def samplingNumerator (a b r : R) : R :=
  algebraMap ℚ R (4/729) * n33 a b r 0
    + LinearAlgebra.Tridiag.E R 3 3 a b r * lowerNumerator a b r

end Numerator
end Rhone.Probability.SamplingNumerators
