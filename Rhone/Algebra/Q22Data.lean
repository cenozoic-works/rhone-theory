/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.E22

/-! # The transcribed block-(2,2) value `q22` -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

noncomputable def qN2 : Fuv :=
  12 * uu ^ 3 + 100 * uu ^ 2 - 12 * uu * vv ^ 2 + 4 * uu * vv + 272 * uu - 24 * vv ^ 2 + 8 *
    vv + 240

noncomputable def qN1 : Fuv :=
  36 * uu ^ 4 + 460 * uu ^ 3 - 36 * uu ^ 2 * vv ^ 2 + 12 * uu ^ 2 * vv + 2124 * uu ^ 2 - 232 *
    uu * vv ^ 2 + 76 * uu * vv + 4256 * uu - 320 * vv ^ 2 + 104 * vv + 3120

noncomputable def qN0 : Fuv :=
  24 * uu ^ 5 + 400 * uu ^ 4 - 24 * uu ^ 3 * vv ^ 2 + 8 * uu ^ 3 * vv + 2480 * uu ^ 3 - 248 *
    uu ^ 2 * vv ^ 2 + 80 * uu ^ 2 * vv + 7080 * uu ^ 2 - 720 * uu * vv ^ 2 + 216 * uu * vv +
    9216 * uu - 576 * vv ^ 2 + 144 * vv + 4320

noncomputable def qD2 : Fuv :=
  75 * uu ^ 3 + 450 * uu ^ 2 - 75 * uu * vv ^ 2 + 900 * uu - 150 * vv ^ 2 + 600

noncomputable def qD1 : Fuv :=
  225 * uu ^ 4 + 2325 * uu ^ 3 - 225 * uu ^ 2 * vv ^ 2 + 8550 * uu ^ 2 - 1425 * uu * vv ^ 2 +
    13500 * uu - 1950 * vv ^ 2 + 7800

noncomputable def qD0 : Fuv :=
  150 * uu ^ 5 + 2100 * uu ^ 4 - 150 * uu ^ 3 * vv ^ 2 + 10650 * uu ^ 3 - 1500 * uu ^ 2 * vv ^
    2 + 24900 * uu ^ 2 - 4050 * uu * vv ^ 2 + 27000 * uu - 2700 * vv ^ 2 + 10800

noncomputable def Gq : Fuv :=
  75 * uu ^ 2 + 300 * uu - 75 * vv ^ 2 + 300

noncomputable def Hq : Fuv :=
  12 * uu ^ 3 + 100 * uu ^ 2 - 12 * uu * vv ^ 2 + 4 * uu * vv + 272 * uu - 24 * vv ^ 2 + 8 *
    vv + 240

noncomputable def Rem1 : Fuv :=
  4 * uu ^ 4 + 16 * uu ^ 3 - 4 * uu ^ 2 * vv ^ 2 + 16 * uu ^ 2 - 16 * uu * vv ^ 2 - 16 * vv ^
    2

noncomputable def Rem0 : Fuv :=
  8 * uu ^ 5 + 88 * uu ^ 4 - 8 * uu ^ 3 * vv ^ 2 + 288 * uu ^ 3 - 88 * uu ^ 2 * vv ^ 2 + 288 *
    uu ^ 2 - 288 * uu * vv ^ 2 - 288 * vv ^ 2

noncomputable def Nq : P := C qN2 * X ^ 2 + C qN1 * X + C qN0

noncomputable def Dq : P := C qD2 * X ^ 2 + C qD1 * X + C qD0

noncomputable def Remq : P := C Rem1 * X + C Rem0

end Rhone.Algebra
