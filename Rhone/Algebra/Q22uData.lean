/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.E22u

/-! # `q22` in the `u`-last reading of the tower -/

@[expose] public section

namespace Rhone.Algebra

noncomputable def nuU0 : Fuv :=
  -24 * rhoM ^ 2 * vv ^ 2 + 8 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 320 * rhoM * vv ^ 2 + 104 *
    rhoM * vv + 3120 * rhoM - 576 * vv ^ 2 + 144 * vv + 4320

noncomputable def nuU1 : Fuv :=
  -12 * rhoM ^ 2 * vv ^ 2 + 4 * rhoM ^ 2 * vv + 272 * rhoM ^ 2 - 232 * rhoM * vv ^ 2 + 76 *
    rhoM * vv + 4256 * rhoM - 720 * vv ^ 2 + 216 * vv + 9216

noncomputable def nuU2 : Fuv :=
  100 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 12 * rhoM * vv + 2124 * rhoM - 248 * vv ^ 2 + 80 * vv
    + 7080

noncomputable def nuU3 : Fuv :=
  12 * rhoM ^ 2 + 460 * rhoM - 24 * vv ^ 2 + 8 * vv + 2480

noncomputable def nuU4 : Fuv :=
  36 * rhoM + 400

noncomputable def nuU5 : Fuv :=
  24

noncomputable def duU0 : Fuv :=
  -150 * rhoM ^ 2 * vv ^ 2 + 600 * rhoM ^ 2 - 1950 * rhoM * vv ^ 2 + 7800 * rhoM - 2700 * vv ^
    2 + 10800

noncomputable def duU1 : Fuv :=
  -75 * rhoM ^ 2 * vv ^ 2 + 900 * rhoM ^ 2 - 1425 * rhoM * vv ^ 2 + 13500 * rhoM - 4050 * vv ^
    2 + 27000

noncomputable def duU2 : Fuv :=
  450 * rhoM ^ 2 - 225 * rhoM * vv ^ 2 + 8550 * rhoM - 1500 * vv ^ 2 + 24900

noncomputable def duU3 : Fuv :=
  75 * rhoM ^ 2 + 2325 * rhoM - 150 * vv ^ 2 + 10650

noncomputable def duU4 : Fuv :=
  225 * rhoM + 2100

noncomputable def duU5 : Fuv :=
  150

noncomputable def guU0 : Fuv :=
  -75 * vv ^ 2 + 300

noncomputable def guU1 : Fuv :=
  300

noncomputable def guU2 : Fuv :=
  75

noncomputable def huU0 : Fuv :=
  -32 * rhoM - 96 * vv ^ 2 + 32 * vv + 928

noncomputable def huU1 : Fuv :=
  640

noncomputable def huU2 : Fuv :=
  96

noncomputable def ruU0 : Fuv :=
  64 * rhoM ^ 3 + 896 * rhoM ^ 2 - 64 * rhoM * vv ^ 2 + 1984 * rhoM - 1152 * vv ^ 2 + 1152

noncomputable def ruU1 : Fuv :=
  32 * rhoM ^ 3 + 576 * rhoM ^ 2 - 32 * rhoM * vv ^ 2 + 1504 * rhoM - 576 * vv ^ 2 + 576

noncomputable def ruU2 : Fuv :=
  64 * rhoM ^ 2 + 192 * rhoM - 64 * vv ^ 2 + 64

open Polynomial in
noncomputable def NqU : P :=
  C nuU5 * X ^ 5 + C nuU4 * X ^ 4 + C nuU3 * X ^ 3 + C nuU2 * X ^ 2 + C nuU1 * X + C nuU0

open Polynomial in
noncomputable def DqU : P :=
  C duU5 * X ^ 5 + C duU4 * X ^ 4 + C duU3 * X ^ 3 + C duU2 * X ^ 2 + C duU1 * X + C duU0

open Polynomial in
noncomputable def GqU : P := C guU2 * X ^ 2 + C guU1 * X + C guU0

open Polynomial in
noncomputable def HqU : P := C huU2 * X ^ 2 + C huU1 * X + C huU0

open Polynomial in
noncomputable def RemqU : P := C ruU2 * X ^ 2 + C ruU1 * X + C ruU0

end Rhone.Algebra
