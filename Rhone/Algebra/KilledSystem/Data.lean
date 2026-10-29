/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Recursion

/-! # The explicit solution of the `n = 2` killed-PIM system -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open Polynomial

noncomputable def Dcom : P :=
  C (225 * thAF ^ 2 * thBF + 225 * thAF ^ 2 + 225 * thAF * thBF ^ 2 + 900 * thAF * thBF + 675 *
    thAF + 225 * thBF ^ 2 + 675 * thBF + 450) * X ^ 2 + C (675 * thAF ^ 3 * thBF + 675 * thAF ^ 3
    + 1350 * thAF ^ 2 * thBF ^ 2 + 6300 * thAF ^ 2 * thBF + 4950 * thAF ^ 2 + 675 * thAF * thBF ^
    3 + 6300 * thAF * thBF ^ 2 + 15750 * thAF * thBF + 10125 * thAF + 675 * thBF ^ 3 + 4950 * thBF
    ^ 2 + 10125 * thBF + 5850) * X + C (450 * thAF ^ 4 * thBF + 450 * thAF ^ 4 + 1350 * thAF ^ 3 *
    thBF ^ 2 + 6300 * thAF ^ 3 * thBF + 4950 * thAF ^ 3 + 1350 * thAF ^ 2 * thBF ^ 3 + 11700 *
    thAF ^ 2 * thBF ^ 2 + 27000 * thAF ^ 2 * thBF + 16650 * thAF ^ 2 + 450 * thAF * thBF ^ 4 +
    6300 * thAF * thBF ^ 3 + 27000 * thAF * thBF ^ 2 + 41400 * thAF * thBF + 20250 * thAF + 450 *
    thBF ^ 4 + 4950 * thBF ^ 3 + 16650 * thBF ^ 2 + 20250 * thBF + 8100)

noncomputable def V0 : P :=
  C (135 * thAF ^ 2 * thBF + 135 * thAF ^ 2 + 135 * thAF * thBF ^ 2 + 540 * thAF * thBF + 405 *
    thAF + 135 * thBF ^ 2 + 405 * thBF + 270) * X ^ 2 + C (405 * thAF ^ 3 * thBF + 405 * thAF ^ 3
    + 810 * thAF ^ 2 * thBF ^ 2 + 3780 * thAF ^ 2 * thBF + 2970 * thAF ^ 2 + 405 * thAF * thBF ^ 3
    + 3780 * thAF * thBF ^ 2 + 9450 * thAF * thBF + 6075 * thAF + 405 * thBF ^ 3 + 2970 * thBF ^ 2
    + 6075 * thBF + 3510) * X + C (270 * thAF ^ 4 * thBF + 270 * thAF ^ 4 + 810 * thAF ^ 3 * thBF
    ^ 2 + 3780 * thAF ^ 3 * thBF + 2970 * thAF ^ 3 + 810 * thAF ^ 2 * thBF ^ 3 + 7020 * thAF ^ 2 *
    thBF ^ 2 + 16200 * thAF ^ 2 * thBF + 9990 * thAF ^ 2 + 270 * thAF * thBF ^ 4 + 3780 * thAF *
    thBF ^ 3 + 16200 * thAF * thBF ^ 2 + 24840 * thAF * thBF + 12150 * thAF + 270 * thBF ^ 4 +
    2970 * thBF ^ 3 + 9990 * thBF ^ 2 + 12150 * thBF + 4860)

noncomputable def V1 : P :=
  C (90 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 90 * thAF * thBF ^ 2 + 360 * thAF * thBF + 270 * thAF
    + 90 * thBF ^ 2 + 270 * thBF + 180) * X ^ 2 + C (270 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 540
    * thAF ^ 2 * thBF ^ 2 + 2520 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 270 * thAF * thBF ^ 3 +
    2520 * thAF * thBF ^ 2 + 6300 * thAF * thBF + 4050 * thAF + 270 * thBF ^ 3 + 1980 * thBF ^ 2 +
    4050 * thBF + 2340) * X + C (180 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 540 * thAF ^ 3 * thBF ^
    2 + 2520 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 540 * thAF ^ 2 * thBF ^ 3 + 4680 * thAF ^ 2 *
    thBF ^ 2 + 10800 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 180 * thAF * thBF ^ 4 + 2520 * thAF *
    thBF ^ 3 + 10800 * thAF * thBF ^ 2 + 16560 * thAF * thBF + 8100 * thAF + 180 * thBF ^ 4 + 1980
    * thBF ^ 3 + 6660 * thBF ^ 2 + 8100 * thBF + 3240)

noncomputable def V2 : P :=
  C (150 * thAF ^ 2 * thBF + 150 * thAF ^ 2 + 150 * thAF * thBF ^ 2 + 600 * thAF * thBF + 450 *
    thAF + 150 * thBF ^ 2 + 450 * thBF + 300) * X ^ 2 + C (450 * thAF ^ 3 * thBF + 450 * thAF ^ 3
    + 900 * thAF ^ 2 * thBF ^ 2 + 4200 * thAF ^ 2 * thBF + 3300 * thAF ^ 2 + 450 * thAF * thBF ^ 3
    + 4200 * thAF * thBF ^ 2 + 10500 * thAF * thBF + 6750 * thAF + 450 * thBF ^ 3 + 3300 * thBF ^
    2 + 6750 * thBF + 3900) * X + C (300 * thAF ^ 4 * thBF + 300 * thAF ^ 4 + 900 * thAF ^ 3 *
    thBF ^ 2 + 4200 * thAF ^ 3 * thBF + 3300 * thAF ^ 3 + 900 * thAF ^ 2 * thBF ^ 3 + 7800 * thAF
    ^ 2 * thBF ^ 2 + 18000 * thAF ^ 2 * thBF + 11100 * thAF ^ 2 + 300 * thAF * thBF ^ 4 + 4200 *
    thAF * thBF ^ 3 + 18000 * thAF * thBF ^ 2 + 27600 * thAF * thBF + 13500 * thAF + 300 * thBF ^
    4 + 3300 * thBF ^ 3 + 11100 * thBF ^ 2 + 13500 * thBF + 5400)

noncomputable def V3 : P :=
  C (75 * thAF ^ 2 * thBF + 75 * thAF ^ 2 + 75 * thAF * thBF ^ 2 + 300 * thAF * thBF + 225 * thAF
    + 75 * thBF ^ 2 + 225 * thBF + 150) * X ^ 2 + C (225 * thAF ^ 3 * thBF + 225 * thAF ^ 3 + 450
    * thAF ^ 2 * thBF ^ 2 + 2100 * thAF ^ 2 * thBF + 1650 * thAF ^ 2 + 225 * thAF * thBF ^ 3 +
    2100 * thAF * thBF ^ 2 + 5250 * thAF * thBF + 3375 * thAF + 225 * thBF ^ 3 + 1650 * thBF ^ 2 +
    3375 * thBF + 1950) * X + C (150 * thAF ^ 4 * thBF + 150 * thAF ^ 4 + 450 * thAF ^ 3 * thBF ^
    2 + 2100 * thAF ^ 3 * thBF + 1650 * thAF ^ 3 + 450 * thAF ^ 2 * thBF ^ 3 + 3900 * thAF ^ 2 *
    thBF ^ 2 + 9000 * thAF ^ 2 * thBF + 5550 * thAF ^ 2 + 150 * thAF * thBF ^ 4 + 2100 * thAF *
    thBF ^ 3 + 9000 * thAF * thBF ^ 2 + 13800 * thAF * thBF + 6750 * thAF + 150 * thBF ^ 4 + 1650
    * thBF ^ 3 + 5550 * thBF ^ 2 + 6750 * thBF + 2700)

noncomputable def V4 : P :=
  C (81 * thAF ^ 2 * thBF + 135 * thAF ^ 2 + 81 * thAF * thBF ^ 2 + 378 * thAF * thBF + 405 * thAF
    + 81 * thBF ^ 2 + 297 * thBF + 270) * X ^ 2 + C (243 * thAF ^ 3 * thBF + 405 * thAF ^ 3 + 486
    * thAF ^ 2 * thBF ^ 2 + 2592 * thAF ^ 2 * thBF + 2970 * thAF ^ 2 + 243 * thAF * thBF ^ 3 +
    2430 * thAF * thBF ^ 2 + 7020 * thAF * thBF + 6075 * thAF + 243 * thBF ^ 3 + 1944 * thBF ^ 2 +
    4671 * thBF + 3510) * X + C (162 * thAF ^ 4 * thBF + 270 * thAF ^ 4 + 486 * thAF ^ 3 * thBF ^
    2 + 2592 * thAF ^ 3 * thBF + 2970 * thAF ^ 3 + 486 * thAF ^ 2 * thBF ^ 3 + 4536 * thAF ^ 2 *
    thBF ^ 2 + 12204 * thAF ^ 2 * thBF + 9990 * thAF ^ 2 + 162 * thAF * thBF ^ 4 + 2376 * thAF *
    thBF ^ 3 + 11124 * thAF * thBF ^ 2 + 19980 * thAF * thBF + 12150 * thAF + 162 * thBF ^ 4 +
    1890 * thBF ^ 3 + 7074 * thBF ^ 2 + 10206 * thBF + 4860)

noncomputable def V5 : P :=
  C (54 * thAF ^ 2 * thBF + 54 * thAF * thBF ^ 2 + 162 * thAF * thBF + 54 * thBF ^ 2 + 108 * thBF)
    * X ^ 2 + C (162 * thAF ^ 3 * thBF + 324 * thAF ^ 2 * thBF ^ 2 + 1188 * thAF ^ 2 * thBF + 162
    * thAF * thBF ^ 3 + 1350 * thAF * thBF ^ 2 + 2430 * thAF * thBF + 162 * thBF ^ 3 + 1026 * thBF
    ^ 2 + 1404 * thBF) * X + C (108 * thAF ^ 4 * thBF + 324 * thAF ^ 3 * thBF ^ 2 + 1188 * thAF ^
    3 * thBF + 324 * thAF ^ 2 * thBF ^ 3 + 2484 * thAF ^ 2 * thBF ^ 2 + 3996 * thAF ^ 2 * thBF +
    108 * thAF * thBF ^ 4 + 1404 * thAF * thBF ^ 3 + 5076 * thAF * thBF ^ 2 + 4860 * thAF * thBF +
    108 * thBF ^ 4 + 1080 * thBF ^ 3 + 2916 * thBF ^ 2 + 1944 * thBF)

noncomputable def V6 : P :=
  C (36 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 36 * thAF * thBF ^ 2 + 198 * thAF * thBF + 270 * thAF
    + 36 * thBF ^ 2 + 162 * thBF + 180) * X ^ 2 + C (108 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 216
    * thAF ^ 2 * thBF ^ 2 + 1332 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 108 * thAF * thBF ^ 3 +
    1170 * thAF * thBF ^ 2 + 3870 * thAF * thBF + 4050 * thAF + 108 * thBF ^ 3 + 954 * thBF ^ 2 +
    2646 * thBF + 2340) * X + C (72 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 216 * thAF ^ 3 * thBF ^ 2
    + 1332 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 216 * thAF ^ 2 * thBF ^ 3 + 2196 * thAF ^ 2 *
    thBF ^ 2 + 6804 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 72 * thAF * thBF ^ 4 + 1116 * thAF *
    thBF ^ 3 + 5724 * thAF * thBF ^ 2 + 11700 * thAF * thBF + 8100 * thAF + 72 * thBF ^ 4 + 900 *
    thBF ^ 3 + 3744 * thBF ^ 2 + 6156 * thBF + 3240)

noncomputable def V7 : P :=
  C (90 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 90 * thAF * thBF ^ 2 + 360 * thAF * thBF + 270 * thAF
    + 90 * thBF ^ 2 + 270 * thBF + 180) * X ^ 2 + C (270 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 540
    * thAF ^ 2 * thBF ^ 2 + 2520 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 270 * thAF * thBF ^ 3 +
    2520 * thAF * thBF ^ 2 + 6300 * thAF * thBF + 4050 * thAF + 270 * thBF ^ 3 + 1980 * thBF ^ 2 +
    4050 * thBF + 2340) * X + C (180 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 540 * thAF ^ 3 * thBF ^
    2 + 2520 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 540 * thAF ^ 2 * thBF ^ 3 + 4680 * thAF ^ 2 *
    thBF ^ 2 + 10800 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 180 * thAF * thBF ^ 4 + 2520 * thAF *
    thBF ^ 3 + 10800 * thAF * thBF ^ 2 + 16560 * thAF * thBF + 8100 * thAF + 180 * thBF ^ 4 + 1980
    * thBF ^ 3 + 6660 * thBF ^ 2 + 8100 * thBF + 3240)

noncomputable def V8 : P :=
  C (60 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 60 * thAF * thBF ^ 2 + 240 * thAF * thBF + 180 * thAF
    + 60 * thBF ^ 2 + 180 * thBF + 120) * X ^ 2 + C (180 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 360
    * thAF ^ 2 * thBF ^ 2 + 1680 * thAF ^ 2 * thBF + 1320 * thAF ^ 2 + 180 * thAF * thBF ^ 3 +
    1680 * thAF * thBF ^ 2 + 4200 * thAF * thBF + 2700 * thAF + 180 * thBF ^ 3 + 1320 * thBF ^ 2 +
    2700 * thBF + 1560) * X + C (120 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 360 * thAF ^ 3 * thBF ^
    2 + 1680 * thAF ^ 3 * thBF + 1320 * thAF ^ 3 + 360 * thAF ^ 2 * thBF ^ 3 + 3120 * thAF ^ 2 *
    thBF ^ 2 + 7200 * thAF ^ 2 * thBF + 4440 * thAF ^ 2 + 120 * thAF * thBF ^ 4 + 1680 * thAF *
    thBF ^ 3 + 7200 * thAF * thBF ^ 2 + 11040 * thAF * thBF + 5400 * thAF + 120 * thBF ^ 4 + 1320
    * thBF ^ 3 + 4440 * thBF ^ 2 + 5400 * thBF + 2160)

noncomputable def V9 : P :=
  C (45 * thAF ^ 2 * thBF + 45 * thAF ^ 2 + 45 * thAF * thBF ^ 2 + 180 * thAF * thBF + 135 * thAF
    + 45 * thBF ^ 2 + 135 * thBF + 90) * X ^ 2 + C (135 * thAF ^ 3 * thBF + 135 * thAF ^ 3 + 270 *
    thAF ^ 2 * thBF ^ 2 + 1260 * thAF ^ 2 * thBF + 990 * thAF ^ 2 + 135 * thAF * thBF ^ 3 + 1260 *
    thAF * thBF ^ 2 + 3150 * thAF * thBF + 2025 * thAF + 135 * thBF ^ 3 + 990 * thBF ^ 2 + 2025 *
    thBF + 1170) * X + C (90 * thAF ^ 4 * thBF + 90 * thAF ^ 4 + 270 * thAF ^ 3 * thBF ^ 2 + 1260
    * thAF ^ 3 * thBF + 990 * thAF ^ 3 + 270 * thAF ^ 2 * thBF ^ 3 + 2340 * thAF ^ 2 * thBF ^ 2 +
    5400 * thAF ^ 2 * thBF + 3330 * thAF ^ 2 + 90 * thAF * thBF ^ 4 + 1260 * thAF * thBF ^ 3 +
    5400 * thAF * thBF ^ 2 + 8280 * thAF * thBF + 4050 * thAF + 90 * thBF ^ 4 + 990 * thBF ^ 3 +
    3330 * thBF ^ 2 + 4050 * thBF + 1620)

noncomputable def V10 : P :=
  C (30 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 30 * thAF * thBF ^ 2 + 120 * thAF * thBF + 90 * thAF +
    30 * thBF ^ 2 + 90 * thBF + 60) * X ^ 2 + C (90 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 180 * thAF
    ^ 2 * thBF ^ 2 + 840 * thAF ^ 2 * thBF + 660 * thAF ^ 2 + 90 * thAF * thBF ^ 3 + 840 * thAF *
    thBF ^ 2 + 2100 * thAF * thBF + 1350 * thAF + 90 * thBF ^ 3 + 660 * thBF ^ 2 + 1350 * thBF +
    780) * X + C (60 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 180 * thAF ^ 3 * thBF ^ 2 + 840 * thAF ^
    3 * thBF + 660 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 3 + 1560 * thAF ^ 2 * thBF ^ 2 + 3600 *
    thAF ^ 2 * thBF + 2220 * thAF ^ 2 + 60 * thAF * thBF ^ 4 + 840 * thAF * thBF ^ 3 + 3600 * thAF
    * thBF ^ 2 + 5520 * thAF * thBF + 2700 * thAF + 60 * thBF ^ 4 + 660 * thBF ^ 3 + 2220 * thBF ^
    2 + 2700 * thBF + 1080)

noncomputable def V11 : P :=
  C (90 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 90 * thAF * thBF ^ 2 + 360 * thAF * thBF + 270 * thAF
    + 90 * thBF ^ 2 + 270 * thBF + 180) * X ^ 2 + C (270 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 540
    * thAF ^ 2 * thBF ^ 2 + 2520 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 270 * thAF * thBF ^ 3 +
    2520 * thAF * thBF ^ 2 + 6300 * thAF * thBF + 4050 * thAF + 270 * thBF ^ 3 + 1980 * thBF ^ 2 +
    4050 * thBF + 2340) * X + C (180 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 540 * thAF ^ 3 * thBF ^
    2 + 2520 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 540 * thAF ^ 2 * thBF ^ 3 + 4680 * thAF ^ 2 *
    thBF ^ 2 + 10800 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 180 * thAF * thBF ^ 4 + 2520 * thAF *
    thBF ^ 3 + 10800 * thAF * thBF ^ 2 + 16560 * thAF * thBF + 8100 * thAF + 180 * thBF ^ 4 + 1980
    * thBF ^ 3 + 6660 * thBF ^ 2 + 8100 * thBF + 3240)

noncomputable def V12 : P :=
  C (60 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 60 * thAF * thBF ^ 2 + 240 * thAF * thBF + 180 * thAF
    + 60 * thBF ^ 2 + 180 * thBF + 120) * X ^ 2 + C (180 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 360
    * thAF ^ 2 * thBF ^ 2 + 1680 * thAF ^ 2 * thBF + 1320 * thAF ^ 2 + 180 * thAF * thBF ^ 3 +
    1680 * thAF * thBF ^ 2 + 4200 * thAF * thBF + 2700 * thAF + 180 * thBF ^ 3 + 1320 * thBF ^ 2 +
    2700 * thBF + 1560) * X + C (120 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 360 * thAF ^ 3 * thBF ^
    2 + 1680 * thAF ^ 3 * thBF + 1320 * thAF ^ 3 + 360 * thAF ^ 2 * thBF ^ 3 + 3120 * thAF ^ 2 *
    thBF ^ 2 + 7200 * thAF ^ 2 * thBF + 4440 * thAF ^ 2 + 120 * thAF * thBF ^ 4 + 1680 * thAF *
    thBF ^ 3 + 7200 * thAF * thBF ^ 2 + 11040 * thAF * thBF + 5400 * thAF + 120 * thBF ^ 4 + 1320
    * thBF ^ 3 + 4440 * thBF ^ 2 + 5400 * thBF + 2160)

noncomputable def V13 : P :=
  C (45 * thAF ^ 2 * thBF + 45 * thAF ^ 2 + 45 * thAF * thBF ^ 2 + 180 * thAF * thBF + 135 * thAF
    + 45 * thBF ^ 2 + 135 * thBF + 90) * X ^ 2 + C (135 * thAF ^ 3 * thBF + 135 * thAF ^ 3 + 270 *
    thAF ^ 2 * thBF ^ 2 + 1260 * thAF ^ 2 * thBF + 990 * thAF ^ 2 + 135 * thAF * thBF ^ 3 + 1260 *
    thAF * thBF ^ 2 + 3150 * thAF * thBF + 2025 * thAF + 135 * thBF ^ 3 + 990 * thBF ^ 2 + 2025 *
    thBF + 1170) * X + C (90 * thAF ^ 4 * thBF + 90 * thAF ^ 4 + 270 * thAF ^ 3 * thBF ^ 2 + 1260
    * thAF ^ 3 * thBF + 990 * thAF ^ 3 + 270 * thAF ^ 2 * thBF ^ 3 + 2340 * thAF ^ 2 * thBF ^ 2 +
    5400 * thAF ^ 2 * thBF + 3330 * thAF ^ 2 + 90 * thAF * thBF ^ 4 + 1260 * thAF * thBF ^ 3 +
    5400 * thAF * thBF ^ 2 + 8280 * thAF * thBF + 4050 * thAF + 90 * thBF ^ 4 + 990 * thBF ^ 3 +
    3330 * thBF ^ 2 + 4050 * thBF + 1620)

noncomputable def V14 : P :=
  C (30 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 30 * thAF * thBF ^ 2 + 120 * thAF * thBF + 90 * thAF +
    30 * thBF ^ 2 + 90 * thBF + 60) * X ^ 2 + C (90 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 180 * thAF
    ^ 2 * thBF ^ 2 + 840 * thAF ^ 2 * thBF + 660 * thAF ^ 2 + 90 * thAF * thBF ^ 3 + 840 * thAF *
    thBF ^ 2 + 2100 * thAF * thBF + 1350 * thAF + 90 * thBF ^ 3 + 660 * thBF ^ 2 + 1350 * thBF +
    780) * X + C (60 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 180 * thAF ^ 3 * thBF ^ 2 + 840 * thAF ^
    3 * thBF + 660 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 3 + 1560 * thAF ^ 2 * thBF ^ 2 + 3600 *
    thAF ^ 2 * thBF + 2220 * thAF ^ 2 + 60 * thAF * thBF ^ 4 + 840 * thAF * thBF ^ 3 + 3600 * thAF
    * thBF ^ 2 + 5520 * thAF * thBF + 2700 * thAF + 60 * thBF ^ 4 + 660 * thBF ^ 3 + 2220 * thBF ^
    2 + 2700 * thBF + 1080)

noncomputable def V15 : P :=
  C (100 * thAF ^ 2 * thBF + 100 * thAF ^ 2 + 100 * thAF * thBF ^ 2 + 450 * thAF * thBF + 350 *
    thAF + 150 * thBF ^ 2 + 450 * thBF + 300) * X ^ 2 + C (300 * thAF ^ 3 * thBF + 300 * thAF ^ 3
    + 600 * thAF ^ 2 * thBF ^ 2 + 2950 * thAF ^ 2 * thBF + 2350 * thAF ^ 2 + 300 * thAF * thBF ^ 3
    + 3100 * thAF * thBF ^ 2 + 8250 * thAF * thBF + 5450 * thAF + 450 * thBF ^ 3 + 3300 * thBF ^ 2
    + 6750 * thBF + 3900) * X + C (200 * thAF ^ 4 * thBF + 200 * thAF ^ 4 + 600 * thAF ^ 3 * thBF
    ^ 2 + 2900 * thAF ^ 3 * thBF + 2300 * thAF ^ 3 + 600 * thAF ^ 2 * thBF ^ 3 + 5500 * thAF ^ 2 *
    thBF ^ 2 + 13300 * thAF ^ 2 * thBF + 8400 * thAF ^ 2 + 200 * thAF * thBF ^ 4 + 3100 * thAF *
    thBF ^ 3 + 14300 * thAF * thBF ^ 2 + 23100 * thAF * thBF + 11700 * thAF + 300 * thBF ^ 4 +
    3300 * thBF ^ 3 + 11100 * thBF ^ 2 + 13500 * thBF + 5400)

noncomputable def V16 : P :=
  C (50 * thAF ^ 2 * thBF + 50 * thAF ^ 2 + 50 * thAF * thBF ^ 2 + 150 * thAF * thBF + 100 * thAF)
    * X ^ 2 + C (150 * thAF ^ 3 * thBF + 150 * thAF ^ 3 + 300 * thAF ^ 2 * thBF ^ 2 + 1250 * thAF
    ^ 2 * thBF + 950 * thAF ^ 2 + 150 * thAF * thBF ^ 3 + 1100 * thAF * thBF ^ 2 + 2250 * thAF *
    thBF + 1300 * thAF) * X + C (100 * thAF ^ 4 * thBF + 100 * thAF ^ 4 + 300 * thAF ^ 3 * thBF ^
    2 + 1300 * thAF ^ 3 * thBF + 1000 * thAF ^ 3 + 300 * thAF ^ 2 * thBF ^ 3 + 2300 * thAF ^ 2 *
    thBF ^ 2 + 4700 * thAF ^ 2 * thBF + 2700 * thAF ^ 2 + 100 * thAF * thBF ^ 4 + 1100 * thAF *
    thBF ^ 3 + 3700 * thAF * thBF ^ 2 + 4500 * thAF * thBF + 1800 * thAF)

noncomputable def V17 : P :=
  C (25 * thAF ^ 2 * thBF + 25 * thAF ^ 2 + 25 * thAF * thBF ^ 2 + 150 * thAF * thBF + 125 * thAF
    + 75 * thBF ^ 2 + 225 * thBF + 150) * X ^ 2 + C (75 * thAF ^ 3 * thBF + 75 * thAF ^ 3 + 150 *
    thAF ^ 2 * thBF ^ 2 + 850 * thAF ^ 2 * thBF + 700 * thAF ^ 2 + 75 * thAF * thBF ^ 3 + 1000 *
    thAF * thBF ^ 2 + 3000 * thAF * thBF + 2075 * thAF + 225 * thBF ^ 3 + 1650 * thBF ^ 2 + 3375 *
    thBF + 1950) * X + C (50 * thAF ^ 4 * thBF + 50 * thAF ^ 4 + 150 * thAF ^ 3 * thBF ^ 2 + 800 *
    thAF ^ 3 * thBF + 650 * thAF ^ 3 + 150 * thAF ^ 2 * thBF ^ 3 + 1600 * thAF ^ 2 * thBF ^ 2 +
    4300 * thAF ^ 2 * thBF + 2850 * thAF ^ 2 + 50 * thAF * thBF ^ 4 + 1000 * thAF * thBF ^ 3 +
    5300 * thAF * thBF ^ 2 + 9300 * thAF * thBF + 4950 * thAF + 150 * thBF ^ 4 + 1650 * thBF ^ 3 +
    5550 * thBF ^ 2 + 6750 * thBF + 2700)

noncomputable def V18 : P :=
  C (54 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 54 * thAF * thBF ^ 2 + 252 * thAF * thBF + 270 * thAF
    + 54 * thBF ^ 2 + 198 * thBF + 180) * X ^ 2 + C (162 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 324
    * thAF ^ 2 * thBF ^ 2 + 1728 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 162 * thAF * thBF ^ 3 +
    1620 * thAF * thBF ^ 2 + 4680 * thAF * thBF + 4050 * thAF + 162 * thBF ^ 3 + 1296 * thBF ^ 2 +
    3114 * thBF + 2340) * X + C (108 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 324 * thAF ^ 3 * thBF ^
    2 + 1728 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 324 * thAF ^ 2 * thBF ^ 3 + 3024 * thAF ^ 2 *
    thBF ^ 2 + 8136 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 108 * thAF * thBF ^ 4 + 1584 * thAF *
    thBF ^ 3 + 7416 * thAF * thBF ^ 2 + 13320 * thAF * thBF + 8100 * thAF + 108 * thBF ^ 4 + 1260
    * thBF ^ 3 + 4716 * thBF ^ 2 + 6804 * thBF + 3240)

noncomputable def V19 : P :=
  C (36 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 2 + 108 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF)
    * X ^ 2 + C (108 * thAF ^ 3 * thBF + 216 * thAF ^ 2 * thBF ^ 2 + 792 * thAF ^ 2 * thBF + 108 *
    thAF * thBF ^ 3 + 900 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (72 * thAF ^ 4 * thBF + 216 * thAF ^ 3 * thBF ^ 2 + 792 * thAF ^ 3 *
    thBF + 216 * thAF ^ 2 * thBF ^ 3 + 1656 * thAF ^ 2 * thBF ^ 2 + 2664 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 4 + 936 * thAF * thBF ^ 3 + 3384 * thAF * thBF ^ 2 + 3240 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V20 : P :=
  C (27 * thAF ^ 2 * thBF + 45 * thAF ^ 2 + 27 * thAF * thBF ^ 2 + 126 * thAF * thBF + 135 * thAF
    + 27 * thBF ^ 2 + 99 * thBF + 90) * X ^ 2 + C (81 * thAF ^ 3 * thBF + 135 * thAF ^ 3 + 162 *
    thAF ^ 2 * thBF ^ 2 + 864 * thAF ^ 2 * thBF + 990 * thAF ^ 2 + 81 * thAF * thBF ^ 3 + 810 *
    thAF * thBF ^ 2 + 2340 * thAF * thBF + 2025 * thAF + 81 * thBF ^ 3 + 648 * thBF ^ 2 + 1557 *
    thBF + 1170) * X + C (54 * thAF ^ 4 * thBF + 90 * thAF ^ 4 + 162 * thAF ^ 3 * thBF ^ 2 + 864 *
    thAF ^ 3 * thBF + 990 * thAF ^ 3 + 162 * thAF ^ 2 * thBF ^ 3 + 1512 * thAF ^ 2 * thBF ^ 2 +
    4068 * thAF ^ 2 * thBF + 3330 * thAF ^ 2 + 54 * thAF * thBF ^ 4 + 792 * thAF * thBF ^ 3 + 3708
    * thAF * thBF ^ 2 + 6660 * thAF * thBF + 4050 * thAF + 54 * thBF ^ 4 + 630 * thBF ^ 3 + 2358 *
    thBF ^ 2 + 3402 * thBF + 1620)

noncomputable def V21 : P :=
  C (18 * thAF ^ 2 * thBF + 18 * thAF * thBF ^ 2 + 54 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 108 * thAF ^ 2 * thBF ^ 2 + 396 * thAF ^ 2 * thBF + 54 *
    thAF * thBF ^ 3 + 450 * thAF * thBF ^ 2 + 810 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 +
    468 * thBF) * X + C (36 * thAF ^ 4 * thBF + 108 * thAF ^ 3 * thBF ^ 2 + 396 * thAF ^ 3 * thBF
    + 108 * thAF ^ 2 * thBF ^ 3 + 828 * thAF ^ 2 * thBF ^ 2 + 1332 * thAF ^ 2 * thBF + 36 * thAF *
    thBF ^ 4 + 468 * thAF * thBF ^ 3 + 1692 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 36 * thBF ^ 4
    + 360 * thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V22 : P :=
  C (36 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 2 + 108 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF)
    * X ^ 2 + C (108 * thAF ^ 3 * thBF + 216 * thAF ^ 2 * thBF ^ 2 + 792 * thAF ^ 2 * thBF + 108 *
    thAF * thBF ^ 3 + 900 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (72 * thAF ^ 4 * thBF + 216 * thAF ^ 3 * thBF ^ 2 + 792 * thAF ^ 3 *
    thBF + 216 * thAF ^ 2 * thBF ^ 3 + 1656 * thAF ^ 2 * thBF ^ 2 + 2664 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 4 + 936 * thAF * thBF ^ 3 + 3384 * thAF * thBF ^ 2 + 3240 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V23 : P :=
  C (24 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 24 * thAF * thBF ^ 2 + 132 * thAF * thBF + 180 * thAF
    + 24 * thBF ^ 2 + 108 * thBF + 120) * X ^ 2 + C (72 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 144 *
    thAF ^ 2 * thBF ^ 2 + 888 * thAF ^ 2 * thBF + 1320 * thAF ^ 2 + 72 * thAF * thBF ^ 3 + 780 *
    thAF * thBF ^ 2 + 2580 * thAF * thBF + 2700 * thAF + 72 * thBF ^ 3 + 636 * thBF ^ 2 + 1764 *
    thBF + 1560) * X + C (48 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 144 * thAF ^ 3 * thBF ^ 2 + 888
    * thAF ^ 3 * thBF + 1320 * thAF ^ 3 + 144 * thAF ^ 2 * thBF ^ 3 + 1464 * thAF ^ 2 * thBF ^ 2 +
    4536 * thAF ^ 2 * thBF + 4440 * thAF ^ 2 + 48 * thAF * thBF ^ 4 + 744 * thAF * thBF ^ 3 + 3816
    * thAF * thBF ^ 2 + 7800 * thAF * thBF + 5400 * thAF + 48 * thBF ^ 4 + 600 * thBF ^ 3 + 2496 *
    thBF ^ 2 + 4104 * thBF + 2160)

noncomputable def V24 : P :=
  C (18 * thAF ^ 2 * thBF + 18 * thAF * thBF ^ 2 + 54 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 108 * thAF ^ 2 * thBF ^ 2 + 396 * thAF ^ 2 * thBF + 54 *
    thAF * thBF ^ 3 + 450 * thAF * thBF ^ 2 + 810 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 +
    468 * thBF) * X + C (36 * thAF ^ 4 * thBF + 108 * thAF ^ 3 * thBF ^ 2 + 396 * thAF ^ 3 * thBF
    + 108 * thAF ^ 2 * thBF ^ 3 + 828 * thAF ^ 2 * thBF ^ 2 + 1332 * thAF ^ 2 * thBF + 36 * thAF *
    thBF ^ 4 + 468 * thAF * thBF ^ 3 + 1692 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 36 * thBF ^ 4
    + 360 * thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V25 : P :=
  C (12 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 12 * thAF * thBF ^ 2 + 66 * thAF * thBF + 90 * thAF +
    12 * thBF ^ 2 + 54 * thBF + 60) * X ^ 2 + C (36 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 72 * thAF
    ^ 2 * thBF ^ 2 + 444 * thAF ^ 2 * thBF + 660 * thAF ^ 2 + 36 * thAF * thBF ^ 3 + 390 * thAF *
    thBF ^ 2 + 1290 * thAF * thBF + 1350 * thAF + 36 * thBF ^ 3 + 318 * thBF ^ 2 + 882 * thBF +
    780) * X + C (24 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 72 * thAF ^ 3 * thBF ^ 2 + 444 * thAF ^ 3
    * thBF + 660 * thAF ^ 3 + 72 * thAF ^ 2 * thBF ^ 3 + 732 * thAF ^ 2 * thBF ^ 2 + 2268 * thAF ^
    2 * thBF + 2220 * thAF ^ 2 + 24 * thAF * thBF ^ 4 + 372 * thAF * thBF ^ 3 + 1908 * thAF * thBF
    ^ 2 + 3900 * thAF * thBF + 2700 * thAF + 24 * thBF ^ 4 + 300 * thBF ^ 3 + 1248 * thBF ^ 2 +
    2052 * thBF + 1080)

noncomputable def V26 : P :=
  C (54 * thAF ^ 2 * thBF + 90 * thAF ^ 2 + 54 * thAF * thBF ^ 2 + 252 * thAF * thBF + 270 * thAF
    + 54 * thBF ^ 2 + 198 * thBF + 180) * X ^ 2 + C (162 * thAF ^ 3 * thBF + 270 * thAF ^ 3 + 324
    * thAF ^ 2 * thBF ^ 2 + 1728 * thAF ^ 2 * thBF + 1980 * thAF ^ 2 + 162 * thAF * thBF ^ 3 +
    1620 * thAF * thBF ^ 2 + 4680 * thAF * thBF + 4050 * thAF + 162 * thBF ^ 3 + 1296 * thBF ^ 2 +
    3114 * thBF + 2340) * X + C (108 * thAF ^ 4 * thBF + 180 * thAF ^ 4 + 324 * thAF ^ 3 * thBF ^
    2 + 1728 * thAF ^ 3 * thBF + 1980 * thAF ^ 3 + 324 * thAF ^ 2 * thBF ^ 3 + 3024 * thAF ^ 2 *
    thBF ^ 2 + 8136 * thAF ^ 2 * thBF + 6660 * thAF ^ 2 + 108 * thAF * thBF ^ 4 + 1584 * thAF *
    thBF ^ 3 + 7416 * thAF * thBF ^ 2 + 13320 * thAF * thBF + 8100 * thAF + 108 * thBF ^ 4 + 1260
    * thBF ^ 3 + 4716 * thBF ^ 2 + 6804 * thBF + 3240)

noncomputable def V27 : P :=
  C (36 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 2 + 108 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF)
    * X ^ 2 + C (108 * thAF ^ 3 * thBF + 216 * thAF ^ 2 * thBF ^ 2 + 792 * thAF ^ 2 * thBF + 108 *
    thAF * thBF ^ 3 + 900 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (72 * thAF ^ 4 * thBF + 216 * thAF ^ 3 * thBF ^ 2 + 792 * thAF ^ 3 *
    thBF + 216 * thAF ^ 2 * thBF ^ 3 + 1656 * thAF ^ 2 * thBF ^ 2 + 2664 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 4 + 936 * thAF * thBF ^ 3 + 3384 * thAF * thBF ^ 2 + 3240 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V28 : P :=
  C (24 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 24 * thAF * thBF ^ 2 + 132 * thAF * thBF + 180 * thAF
    + 24 * thBF ^ 2 + 108 * thBF + 120) * X ^ 2 + C (72 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 144 *
    thAF ^ 2 * thBF ^ 2 + 888 * thAF ^ 2 * thBF + 1320 * thAF ^ 2 + 72 * thAF * thBF ^ 3 + 780 *
    thAF * thBF ^ 2 + 2580 * thAF * thBF + 2700 * thAF + 72 * thBF ^ 3 + 636 * thBF ^ 2 + 1764 *
    thBF + 1560) * X + C (48 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 144 * thAF ^ 3 * thBF ^ 2 + 888
    * thAF ^ 3 * thBF + 1320 * thAF ^ 3 + 144 * thAF ^ 2 * thBF ^ 3 + 1464 * thAF ^ 2 * thBF ^ 2 +
    4536 * thAF ^ 2 * thBF + 4440 * thAF ^ 2 + 48 * thAF * thBF ^ 4 + 744 * thAF * thBF ^ 3 + 3816
    * thAF * thBF ^ 2 + 7800 * thAF * thBF + 5400 * thAF + 48 * thBF ^ 4 + 600 * thBF ^ 3 + 2496 *
    thBF ^ 2 + 4104 * thBF + 2160)

noncomputable def V29 : P :=
  C (27 * thAF ^ 2 * thBF + 45 * thAF ^ 2 + 27 * thAF * thBF ^ 2 + 126 * thAF * thBF + 135 * thAF
    + 27 * thBF ^ 2 + 99 * thBF + 90) * X ^ 2 + C (81 * thAF ^ 3 * thBF + 135 * thAF ^ 3 + 162 *
    thAF ^ 2 * thBF ^ 2 + 864 * thAF ^ 2 * thBF + 990 * thAF ^ 2 + 81 * thAF * thBF ^ 3 + 810 *
    thAF * thBF ^ 2 + 2340 * thAF * thBF + 2025 * thAF + 81 * thBF ^ 3 + 648 * thBF ^ 2 + 1557 *
    thBF + 1170) * X + C (54 * thAF ^ 4 * thBF + 90 * thAF ^ 4 + 162 * thAF ^ 3 * thBF ^ 2 + 864 *
    thAF ^ 3 * thBF + 990 * thAF ^ 3 + 162 * thAF ^ 2 * thBF ^ 3 + 1512 * thAF ^ 2 * thBF ^ 2 +
    4068 * thAF ^ 2 * thBF + 3330 * thAF ^ 2 + 54 * thAF * thBF ^ 4 + 792 * thAF * thBF ^ 3 + 3708
    * thAF * thBF ^ 2 + 6660 * thAF * thBF + 4050 * thAF + 54 * thBF ^ 4 + 630 * thBF ^ 3 + 2358 *
    thBF ^ 2 + 3402 * thBF + 1620)

noncomputable def V30 : P :=
  C (18 * thAF ^ 2 * thBF + 18 * thAF * thBF ^ 2 + 54 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 108 * thAF ^ 2 * thBF ^ 2 + 396 * thAF ^ 2 * thBF + 54 *
    thAF * thBF ^ 3 + 450 * thAF * thBF ^ 2 + 810 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 +
    468 * thBF) * X + C (36 * thAF ^ 4 * thBF + 108 * thAF ^ 3 * thBF ^ 2 + 396 * thAF ^ 3 * thBF
    + 108 * thAF ^ 2 * thBF ^ 3 + 828 * thAF ^ 2 * thBF ^ 2 + 1332 * thAF ^ 2 * thBF + 36 * thAF *
    thBF ^ 4 + 468 * thAF * thBF ^ 3 + 1692 * thAF * thBF ^ 2 + 1620 * thAF * thBF + 36 * thBF ^ 4
    + 360 * thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V31 : P :=
  C (12 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 12 * thAF * thBF ^ 2 + 66 * thAF * thBF + 90 * thAF +
    12 * thBF ^ 2 + 54 * thBF + 60) * X ^ 2 + C (36 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 72 * thAF
    ^ 2 * thBF ^ 2 + 444 * thAF ^ 2 * thBF + 660 * thAF ^ 2 + 36 * thAF * thBF ^ 3 + 390 * thAF *
    thBF ^ 2 + 1290 * thAF * thBF + 1350 * thAF + 36 * thBF ^ 3 + 318 * thBF ^ 2 + 882 * thBF +
    780) * X + C (24 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 72 * thAF ^ 3 * thBF ^ 2 + 444 * thAF ^ 3
    * thBF + 660 * thAF ^ 3 + 72 * thAF ^ 2 * thBF ^ 3 + 732 * thAF ^ 2 * thBF ^ 2 + 2268 * thAF ^
    2 * thBF + 2220 * thAF ^ 2 + 24 * thAF * thBF ^ 4 + 372 * thAF * thBF ^ 3 + 1908 * thAF * thBF
    ^ 2 + 3900 * thAF * thBF + 2700 * thAF + 24 * thBF ^ 4 + 300 * thBF ^ 3 + 1248 * thBF ^ 2 +
    2052 * thBF + 1080)

noncomputable def V32 : P :=
  C (60 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 60 * thAF * thBF ^ 2 + 270 * thAF * thBF + 210 * thAF
    + 90 * thBF ^ 2 + 270 * thBF + 180) * X ^ 2 + C (180 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 360
    * thAF ^ 2 * thBF ^ 2 + 1770 * thAF ^ 2 * thBF + 1410 * thAF ^ 2 + 180 * thAF * thBF ^ 3 +
    1860 * thAF * thBF ^ 2 + 4950 * thAF * thBF + 3270 * thAF + 270 * thBF ^ 3 + 1980 * thBF ^ 2 +
    4050 * thBF + 2340) * X + C (120 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 360 * thAF ^ 3 * thBF ^
    2 + 1740 * thAF ^ 3 * thBF + 1380 * thAF ^ 3 + 360 * thAF ^ 2 * thBF ^ 3 + 3300 * thAF ^ 2 *
    thBF ^ 2 + 7980 * thAF ^ 2 * thBF + 5040 * thAF ^ 2 + 120 * thAF * thBF ^ 4 + 1860 * thAF *
    thBF ^ 3 + 8580 * thAF * thBF ^ 2 + 13860 * thAF * thBF + 7020 * thAF + 180 * thBF ^ 4 + 1980
    * thBF ^ 3 + 6660 * thBF ^ 2 + 8100 * thBF + 3240)

noncomputable def V33 : P :=
  C (40 * thAF ^ 2 * thBF + 40 * thAF ^ 2 + 40 * thAF * thBF ^ 2 + 180 * thAF * thBF + 140 * thAF
    + 60 * thBF ^ 2 + 180 * thBF + 120) * X ^ 2 + C (120 * thAF ^ 3 * thBF + 120 * thAF ^ 3 + 240
    * thAF ^ 2 * thBF ^ 2 + 1180 * thAF ^ 2 * thBF + 940 * thAF ^ 2 + 120 * thAF * thBF ^ 3 + 1240
    * thAF * thBF ^ 2 + 3300 * thAF * thBF + 2180 * thAF + 180 * thBF ^ 3 + 1320 * thBF ^ 2 + 2700
    * thBF + 1560) * X + C (80 * thAF ^ 4 * thBF + 80 * thAF ^ 4 + 240 * thAF ^ 3 * thBF ^ 2 +
    1160 * thAF ^ 3 * thBF + 920 * thAF ^ 3 + 240 * thAF ^ 2 * thBF ^ 3 + 2200 * thAF ^ 2 * thBF ^
    2 + 5320 * thAF ^ 2 * thBF + 3360 * thAF ^ 2 + 80 * thAF * thBF ^ 4 + 1240 * thAF * thBF ^ 3 +
    5720 * thAF * thBF ^ 2 + 9240 * thAF * thBF + 4680 * thAF + 120 * thBF ^ 4 + 1320 * thBF ^ 3 +
    4440 * thBF ^ 2 + 5400 * thBF + 2160)

noncomputable def V34 : P :=
  C (30 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 30 * thAF * thBF ^ 2 + 90 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (90 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 2 + 750 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 90 * thAF * thBF ^ 3 + 660 * thAF * thBF ^ 2 + 1350 * thAF * thBF +
    780 * thAF) * X + C (60 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 180 * thAF ^ 3 * thBF ^ 2 + 780 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 3 + 1380 * thAF ^ 2 * thBF ^ 2 +
    2820 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 60 * thAF * thBF ^ 4 + 660 * thAF * thBF ^ 3 + 2220
    * thAF * thBF ^ 2 + 2700 * thAF * thBF + 1080 * thAF)

noncomputable def V35 : P :=
  C (20 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 20 * thAF * thBF ^ 2 + 60 * thAF * thBF + 40 * thAF) *
    X ^ 2 + C (60 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 2 + 500 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 60 * thAF * thBF ^ 3 + 440 * thAF * thBF ^ 2 + 900 * thAF * thBF + 520
    * thAF) * X + C (40 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 120 * thAF ^ 3 * thBF ^ 2 + 520 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 3 + 920 * thAF ^ 2 * thBF ^ 2 + 1880 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 40 * thAF * thBF ^ 4 + 440 * thAF * thBF ^ 3 + 1480 * thAF
    * thBF ^ 2 + 1800 * thAF * thBF + 720 * thAF)

noncomputable def V36 : P :=
  C (60 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 60 * thAF * thBF ^ 2 + 270 * thAF * thBF + 210 * thAF
    + 90 * thBF ^ 2 + 270 * thBF + 180) * X ^ 2 + C (180 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 360
    * thAF ^ 2 * thBF ^ 2 + 1770 * thAF ^ 2 * thBF + 1410 * thAF ^ 2 + 180 * thAF * thBF ^ 3 +
    1860 * thAF * thBF ^ 2 + 4950 * thAF * thBF + 3270 * thAF + 270 * thBF ^ 3 + 1980 * thBF ^ 2 +
    4050 * thBF + 2340) * X + C (120 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 360 * thAF ^ 3 * thBF ^
    2 + 1740 * thAF ^ 3 * thBF + 1380 * thAF ^ 3 + 360 * thAF ^ 2 * thBF ^ 3 + 3300 * thAF ^ 2 *
    thBF ^ 2 + 7980 * thAF ^ 2 * thBF + 5040 * thAF ^ 2 + 120 * thAF * thBF ^ 4 + 1860 * thAF *
    thBF ^ 3 + 8580 * thAF * thBF ^ 2 + 13860 * thAF * thBF + 7020 * thAF + 180 * thBF ^ 4 + 1980
    * thBF ^ 3 + 6660 * thBF ^ 2 + 8100 * thBF + 3240)

noncomputable def V37 : P :=
  C (40 * thAF ^ 2 * thBF + 40 * thAF ^ 2 + 40 * thAF * thBF ^ 2 + 180 * thAF * thBF + 140 * thAF
    + 60 * thBF ^ 2 + 180 * thBF + 120) * X ^ 2 + C (120 * thAF ^ 3 * thBF + 120 * thAF ^ 3 + 240
    * thAF ^ 2 * thBF ^ 2 + 1180 * thAF ^ 2 * thBF + 940 * thAF ^ 2 + 120 * thAF * thBF ^ 3 + 1240
    * thAF * thBF ^ 2 + 3300 * thAF * thBF + 2180 * thAF + 180 * thBF ^ 3 + 1320 * thBF ^ 2 + 2700
    * thBF + 1560) * X + C (80 * thAF ^ 4 * thBF + 80 * thAF ^ 4 + 240 * thAF ^ 3 * thBF ^ 2 +
    1160 * thAF ^ 3 * thBF + 920 * thAF ^ 3 + 240 * thAF ^ 2 * thBF ^ 3 + 2200 * thAF ^ 2 * thBF ^
    2 + 5320 * thAF ^ 2 * thBF + 3360 * thAF ^ 2 + 80 * thAF * thBF ^ 4 + 1240 * thAF * thBF ^ 3 +
    5720 * thAF * thBF ^ 2 + 9240 * thAF * thBF + 4680 * thAF + 120 * thBF ^ 4 + 1320 * thBF ^ 3 +
    4440 * thBF ^ 2 + 5400 * thBF + 2160)

noncomputable def V38 : P :=
  C (30 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 30 * thAF * thBF ^ 2 + 90 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (90 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 2 + 750 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 90 * thAF * thBF ^ 3 + 660 * thAF * thBF ^ 2 + 1350 * thAF * thBF +
    780 * thAF) * X + C (60 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 180 * thAF ^ 3 * thBF ^ 2 + 780 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 3 + 1380 * thAF ^ 2 * thBF ^ 2 +
    2820 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 60 * thAF * thBF ^ 4 + 660 * thAF * thBF ^ 3 + 2220
    * thAF * thBF ^ 2 + 2700 * thAF * thBF + 1080 * thAF)

noncomputable def V39 : P :=
  C (20 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 20 * thAF * thBF ^ 2 + 60 * thAF * thBF + 40 * thAF) *
    X ^ 2 + C (60 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 2 + 500 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 60 * thAF * thBF ^ 3 + 440 * thAF * thBF ^ 2 + 900 * thAF * thBF + 520
    * thAF) * X + C (40 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 120 * thAF ^ 3 * thBF ^ 2 + 520 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 3 + 920 * thAF ^ 2 * thBF ^ 2 + 1880 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 40 * thAF * thBF ^ 4 + 440 * thAF * thBF ^ 3 + 1480 * thAF
    * thBF ^ 2 + 1800 * thAF * thBF + 720 * thAF)

noncomputable def V40 : P :=
  C (15 * thAF ^ 2 * thBF + 15 * thAF ^ 2 + 15 * thAF * thBF ^ 2 + 90 * thAF * thBF + 75 * thAF +
    45 * thBF ^ 2 + 135 * thBF + 90) * X ^ 2 + C (45 * thAF ^ 3 * thBF + 45 * thAF ^ 3 + 90 * thAF
    ^ 2 * thBF ^ 2 + 510 * thAF ^ 2 * thBF + 420 * thAF ^ 2 + 45 * thAF * thBF ^ 3 + 600 * thAF *
    thBF ^ 2 + 1800 * thAF * thBF + 1245 * thAF + 135 * thBF ^ 3 + 990 * thBF ^ 2 + 2025 * thBF +
    1170) * X + C (30 * thAF ^ 4 * thBF + 30 * thAF ^ 4 + 90 * thAF ^ 3 * thBF ^ 2 + 480 * thAF ^
    3 * thBF + 390 * thAF ^ 3 + 90 * thAF ^ 2 * thBF ^ 3 + 960 * thAF ^ 2 * thBF ^ 2 + 2580 * thAF
    ^ 2 * thBF + 1710 * thAF ^ 2 + 30 * thAF * thBF ^ 4 + 600 * thAF * thBF ^ 3 + 3180 * thAF *
    thBF ^ 2 + 5580 * thAF * thBF + 2970 * thAF + 90 * thBF ^ 4 + 990 * thBF ^ 3 + 3330 * thBF ^ 2
    + 4050 * thBF + 1620)

noncomputable def V41 : P :=
  C (10 * thAF ^ 2 * thBF + 10 * thAF ^ 2 + 10 * thAF * thBF ^ 2 + 60 * thAF * thBF + 50 * thAF +
    30 * thBF ^ 2 + 90 * thBF + 60) * X ^ 2 + C (30 * thAF ^ 3 * thBF + 30 * thAF ^ 3 + 60 * thAF
    ^ 2 * thBF ^ 2 + 340 * thAF ^ 2 * thBF + 280 * thAF ^ 2 + 30 * thAF * thBF ^ 3 + 400 * thAF *
    thBF ^ 2 + 1200 * thAF * thBF + 830 * thAF + 90 * thBF ^ 3 + 660 * thBF ^ 2 + 1350 * thBF +
    780) * X + C (20 * thAF ^ 4 * thBF + 20 * thAF ^ 4 + 60 * thAF ^ 3 * thBF ^ 2 + 320 * thAF ^ 3
    * thBF + 260 * thAF ^ 3 + 60 * thAF ^ 2 * thBF ^ 3 + 640 * thAF ^ 2 * thBF ^ 2 + 1720 * thAF ^
    2 * thBF + 1140 * thAF ^ 2 + 20 * thAF * thBF ^ 4 + 400 * thAF * thBF ^ 3 + 2120 * thAF * thBF
    ^ 2 + 3720 * thAF * thBF + 1980 * thAF + 60 * thBF ^ 4 + 660 * thBF ^ 3 + 2220 * thBF ^ 2 +
    2700 * thBF + 1080)

noncomputable def V42 : P :=
  C (30 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 30 * thAF * thBF ^ 2 + 90 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (90 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 2 + 750 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 90 * thAF * thBF ^ 3 + 660 * thAF * thBF ^ 2 + 1350 * thAF * thBF +
    780 * thAF) * X + C (60 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 180 * thAF ^ 3 * thBF ^ 2 + 780 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 180 * thAF ^ 2 * thBF ^ 3 + 1380 * thAF ^ 2 * thBF ^ 2 +
    2820 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 60 * thAF * thBF ^ 4 + 660 * thAF * thBF ^ 3 + 2220
    * thAF * thBF ^ 2 + 2700 * thAF * thBF + 1080 * thAF)

noncomputable def V43 : P :=
  C (20 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 20 * thAF * thBF ^ 2 + 60 * thAF * thBF + 40 * thAF) *
    X ^ 2 + C (60 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 2 + 500 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 60 * thAF * thBF ^ 3 + 440 * thAF * thBF ^ 2 + 900 * thAF * thBF + 520
    * thAF) * X + C (40 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 120 * thAF ^ 3 * thBF ^ 2 + 520 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 120 * thAF ^ 2 * thBF ^ 3 + 920 * thAF ^ 2 * thBF ^ 2 + 1880 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 40 * thAF * thBF ^ 4 + 440 * thAF * thBF ^ 3 + 1480 * thAF
    * thBF ^ 2 + 1800 * thAF * thBF + 720 * thAF)

noncomputable def V44 : P :=
  C (15 * thAF ^ 2 * thBF + 15 * thAF ^ 2 + 15 * thAF * thBF ^ 2 + 90 * thAF * thBF + 75 * thAF +
    45 * thBF ^ 2 + 135 * thBF + 90) * X ^ 2 + C (45 * thAF ^ 3 * thBF + 45 * thAF ^ 3 + 90 * thAF
    ^ 2 * thBF ^ 2 + 510 * thAF ^ 2 * thBF + 420 * thAF ^ 2 + 45 * thAF * thBF ^ 3 + 600 * thAF *
    thBF ^ 2 + 1800 * thAF * thBF + 1245 * thAF + 135 * thBF ^ 3 + 990 * thBF ^ 2 + 2025 * thBF +
    1170) * X + C (30 * thAF ^ 4 * thBF + 30 * thAF ^ 4 + 90 * thAF ^ 3 * thBF ^ 2 + 480 * thAF ^
    3 * thBF + 390 * thAF ^ 3 + 90 * thAF ^ 2 * thBF ^ 3 + 960 * thAF ^ 2 * thBF ^ 2 + 2580 * thAF
    ^ 2 * thBF + 1710 * thAF ^ 2 + 30 * thAF * thBF ^ 4 + 600 * thAF * thBF ^ 3 + 3180 * thAF *
    thBF ^ 2 + 5580 * thAF * thBF + 2970 * thAF + 90 * thBF ^ 4 + 990 * thBF ^ 3 + 3330 * thBF ^ 2
    + 4050 * thBF + 1620)

noncomputable def V45 : P :=
  C (10 * thAF ^ 2 * thBF + 10 * thAF ^ 2 + 10 * thAF * thBF ^ 2 + 60 * thAF * thBF + 50 * thAF +
    30 * thBF ^ 2 + 90 * thBF + 60) * X ^ 2 + C (30 * thAF ^ 3 * thBF + 30 * thAF ^ 3 + 60 * thAF
    ^ 2 * thBF ^ 2 + 340 * thAF ^ 2 * thBF + 280 * thAF ^ 2 + 30 * thAF * thBF ^ 3 + 400 * thAF *
    thBF ^ 2 + 1200 * thAF * thBF + 830 * thAF + 90 * thBF ^ 3 + 660 * thBF ^ 2 + 1350 * thBF +
    780) * X + C (20 * thAF ^ 4 * thBF + 20 * thAF ^ 4 + 60 * thAF ^ 3 * thBF ^ 2 + 320 * thAF ^ 3
    * thBF + 260 * thAF ^ 3 + 60 * thAF ^ 2 * thBF ^ 3 + 640 * thAF ^ 2 * thBF ^ 2 + 1720 * thAF ^
    2 * thBF + 1140 * thAF ^ 2 + 20 * thAF * thBF ^ 4 + 400 * thAF * thBF ^ 3 + 2120 * thAF * thBF
    ^ 2 + 3720 * thAF * thBF + 1980 * thAF + 60 * thBF ^ 4 + 660 * thBF ^ 3 + 2220 * thBF ^ 2 +
    2700 * thBF + 1080)

noncomputable def V46 : P :=
  C (36 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 36 * thAF * thBF ^ 2 + 186 * thAF * thBF + 210 * thAF
    + 54 * thBF ^ 2 + 198 * thBF + 180) * X ^ 2 + C (108 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 216
    * thAF ^ 2 * thBF ^ 2 + 1218 * thAF ^ 2 * thBF + 1410 * thAF ^ 2 + 108 * thAF * thBF ^ 3 +
    1200 * thAF * thBF ^ 2 + 3666 * thAF * thBF + 3270 * thAF + 162 * thBF ^ 3 + 1296 * thBF ^ 2 +
    3114 * thBF + 2340) * X + C (72 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 216 * thAF ^ 3 * thBF ^ 2
    + 1212 * thAF ^ 3 * thBF + 1380 * thAF ^ 3 + 216 * thAF ^ 2 * thBF ^ 3 + 2172 * thAF ^ 2 *
    thBF ^ 2 + 6180 * thAF ^ 2 * thBF + 5040 * thAF ^ 2 + 72 * thAF * thBF ^ 4 + 1188 * thAF *
    thBF ^ 3 + 6060 * thAF * thBF ^ 2 + 11484 * thAF * thBF + 7020 * thAF + 108 * thBF ^ 4 + 1260
    * thBF ^ 3 + 4716 * thBF ^ 2 + 6804 * thBF + 3240)

noncomputable def V47 : P :=
  C (24 * thAF ^ 2 * thBF + 24 * thAF * thBF ^ 2 + 84 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF) *
    X ^ 2 + C (72 * thAF ^ 3 * thBF + 144 * thAF ^ 2 * thBF ^ 2 + 552 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 3 + 660 * thAF * thBF ^ 2 + 1284 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (48 * thAF ^ 4 * thBF + 144 * thAF ^ 3 * thBF ^ 2 + 528 * thAF ^ 3 *
    thBF + 144 * thAF ^ 2 * thBF ^ 3 + 1128 * thAF ^ 2 * thBF ^ 2 + 1800 * thAF ^ 2 * thBF + 48 *
    thAF * thBF ^ 4 + 672 * thAF * thBF ^ 3 + 2520 * thAF * thBF ^ 2 + 2376 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V48 : P :=
  C (16 * thAF ^ 2 * thBF + 40 * thAF ^ 2 + 16 * thAF * thBF ^ 2 + 96 * thAF * thBF + 140 * thAF +
    24 * thBF ^ 2 + 108 * thBF + 120) * X ^ 2 + C (48 * thAF ^ 3 * thBF + 120 * thAF ^ 3 + 96 *
    thAF ^ 2 * thBF ^ 2 + 628 * thAF ^ 2 * thBF + 940 * thAF ^ 2 + 48 * thAF * thBF ^ 3 + 580 *
    thAF * thBF ^ 2 + 2016 * thAF * thBF + 2180 * thAF + 72 * thBF ^ 3 + 636 * thBF ^ 2 + 1764 *
    thBF + 1560) * X + C (32 * thAF ^ 4 * thBF + 80 * thAF ^ 4 + 96 * thAF ^ 3 * thBF ^ 2 + 632 *
    thAF ^ 3 * thBF + 920 * thAF ^ 3 + 96 * thAF ^ 2 * thBF ^ 3 + 1072 * thAF ^ 2 * thBF ^ 2 +
    3520 * thAF ^ 2 * thBF + 3360 * thAF ^ 2 + 32 * thAF * thBF ^ 4 + 568 * thAF * thBF ^ 3 + 3200
    * thAF * thBF ^ 2 + 6864 * thAF * thBF + 4680 * thAF + 48 * thBF ^ 4 + 600 * thBF ^ 3 + 2496 *
    thBF ^ 2 + 4104 * thBF + 2160)

noncomputable def V49 : P :=
  C (18 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 18 * thAF * thBF ^ 2 + 66 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 2 + 510 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 54 * thAF * thBF ^ 3 + 420 * thAF * thBF ^ 2 + 1014 * thAF * thBF +
    780 * thAF) * X + C (36 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 108 * thAF ^ 3 * thBF ^ 2 + 516 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 3 + 852 * thAF ^ 2 * thBF ^ 2 +
    1956 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 36 * thAF * thBF ^ 4 + 396 * thAF * thBF ^ 3 + 1356
    * thAF * thBF ^ 2 + 1836 * thAF * thBF + 1080 * thAF)

noncomputable def V50 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 240 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 240 * thAF *
    thBF ^ 2 + 336 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 264 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 528 * thAF ^ 2 * thBF ^ 2 + 864 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 264 * thAF * thBF ^ 3 + 864 * thAF * thBF ^ 2 + 864 * thAF * thBF)

noncomputable def V51 : P :=
  C (9 * thAF ^ 2 * thBF + 15 * thAF ^ 2 + 9 * thAF * thBF ^ 2 + 60 * thAF * thBF + 75 * thAF + 27
    * thBF ^ 2 + 99 * thBF + 90) * X ^ 2 + C (27 * thAF ^ 3 * thBF + 45 * thAF ^ 3 + 54 * thAF ^ 2
    * thBF ^ 2 + 354 * thAF ^ 2 * thBF + 420 * thAF ^ 2 + 27 * thAF * thBF ^ 3 + 390 * thAF * thBF
    ^ 2 + 1326 * thAF * thBF + 1245 * thAF + 81 * thBF ^ 3 + 648 * thBF ^ 2 + 1557 * thBF + 1170)
    * X + C (18 * thAF ^ 4 * thBF + 30 * thAF ^ 4 + 54 * thAF ^ 3 * thBF ^ 2 + 348 * thAF ^ 3 *
    thBF + 390 * thAF ^ 3 + 54 * thAF ^ 2 * thBF ^ 3 + 660 * thAF ^ 2 * thBF ^ 2 + 2112 * thAF ^ 2
    * thBF + 1710 * thAF ^ 2 + 18 * thAF * thBF ^ 4 + 396 * thAF * thBF ^ 3 + 2352 * thAF * thBF ^
    2 + 4824 * thAF * thBF + 2970 * thAF + 54 * thBF ^ 4 + 630 * thBF ^ 3 + 2358 * thBF ^ 2 + 3402
    * thBF + 1620)

noncomputable def V52 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 240 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 240 * thAF *
    thBF ^ 2 + 336 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 264 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 528 * thAF ^ 2 * thBF ^ 2 + 864 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 264 * thAF * thBF ^ 3 + 864 * thAF * thBF ^ 2 + 864 * thAF * thBF)

noncomputable def V53 : P :=
  C (8 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 8 * thAF * thBF ^ 2 + 36 * thAF * thBF + 40 * thAF) * X
    ^ 2 + C (24 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 2 + 260 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 24 * thAF * thBF ^ 3 + 200 * thAF * thBF ^ 2 + 564 * thAF * thBF + 520
    * thAF) * X + C (16 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 48 * thAF ^ 3 * thBF ^ 2 + 256 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 3 + 392 * thAF ^ 2 * thBF ^ 2 + 1016 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 16 * thAF * thBF ^ 4 + 176 * thAF * thBF ^ 3 + 616 * thAF
    * thBF ^ 2 + 936 * thAF * thBF + 720 * thAF)

noncomputable def V54 : P :=
  C (6 * thAF ^ 2 * thBF + 6 * thAF * thBF ^ 2 + 30 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) * X
    ^ 2 + C (18 * thAF ^ 3 * thBF + 36 * thAF ^ 2 * thBF ^ 2 + 156 * thAF ^ 2 * thBF + 18 * thAF *
    thBF ^ 3 + 210 * thAF * thBF ^ 2 + 474 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 + 468 *
    thBF) * X + C (12 * thAF ^ 4 * thBF + 36 * thAF ^ 3 * thBF ^ 2 + 132 * thAF ^ 3 * thBF + 36 *
    thAF ^ 2 * thBF ^ 3 + 300 * thAF ^ 2 * thBF ^ 2 + 468 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 4
    + 204 * thAF * thBF ^ 3 + 828 * thAF * thBF ^ 2 + 756 * thAF * thBF + 36 * thBF ^ 4 + 360 *
    thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V55 : P :=
  C (4 * thAF ^ 2 * thBF + 10 * thAF ^ 2 + 4 * thAF * thBF ^ 2 + 30 * thAF * thBF + 50 * thAF + 12
    * thBF ^ 2 + 54 * thBF + 60) * X ^ 2 + C (12 * thAF ^ 3 * thBF + 30 * thAF ^ 3 + 24 * thAF ^ 2
    * thBF ^ 2 + 184 * thAF ^ 2 * thBF + 280 * thAF ^ 2 + 12 * thAF * thBF ^ 3 + 190 * thAF * thBF
    ^ 2 + 726 * thAF * thBF + 830 * thAF + 36 * thBF ^ 3 + 318 * thBF ^ 2 + 882 * thBF + 780) * X
    + C (8 * thAF ^ 4 * thBF + 20 * thAF ^ 4 + 24 * thAF ^ 3 * thBF ^ 2 + 188 * thAF ^ 3 * thBF +
    260 * thAF ^ 3 + 24 * thAF ^ 2 * thBF ^ 3 + 340 * thAF ^ 2 * thBF ^ 2 + 1252 * thAF ^ 2 * thBF
    + 1140 * thAF ^ 2 + 8 * thAF * thBF ^ 4 + 196 * thAF * thBF ^ 3 + 1292 * thAF * thBF ^ 2 +
    2964 * thAF * thBF + 1980 * thAF + 24 * thBF ^ 4 + 300 * thBF ^ 3 + 1248 * thBF ^ 2 + 2052 *
    thBF + 1080)

noncomputable def V56 : P :=
  C (36 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 36 * thAF * thBF ^ 2 + 186 * thAF * thBF + 210 * thAF
    + 54 * thBF ^ 2 + 198 * thBF + 180) * X ^ 2 + C (108 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 216
    * thAF ^ 2 * thBF ^ 2 + 1206 * thAF ^ 2 * thBF + 1410 * thAF ^ 2 + 108 * thAF * thBF ^ 3 +
    1188 * thAF * thBF ^ 2 + 3642 * thAF * thBF + 3270 * thAF + 162 * thBF ^ 3 + 1296 * thBF ^ 2 +
    3114 * thBF + 2340) * X + C (72 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 216 * thAF ^ 3 * thBF ^ 2
    + 1188 * thAF ^ 3 * thBF + 1380 * thAF ^ 3 + 216 * thAF ^ 2 * thBF ^ 3 + 2124 * thAF ^ 2 *
    thBF ^ 2 + 5988 * thAF ^ 2 * thBF + 5040 * thAF ^ 2 + 72 * thAF * thBF ^ 4 + 1164 * thAF *
    thBF ^ 3 + 5868 * thAF * thBF ^ 2 + 11196 * thAF * thBF + 7020 * thAF + 108 * thBF ^ 4 + 1260
    * thBF ^ 3 + 4716 * thBF ^ 2 + 6804 * thBF + 3240)

noncomputable def V57 : P :=
  C (24 * thAF ^ 2 * thBF + 24 * thAF * thBF ^ 2 + 84 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF) *
    X ^ 2 + C (72 * thAF ^ 3 * thBF + 144 * thAF ^ 2 * thBF ^ 2 + 564 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 1308 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (48 * thAF ^ 4 * thBF + 144 * thAF ^ 3 * thBF ^ 2 + 552 * thAF ^ 3 *
    thBF + 144 * thAF ^ 2 * thBF ^ 3 + 1176 * thAF ^ 2 * thBF ^ 2 + 1992 * thAF ^ 2 * thBF + 48 *
    thAF * thBF ^ 4 + 696 * thAF * thBF ^ 3 + 2712 * thAF * thBF ^ 2 + 2664 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V58 : P :=
  C (18 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 18 * thAF * thBF ^ 2 + 66 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 2 + 522 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 54 * thAF * thBF ^ 3 + 432 * thAF * thBF ^ 2 + 1038 * thAF * thBF +
    780 * thAF) * X + C (36 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 108 * thAF ^ 3 * thBF ^ 2 + 540 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 3 + 900 * thAF ^ 2 * thBF ^ 2 +
    2148 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 36 * thAF * thBF ^ 4 + 420 * thAF * thBF ^ 3 + 1548
    * thAF * thBF ^ 2 + 2124 * thAF * thBF + 1080 * thAF)

noncomputable def V59 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 228 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 228 * thAF *
    thBF ^ 2 + 312 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 240 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 480 * thAF ^ 2 * thBF ^ 2 + 672 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 240 * thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 576 * thAF * thBF)

noncomputable def V60 : P :=
  C (24 * thAF ^ 2 * thBF + 24 * thAF * thBF ^ 2 + 84 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF) *
    X ^ 2 + C (72 * thAF ^ 3 * thBF + 144 * thAF ^ 2 * thBF ^ 2 + 564 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 1308 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (48 * thAF ^ 4 * thBF + 144 * thAF ^ 3 * thBF ^ 2 + 552 * thAF ^ 3 *
    thBF + 144 * thAF ^ 2 * thBF ^ 3 + 1176 * thAF ^ 2 * thBF ^ 2 + 1992 * thAF ^ 2 * thBF + 48 *
    thAF * thBF ^ 4 + 696 * thAF * thBF ^ 3 + 2712 * thAF * thBF ^ 2 + 2664 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V61 : P :=
  C (16 * thAF ^ 2 * thBF + 40 * thAF ^ 2 + 16 * thAF * thBF ^ 2 + 96 * thAF * thBF + 140 * thAF +
    24 * thBF ^ 2 + 108 * thBF + 120) * X ^ 2 + C (48 * thAF ^ 3 * thBF + 120 * thAF ^ 3 + 96 *
    thAF ^ 2 * thBF ^ 2 + 616 * thAF ^ 2 * thBF + 940 * thAF ^ 2 + 48 * thAF * thBF ^ 3 + 568 *
    thAF * thBF ^ 2 + 1992 * thAF * thBF + 2180 * thAF + 72 * thBF ^ 3 + 636 * thBF ^ 2 + 1764 *
    thBF + 1560) * X + C (32 * thAF ^ 4 * thBF + 80 * thAF ^ 4 + 96 * thAF ^ 3 * thBF ^ 2 + 608 *
    thAF ^ 3 * thBF + 920 * thAF ^ 3 + 96 * thAF ^ 2 * thBF ^ 3 + 1024 * thAF ^ 2 * thBF ^ 2 +
    3328 * thAF ^ 2 * thBF + 3360 * thAF ^ 2 + 32 * thAF * thBF ^ 4 + 544 * thAF * thBF ^ 3 + 3008
    * thAF * thBF ^ 2 + 6576 * thAF * thBF + 4680 * thAF + 48 * thBF ^ 4 + 600 * thBF ^ 3 + 2496 *
    thBF ^ 2 + 4104 * thBF + 2160)

noncomputable def V62 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 228 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 228 * thAF *
    thBF ^ 2 + 312 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 240 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 480 * thAF ^ 2 * thBF ^ 2 + 672 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 240 * thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 576 * thAF * thBF)

noncomputable def V63 : P :=
  C (8 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 8 * thAF * thBF ^ 2 + 36 * thAF * thBF + 40 * thAF) * X
    ^ 2 + C (24 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 2 + 272 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 24 * thAF * thBF ^ 3 + 212 * thAF * thBF ^ 2 + 588 * thAF * thBF + 520
    * thAF) * X + C (16 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 48 * thAF ^ 3 * thBF ^ 2 + 280 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 3 + 440 * thAF ^ 2 * thBF ^ 2 + 1208 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 16 * thAF * thBF ^ 4 + 200 * thAF * thBF ^ 3 + 808 * thAF
    * thBF ^ 2 + 1224 * thAF * thBF + 720 * thAF)

noncomputable def V64 : P :=
  C (36 * thAF ^ 2 * thBF + 60 * thAF ^ 2 + 36 * thAF * thBF ^ 2 + 186 * thAF * thBF + 210 * thAF
    + 54 * thBF ^ 2 + 198 * thBF + 180) * X ^ 2 + C (108 * thAF ^ 3 * thBF + 180 * thAF ^ 3 + 216
    * thAF ^ 2 * thBF ^ 2 + 1206 * thAF ^ 2 * thBF + 1410 * thAF ^ 2 + 108 * thAF * thBF ^ 3 +
    1188 * thAF * thBF ^ 2 + 3642 * thAF * thBF + 3270 * thAF + 162 * thBF ^ 3 + 1296 * thBF ^ 2 +
    3114 * thBF + 2340) * X + C (72 * thAF ^ 4 * thBF + 120 * thAF ^ 4 + 216 * thAF ^ 3 * thBF ^ 2
    + 1188 * thAF ^ 3 * thBF + 1380 * thAF ^ 3 + 216 * thAF ^ 2 * thBF ^ 3 + 2124 * thAF ^ 2 *
    thBF ^ 2 + 5964 * thAF ^ 2 * thBF + 5040 * thAF ^ 2 + 72 * thAF * thBF ^ 4 + 1164 * thAF *
    thBF ^ 3 + 5844 * thAF * thBF ^ 2 + 11148 * thAF * thBF + 7020 * thAF + 108 * thBF ^ 4 + 1260
    * thBF ^ 3 + 4716 * thBF ^ 2 + 6804 * thBF + 3240)

noncomputable def V65 : P :=
  C (24 * thAF ^ 2 * thBF + 24 * thAF * thBF ^ 2 + 84 * thAF * thBF + 36 * thBF ^ 2 + 72 * thBF) *
    X ^ 2 + C (72 * thAF ^ 3 * thBF + 144 * thAF ^ 2 * thBF ^ 2 + 564 * thAF ^ 2 * thBF + 72 *
    thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 1308 * thAF * thBF + 108 * thBF ^ 3 + 684 * thBF ^ 2
    + 936 * thBF) * X + C (48 * thAF ^ 4 * thBF + 144 * thAF ^ 3 * thBF ^ 2 + 552 * thAF ^ 3 *
    thBF + 144 * thAF ^ 2 * thBF ^ 3 + 1176 * thAF ^ 2 * thBF ^ 2 + 2016 * thAF ^ 2 * thBF + 48 *
    thAF * thBF ^ 4 + 696 * thAF * thBF ^ 3 + 2736 * thAF * thBF ^ 2 + 2712 * thAF * thBF + 72 *
    thBF ^ 4 + 720 * thBF ^ 3 + 1944 * thBF ^ 2 + 1296 * thBF)

noncomputable def V66 : P :=
  C (16 * thAF ^ 2 * thBF + 40 * thAF ^ 2 + 16 * thAF * thBF ^ 2 + 96 * thAF * thBF + 140 * thAF +
    24 * thBF ^ 2 + 108 * thBF + 120) * X ^ 2 + C (48 * thAF ^ 3 * thBF + 120 * thAF ^ 3 + 96 *
    thAF ^ 2 * thBF ^ 2 + 616 * thAF ^ 2 * thBF + 940 * thAF ^ 2 + 48 * thAF * thBF ^ 3 + 568 *
    thAF * thBF ^ 2 + 1992 * thAF * thBF + 2180 * thAF + 72 * thBF ^ 3 + 636 * thBF ^ 2 + 1764 *
    thBF + 1560) * X + C (32 * thAF ^ 4 * thBF + 80 * thAF ^ 4 + 96 * thAF ^ 3 * thBF ^ 2 + 608 *
    thAF ^ 3 * thBF + 920 * thAF ^ 3 + 96 * thAF ^ 2 * thBF ^ 3 + 1024 * thAF ^ 2 * thBF ^ 2 +
    3304 * thAF ^ 2 * thBF + 3360 * thAF ^ 2 + 32 * thAF * thBF ^ 4 + 544 * thAF * thBF ^ 3 + 2984
    * thAF * thBF ^ 2 + 6528 * thAF * thBF + 4680 * thAF + 48 * thBF ^ 4 + 600 * thBF ^ 3 + 2496 *
    thBF ^ 2 + 4104 * thBF + 2160)

noncomputable def V67 : P :=
  C (18 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 18 * thAF * thBF ^ 2 + 66 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 2 + 522 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 54 * thAF * thBF ^ 3 + 432 * thAF * thBF ^ 2 + 1038 * thAF * thBF +
    780 * thAF) * X + C (36 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 108 * thAF ^ 3 * thBF ^ 2 + 540 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 3 + 900 * thAF ^ 2 * thBF ^ 2 +
    2148 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 36 * thAF * thBF ^ 4 + 420 * thAF * thBF ^ 3 + 1548
    * thAF * thBF ^ 2 + 2124 * thAF * thBF + 1080 * thAF)

noncomputable def V68 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 228 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 228 * thAF *
    thBF ^ 2 + 312 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 240 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 480 * thAF ^ 2 * thBF ^ 2 + 672 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 240 * thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 576 * thAF * thBF)

noncomputable def V69 : P :=
  C (9 * thAF ^ 2 * thBF + 15 * thAF ^ 2 + 9 * thAF * thBF ^ 2 + 60 * thAF * thBF + 75 * thAF + 27
    * thBF ^ 2 + 99 * thBF + 90) * X ^ 2 + C (27 * thAF ^ 3 * thBF + 45 * thAF ^ 3 + 54 * thAF ^ 2
    * thBF ^ 2 + 342 * thAF ^ 2 * thBF + 420 * thAF ^ 2 + 27 * thAF * thBF ^ 3 + 378 * thAF * thBF
    ^ 2 + 1302 * thAF * thBF + 1245 * thAF + 81 * thBF ^ 3 + 648 * thBF ^ 2 + 1557 * thBF + 1170)
    * X + C (18 * thAF ^ 4 * thBF + 30 * thAF ^ 4 + 54 * thAF ^ 3 * thBF ^ 2 + 324 * thAF ^ 3 *
    thBF + 390 * thAF ^ 3 + 54 * thAF ^ 2 * thBF ^ 3 + 612 * thAF ^ 2 * thBF ^ 2 + 1920 * thAF ^ 2
    * thBF + 1710 * thAF ^ 2 + 18 * thAF * thBF ^ 4 + 372 * thAF * thBF ^ 3 + 2160 * thAF * thBF ^
    2 + 4536 * thAF * thBF + 2970 * thAF + 54 * thBF ^ 4 + 630 * thBF ^ 3 + 2358 * thBF ^ 2 + 3402
    * thBF + 1620)

noncomputable def V70 : P :=
  C (6 * thAF ^ 2 * thBF + 6 * thAF * thBF ^ 2 + 30 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) * X
    ^ 2 + C (18 * thAF ^ 3 * thBF + 36 * thAF ^ 2 * thBF ^ 2 + 168 * thAF ^ 2 * thBF + 18 * thAF *
    thBF ^ 3 + 222 * thAF * thBF ^ 2 + 498 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 + 468 *
    thBF) * X + C (12 * thAF ^ 4 * thBF + 36 * thAF ^ 3 * thBF ^ 2 + 156 * thAF ^ 3 * thBF + 36 *
    thAF ^ 2 * thBF ^ 3 + 348 * thAF ^ 2 * thBF ^ 2 + 660 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 4
    + 228 * thAF * thBF ^ 3 + 1020 * thAF * thBF ^ 2 + 1044 * thAF * thBF + 36 * thBF ^ 4 + 360 *
    thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V71 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 228 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 228 * thAF *
    thBF ^ 2 + 312 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 240 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 480 * thAF ^ 2 * thBF ^ 2 + 672 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 240 * thAF * thBF ^ 3 + 672 * thAF * thBF ^ 2 + 576 * thAF * thBF)

noncomputable def V72 : P :=
  C (8 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 8 * thAF * thBF ^ 2 + 36 * thAF * thBF + 40 * thAF) * X
    ^ 2 + C (24 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 2 + 272 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 24 * thAF * thBF ^ 3 + 212 * thAF * thBF ^ 2 + 588 * thAF * thBF + 520
    * thAF) * X + C (16 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 48 * thAF ^ 3 * thBF ^ 2 + 280 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 3 + 440 * thAF ^ 2 * thBF ^ 2 + 1208 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 16 * thAF * thBF ^ 4 + 200 * thAF * thBF ^ 3 + 808 * thAF
    * thBF ^ 2 + 1224 * thAF * thBF + 720 * thAF)

noncomputable def V73 : P :=
  C (6 * thAF ^ 2 * thBF + 6 * thAF * thBF ^ 2 + 30 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) * X
    ^ 2 + C (18 * thAF ^ 3 * thBF + 36 * thAF ^ 2 * thBF ^ 2 + 168 * thAF ^ 2 * thBF + 18 * thAF *
    thBF ^ 3 + 222 * thAF * thBF ^ 2 + 498 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 + 468 *
    thBF) * X + C (12 * thAF ^ 4 * thBF + 36 * thAF ^ 3 * thBF ^ 2 + 156 * thAF ^ 3 * thBF + 36 *
    thAF ^ 2 * thBF ^ 3 + 348 * thAF ^ 2 * thBF ^ 2 + 660 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 4
    + 228 * thAF * thBF ^ 3 + 1020 * thAF * thBF ^ 2 + 1044 * thAF * thBF + 36 * thBF ^ 4 + 360 *
    thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V74 : P :=
  C (4 * thAF ^ 2 * thBF + 10 * thAF ^ 2 + 4 * thAF * thBF ^ 2 + 30 * thAF * thBF + 50 * thAF + 12
    * thBF ^ 2 + 54 * thBF + 60) * X ^ 2 + C (12 * thAF ^ 3 * thBF + 30 * thAF ^ 3 + 24 * thAF ^ 2
    * thBF ^ 2 + 172 * thAF ^ 2 * thBF + 280 * thAF ^ 2 + 12 * thAF * thBF ^ 3 + 178 * thAF * thBF
    ^ 2 + 702 * thAF * thBF + 830 * thAF + 36 * thBF ^ 3 + 318 * thBF ^ 2 + 882 * thBF + 780) * X
    + C (8 * thAF ^ 4 * thBF + 20 * thAF ^ 4 + 24 * thAF ^ 3 * thBF ^ 2 + 164 * thAF ^ 3 * thBF +
    260 * thAF ^ 3 + 24 * thAF ^ 2 * thBF ^ 3 + 292 * thAF ^ 2 * thBF ^ 2 + 1060 * thAF ^ 2 * thBF
    + 1140 * thAF ^ 2 + 8 * thAF * thBF ^ 4 + 172 * thAF * thBF ^ 3 + 1100 * thAF * thBF ^ 2 +
    2676 * thAF * thBF + 1980 * thAF + 24 * thBF ^ 4 + 300 * thBF ^ 3 + 1248 * thBF ^ 2 + 2052 *
    thBF + 1080)

noncomputable def V75 : P :=
  C (18 * thAF ^ 2 * thBF + 30 * thAF ^ 2 + 18 * thAF * thBF ^ 2 + 66 * thAF * thBF + 60 * thAF) *
    X ^ 2 + C (54 * thAF ^ 3 * thBF + 90 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 2 + 522 * thAF ^ 2 *
    thBF + 570 * thAF ^ 2 + 54 * thAF * thBF ^ 3 + 432 * thAF * thBF ^ 2 + 1038 * thAF * thBF +
    780 * thAF) * X + C (36 * thAF ^ 4 * thBF + 60 * thAF ^ 4 + 108 * thAF ^ 3 * thBF ^ 2 + 540 *
    thAF ^ 3 * thBF + 600 * thAF ^ 3 + 108 * thAF ^ 2 * thBF ^ 3 + 900 * thAF ^ 2 * thBF ^ 2 +
    2172 * thAF ^ 2 * thBF + 1620 * thAF ^ 2 + 36 * thAF * thBF ^ 4 + 420 * thAF * thBF ^ 3 + 1572
    * thAF * thBF ^ 2 + 2172 * thAF * thBF + 1080 * thAF)

noncomputable def V76 : P :=
  C (12 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 2 + 24 * thAF * thBF) * X ^ 2 + C (36 * thAF ^ 3 *
    thBF + 72 * thAF ^ 2 * thBF ^ 2 + 228 * thAF ^ 2 * thBF + 36 * thAF * thBF ^ 3 + 228 * thAF *
    thBF ^ 2 + 312 * thAF * thBF) * X + C (24 * thAF ^ 4 * thBF + 72 * thAF ^ 3 * thBF ^ 2 + 240 *
    thAF ^ 3 * thBF + 72 * thAF ^ 2 * thBF ^ 3 + 480 * thAF ^ 2 * thBF ^ 2 + 648 * thAF ^ 2 * thBF
    + 24 * thAF * thBF ^ 4 + 240 * thAF * thBF ^ 3 + 648 * thAF * thBF ^ 2 + 528 * thAF * thBF)

noncomputable def V77 : P :=
  C (8 * thAF ^ 2 * thBF + 20 * thAF ^ 2 + 8 * thAF * thBF ^ 2 + 36 * thAF * thBF + 40 * thAF) * X
    ^ 2 + C (24 * thAF ^ 3 * thBF + 60 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 2 + 272 * thAF ^ 2 *
    thBF + 380 * thAF ^ 2 + 24 * thAF * thBF ^ 3 + 212 * thAF * thBF ^ 2 + 588 * thAF * thBF + 520
    * thAF) * X + C (16 * thAF ^ 4 * thBF + 40 * thAF ^ 4 + 48 * thAF ^ 3 * thBF ^ 2 + 280 * thAF
    ^ 3 * thBF + 400 * thAF ^ 3 + 48 * thAF ^ 2 * thBF ^ 3 + 440 * thAF ^ 2 * thBF ^ 2 + 1232 *
    thAF ^ 2 * thBF + 1080 * thAF ^ 2 + 16 * thAF * thBF ^ 4 + 200 * thAF * thBF ^ 3 + 832 * thAF
    * thBF ^ 2 + 1272 * thAF * thBF + 720 * thAF)

noncomputable def V78 : P :=
  C (9 * thAF ^ 2 * thBF + 15 * thAF ^ 2 + 9 * thAF * thBF ^ 2 + 60 * thAF * thBF + 75 * thAF + 27
    * thBF ^ 2 + 99 * thBF + 90) * X ^ 2 + C (27 * thAF ^ 3 * thBF + 45 * thAF ^ 3 + 54 * thAF ^ 2
    * thBF ^ 2 + 342 * thAF ^ 2 * thBF + 420 * thAF ^ 2 + 27 * thAF * thBF ^ 3 + 378 * thAF * thBF
    ^ 2 + 1302 * thAF * thBF + 1245 * thAF + 81 * thBF ^ 3 + 648 * thBF ^ 2 + 1557 * thBF + 1170)
    * X + C (18 * thAF ^ 4 * thBF + 30 * thAF ^ 4 + 54 * thAF ^ 3 * thBF ^ 2 + 324 * thAF ^ 3 *
    thBF + 390 * thAF ^ 3 + 54 * thAF ^ 2 * thBF ^ 3 + 612 * thAF ^ 2 * thBF ^ 2 + 1896 * thAF ^ 2
    * thBF + 1710 * thAF ^ 2 + 18 * thAF * thBF ^ 4 + 372 * thAF * thBF ^ 3 + 2136 * thAF * thBF ^
    2 + 4488 * thAF * thBF + 2970 * thAF + 54 * thBF ^ 4 + 630 * thBF ^ 3 + 2358 * thBF ^ 2 + 3402
    * thBF + 1620)

noncomputable def V79 : P :=
  C (6 * thAF ^ 2 * thBF + 6 * thAF * thBF ^ 2 + 30 * thAF * thBF + 18 * thBF ^ 2 + 36 * thBF) * X
    ^ 2 + C (18 * thAF ^ 3 * thBF + 36 * thAF ^ 2 * thBF ^ 2 + 168 * thAF ^ 2 * thBF + 18 * thAF *
    thBF ^ 3 + 222 * thAF * thBF ^ 2 + 498 * thAF * thBF + 54 * thBF ^ 3 + 342 * thBF ^ 2 + 468 *
    thBF) * X + C (12 * thAF ^ 4 * thBF + 36 * thAF ^ 3 * thBF ^ 2 + 156 * thAF ^ 3 * thBF + 36 *
    thAF ^ 2 * thBF ^ 3 + 348 * thAF ^ 2 * thBF ^ 2 + 684 * thAF ^ 2 * thBF + 12 * thAF * thBF ^ 4
    + 228 * thAF * thBF ^ 3 + 1044 * thAF * thBF ^ 2 + 1092 * thAF * thBF + 36 * thBF ^ 4 + 360 *
    thBF ^ 3 + 972 * thBF ^ 2 + 648 * thBF)

noncomputable def V80 : P :=
  C (4 * thAF ^ 2 * thBF + 10 * thAF ^ 2 + 4 * thAF * thBF ^ 2 + 30 * thAF * thBF + 50 * thAF + 12
    * thBF ^ 2 + 54 * thBF + 60) * X ^ 2 + C (12 * thAF ^ 3 * thBF + 30 * thAF ^ 3 + 24 * thAF ^ 2
    * thBF ^ 2 + 172 * thAF ^ 2 * thBF + 280 * thAF ^ 2 + 12 * thAF * thBF ^ 3 + 178 * thAF * thBF
    ^ 2 + 702 * thAF * thBF + 830 * thAF + 36 * thBF ^ 3 + 318 * thBF ^ 2 + 882 * thBF + 780) * X
    + C (8 * thAF ^ 4 * thBF + 20 * thAF ^ 4 + 24 * thAF ^ 3 * thBF ^ 2 + 164 * thAF ^ 3 * thBF +
    260 * thAF ^ 3 + 24 * thAF ^ 2 * thBF ^ 3 + 292 * thAF ^ 2 * thBF ^ 2 + 1036 * thAF ^ 2 * thBF
    + 1140 * thAF ^ 2 + 8 * thAF * thBF ^ 4 + 172 * thAF * thBF ^ 3 + 1076 * thAF * thBF ^ 2 +
    2628 * thAF * thBF + 1980 * thAF + 24 * thBF ^ 4 + 300 * thBF ^ 3 + 1248 * thBF ^ 2 + 2052 *
    thBF + 1080)

noncomputable def Val (s : St) : P :=
  if s = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ then V0 else
  if s = ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ then V1 else
  if s = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ then V2 else
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ then V3 else
  if s = ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ then V4 else
  if s = ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ then V5 else
  if s = ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ then V6 else
  if s = ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ then V7 else
  if s = ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ then V8 else
  if s = ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ then V9 else
  if s = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ then V10 else
  if s = ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ then V11 else
  if s = ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ then V12 else
  if s = ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ then V13 else
  if s = ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ then V14 else
  if s = ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ then V15 else
  if s = ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ then V16 else
  if s = ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ then V17 else
  if s = ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ then V18 else
  if s = ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ then V19 else
  if s = ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ then V20 else
  if s = ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ then V21 else
  if s = ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ then V22 else
  if s = ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ then V23 else
  if s = ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ then V24 else
  if s = ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ then V25 else
  if s = ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ then V26 else
  if s = ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ then V27 else
  if s = ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ then V28 else
  if s = ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ then V29 else
  if s = ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ then V30 else
  if s = ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ then V31 else
  if s = ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ then V32 else
  if s = ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ then V33 else
  if s = ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ then V34 else
  if s = ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ then V35 else
  if s = ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ then V36 else
  if s = ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ then V37 else
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ then V38 else
  if s = ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ then V39 else
  if s = ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ then V40 else
  if s = ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ then V41 else
  if s = ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ then V42 else
  if s = ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ then V43 else
  if s = ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ then V44 else
  if s = ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ then V45 else
  if s = ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ then V46 else
  if s = ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ then V47 else
  if s = ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ then V48 else
  if s = ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ then V49 else
  if s = ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ then V50 else
  if s = ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ then V51 else
  if s = ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ then V52 else
  if s = ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ then V53 else
  if s = ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ then V54 else
  if s = ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ then V55 else
  if s = ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ then V56 else
  if s = ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ then V57 else
  if s = ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ then V58 else
  if s = ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ then V59 else
  if s = ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ then V60 else
  if s = ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ then V61 else
  if s = ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ then V62 else
  if s = ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ then V63 else
  if s = ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ then V64 else
  if s = ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ then V65 else
  if s = ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ then V66 else
  if s = ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ then V67 else
  if s = ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ then V68 else
  if s = ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ then V69 else
  if s = ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ then V70 else
  if s = ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ then V71 else
  if s = ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ then V72 else
  if s = ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ then V73 else
  if s = ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ then V74 else
  if s = ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ then V75 else
  if s = ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ then V76 else
  if s = ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ then V77 else
  if s = ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ then V78 else
  if s = ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ then V79 else
  if s = ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ then V80 else
  0

@[simp] theorem Val_0 : Val ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = V0 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_1 : Val ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = V1 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_2 : Val ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = V2 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_3 : Val ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = V3 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_4 : Val ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = V4 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_5 : Val ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = V5 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_6 : Val ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = V6 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_7 : Val ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = V7 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_8 : Val ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = V8 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_9 : Val ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = V9 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_10 : Val ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = V10 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_11 : Val ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = V11 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_12 : Val ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = V12 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_13 : Val ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = V13 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_14 : Val ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = V14 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_15 : Val ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = V15 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_16 : Val ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = V16 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_17 : Val ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = V17 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_18 : Val ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = V18 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_19 : Val ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = V19 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_20 : Val ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = V20 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_21 : Val ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = V21 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_22 : Val ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = V22 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_23 : Val ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = V23 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_24 : Val ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = V24 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_25 : Val ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = V25 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_26 : Val ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = V26 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_27 : Val ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = V27 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_28 : Val ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = V28 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_29 : Val ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = V29 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_30 : Val ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = V30 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_31 : Val ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = V31 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_32 : Val ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = V32 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_33 : Val ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = V33 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_34 : Val ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = V34 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_35 : Val ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = V35 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_36 : Val ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = V36 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_37 : Val ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = V37 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_38 : Val ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = V38 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_39 : Val ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = V39 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_40 : Val ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = V40 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_41 : Val ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = V41 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_42 : Val ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = V42 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_43 : Val ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = V43 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_44 : Val ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = V44 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_45 : Val ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = V45 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_46 : Val ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = V46 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_47 : Val ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ = V47 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_48 : Val ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ = V48 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_49 : Val ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ = V49 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_50 : Val ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ = V50 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_51 : Val ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ = V51 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_52 : Val ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ = V52 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_53 : Val ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ = V53 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_54 : Val ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ = V54 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_55 : Val ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ = V55 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_56 : Val ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ = V56 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_57 : Val ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ = V57 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_58 : Val ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ = V58 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_59 : Val ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ = V59 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_60 : Val ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = V60 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_61 : Val ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ = V61 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_62 : Val ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ = V62 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_63 : Val ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ = V63 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_64 : Val ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = V64 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_65 : Val ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = V65 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_66 : Val ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = V66 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_67 : Val ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = V67 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_68 : Val ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = V68 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_69 : Val ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ = V69 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_70 : Val ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ = V70 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_71 : Val ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = V71 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_72 : Val ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = V72 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_73 : Val ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = V73 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_74 : Val ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ = V74 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_75 : Val ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = V75 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_76 : Val ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = V76 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_77 : Val ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = V77 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_78 : Val ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = V78 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_79 : Val ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = V79 := by
  simp only [Val]
  norm_num

@[simp] theorem Val_80 : Val ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = V80 := by
  simp only [Val]
  norm_num

end Rhone.Algebra.KilledSystem
