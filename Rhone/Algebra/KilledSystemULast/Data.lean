/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Recursion

/-! # The explicit solution of the `n = 2` killed-PIM system, `u`-last -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

noncomputable def DcomU : P :=
  C (450) * X ^ 5 + C (675 * rhoM + 6300) * X ^ 4 + C (225 * rhoM ^ 2 + 6975 * rhoM - 450 * vv ^ 2
    + 31950) * X ^ 3 + C (1350 * rhoM ^ 2 - 675 * rhoM * vv ^ 2 + 25650 * rhoM - 4500 * vv ^ 2 +
    74700) * X ^ 2 + C (-225 * rhoM ^ 2 * vv ^ 2 + 2700 * rhoM ^ 2 - 4275 * rhoM * vv ^ 2 + 40500
    * rhoM - 12150 * vv ^ 2 + 81000) * X + C (-450 * rhoM ^ 2 * vv ^ 2 + 1800 * rhoM ^ 2 - 5850 *
    rhoM * vv ^ 2 + 23400 * rhoM - 8100 * vv ^ 2 + 32400)

noncomputable def VU0 : P :=
  C (270) * X ^ 5 + C (405 * rhoM + 3780) * X ^ 4 + C (135 * rhoM ^ 2 + 4185 * rhoM - 270 * vv ^ 2
    + 19170) * X ^ 3 + C (810 * rhoM ^ 2 - 405 * rhoM * vv ^ 2 + 15390 * rhoM - 2700 * vv ^ 2 +
    44820) * X ^ 2 + C (-135 * rhoM ^ 2 * vv ^ 2 + 1620 * rhoM ^ 2 - 2565 * rhoM * vv ^ 2 + 24300
    * rhoM - 7290 * vv ^ 2 + 48600) * X + C (-270 * rhoM ^ 2 * vv ^ 2 + 1080 * rhoM ^ 2 - 3510 *
    rhoM * vv ^ 2 + 14040 * rhoM - 4860 * vv ^ 2 + 19440)

noncomputable def VU1 : P :=
  C (180) * X ^ 5 + C (270 * rhoM + 2520) * X ^ 4 + C (90 * rhoM ^ 2 + 2790 * rhoM - 180 * vv ^ 2
    + 12780) * X ^ 3 + C (540 * rhoM ^ 2 - 270 * rhoM * vv ^ 2 + 10260 * rhoM - 1800 * vv ^ 2 +
    29880) * X ^ 2 + C (-90 * rhoM ^ 2 * vv ^ 2 + 1080 * rhoM ^ 2 - 1710 * rhoM * vv ^ 2 + 16200 *
    rhoM - 4860 * vv ^ 2 + 32400) * X + C (-180 * rhoM ^ 2 * vv ^ 2 + 720 * rhoM ^ 2 - 2340 * rhoM
    * vv ^ 2 + 9360 * rhoM - 3240 * vv ^ 2 + 12960)

noncomputable def VU2 : P :=
  C (300) * X ^ 5 + C (450 * rhoM + 4200) * X ^ 4 + C (150 * rhoM ^ 2 + 4650 * rhoM - 300 * vv ^ 2
    + 21300) * X ^ 3 + C (900 * rhoM ^ 2 - 450 * rhoM * vv ^ 2 + 17100 * rhoM - 3000 * vv ^ 2 +
    49800) * X ^ 2 + C (-150 * rhoM ^ 2 * vv ^ 2 + 1800 * rhoM ^ 2 - 2850 * rhoM * vv ^ 2 + 27000
    * rhoM - 8100 * vv ^ 2 + 54000) * X + C (-300 * rhoM ^ 2 * vv ^ 2 + 1200 * rhoM ^ 2 - 3900 *
    rhoM * vv ^ 2 + 15600 * rhoM - 5400 * vv ^ 2 + 21600)

noncomputable def VU3 : P :=
  C (150) * X ^ 5 + C (225 * rhoM + 2100) * X ^ 4 + C (75 * rhoM ^ 2 + 2325 * rhoM - 150 * vv ^ 2
    + 10650) * X ^ 3 + C (450 * rhoM ^ 2 - 225 * rhoM * vv ^ 2 + 8550 * rhoM - 1500 * vv ^ 2 +
    24900) * X ^ 2 + C (-75 * rhoM ^ 2 * vv ^ 2 + 900 * rhoM ^ 2 - 1425 * rhoM * vv ^ 2 + 13500 *
    rhoM - 4050 * vv ^ 2 + 27000) * X + C (-150 * rhoM ^ 2 * vv ^ 2 + 600 * rhoM ^ 2 - 1950 * rhoM
    * vv ^ 2 + 7800 * rhoM - 2700 * vv ^ 2 + 10800)

noncomputable def VU4 : P :=
  C (162) * X ^ 5 + C (243 * rhoM + 2484) * X ^ 4 + C (81 * rhoM ^ 2 + 2835 * rhoM - 162 * vv ^ 2
    + 216 * vv + 14094) * X ^ 3 + C (594 * rhoM ^ 2 - 243 * rhoM * vv ^ 2 + 324 * rhoM * vv +
    11934 * rhoM - 1620 * vv ^ 2 + 2160 * vv + 37044) * X ^ 2 + C (-81 * rhoM ^ 2 * vv ^ 2 + 108 *
    rhoM ^ 2 * vv + 1404 * rhoM ^ 2 - 1539 * rhoM * vv ^ 2 + 2052 * rhoM * vv + 21492 * rhoM -
    4374 * vv ^ 2 + 5832 * vv + 44712) * X + C (-162 * rhoM ^ 2 * vv ^ 2 + 216 * rhoM ^ 2 * vv +
    1080 * rhoM ^ 2 - 2106 * rhoM * vv ^ 2 + 2808 * rhoM * vv + 14040 * rhoM - 2916 * vv ^ 2 +
    3888 * vv + 19440)

noncomputable def VU5 : P :=
  C (108) * X ^ 5 + C (162 * rhoM + 1296) * X ^ 4 + C (54 * rhoM ^ 2 + 1350 * rhoM - 108 * vv ^ 2
    - 216 * vv + 5076) * X ^ 3 + C (216 * rhoM ^ 2 - 162 * rhoM * vv ^ 2 - 324 * rhoM * vv + 3456
    * rhoM - 1080 * vv ^ 2 - 2160 * vv + 7776) * X ^ 2 + C (-54 * rhoM ^ 2 * vv ^ 2 - 108 * rhoM ^
    2 * vv + 216 * rhoM ^ 2 - 1026 * rhoM * vv ^ 2 - 2052 * rhoM * vv + 2808 * rhoM - 2916 * vv ^
    2 - 5832 * vv + 3888) * X + C (-108 * rhoM ^ 2 * vv ^ 2 - 216 * rhoM ^ 2 * vv - 1404 * rhoM *
    vv ^ 2 - 2808 * rhoM * vv - 1944 * vv ^ 2 - 3888 * vv)

noncomputable def VU6 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 1224) * X ^ 4 + C (36 * rhoM ^ 2 + 1440 * rhoM - 72 * vv ^ 2 +
    216 * vv + 7704) * X ^ 3 + C (324 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 + 324 * rhoM * vv + 6804 *
    rhoM - 720 * vv ^ 2 + 2160 * vv + 22104) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 + 108 * rhoM ^ 2
    * vv + 864 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 + 2052 * rhoM * vv + 13392 * rhoM - 1944 * vv ^ 2
    + 5832 * vv + 28512) * X + C (-72 * rhoM ^ 2 * vv ^ 2 + 216 * rhoM ^ 2 * vv + 720 * rhoM ^ 2 -
    936 * rhoM * vv ^ 2 + 2808 * rhoM * vv + 9360 * rhoM - 1296 * vv ^ 2 + 3888 * vv + 12960)

noncomputable def VU7 : P :=
  C (180) * X ^ 5 + C (270 * rhoM + 2520) * X ^ 4 + C (90 * rhoM ^ 2 + 2790 * rhoM - 180 * vv ^ 2
    + 12780) * X ^ 3 + C (540 * rhoM ^ 2 - 270 * rhoM * vv ^ 2 + 10260 * rhoM - 1800 * vv ^ 2 +
    29880) * X ^ 2 + C (-90 * rhoM ^ 2 * vv ^ 2 + 1080 * rhoM ^ 2 - 1710 * rhoM * vv ^ 2 + 16200 *
    rhoM - 4860 * vv ^ 2 + 32400) * X + C (-180 * rhoM ^ 2 * vv ^ 2 + 720 * rhoM ^ 2 - 2340 * rhoM
    * vv ^ 2 + 9360 * rhoM - 3240 * vv ^ 2 + 12960)

noncomputable def VU8 : P :=
  C (120) * X ^ 5 + C (180 * rhoM + 1680) * X ^ 4 + C (60 * rhoM ^ 2 + 1860 * rhoM - 120 * vv ^ 2
    + 8520) * X ^ 3 + C (360 * rhoM ^ 2 - 180 * rhoM * vv ^ 2 + 6840 * rhoM - 1200 * vv ^ 2 +
    19920) * X ^ 2 + C (-60 * rhoM ^ 2 * vv ^ 2 + 720 * rhoM ^ 2 - 1140 * rhoM * vv ^ 2 + 10800 *
    rhoM - 3240 * vv ^ 2 + 21600) * X + C (-120 * rhoM ^ 2 * vv ^ 2 + 480 * rhoM ^ 2 - 1560 * rhoM
    * vv ^ 2 + 6240 * rhoM - 2160 * vv ^ 2 + 8640)

noncomputable def VU9 : P :=
  C (90) * X ^ 5 + C (135 * rhoM + 1260) * X ^ 4 + C (45 * rhoM ^ 2 + 1395 * rhoM - 90 * vv ^ 2 +
    6390) * X ^ 3 + C (270 * rhoM ^ 2 - 135 * rhoM * vv ^ 2 + 5130 * rhoM - 900 * vv ^ 2 + 14940)
    * X ^ 2 + C (-45 * rhoM ^ 2 * vv ^ 2 + 540 * rhoM ^ 2 - 855 * rhoM * vv ^ 2 + 8100 * rhoM -
    2430 * vv ^ 2 + 16200) * X + C (-90 * rhoM ^ 2 * vv ^ 2 + 360 * rhoM ^ 2 - 1170 * rhoM * vv ^
    2 + 4680 * rhoM - 1620 * vv ^ 2 + 6480)

noncomputable def VU10 : P :=
  C (60) * X ^ 5 + C (90 * rhoM + 840) * X ^ 4 + C (30 * rhoM ^ 2 + 930 * rhoM - 60 * vv ^ 2 +
    4260) * X ^ 3 + C (180 * rhoM ^ 2 - 90 * rhoM * vv ^ 2 + 3420 * rhoM - 600 * vv ^ 2 + 9960) *
    X ^ 2 + C (-30 * rhoM ^ 2 * vv ^ 2 + 360 * rhoM ^ 2 - 570 * rhoM * vv ^ 2 + 5400 * rhoM - 1620
    * vv ^ 2 + 10800) * X + C (-60 * rhoM ^ 2 * vv ^ 2 + 240 * rhoM ^ 2 - 780 * rhoM * vv ^ 2 +
    3120 * rhoM - 1080 * vv ^ 2 + 4320)

noncomputable def VU11 : P :=
  C (180) * X ^ 5 + C (270 * rhoM + 2520) * X ^ 4 + C (90 * rhoM ^ 2 + 2790 * rhoM - 180 * vv ^ 2
    + 12780) * X ^ 3 + C (540 * rhoM ^ 2 - 270 * rhoM * vv ^ 2 + 10260 * rhoM - 1800 * vv ^ 2 +
    29880) * X ^ 2 + C (-90 * rhoM ^ 2 * vv ^ 2 + 1080 * rhoM ^ 2 - 1710 * rhoM * vv ^ 2 + 16200 *
    rhoM - 4860 * vv ^ 2 + 32400) * X + C (-180 * rhoM ^ 2 * vv ^ 2 + 720 * rhoM ^ 2 - 2340 * rhoM
    * vv ^ 2 + 9360 * rhoM - 3240 * vv ^ 2 + 12960)

noncomputable def VU12 : P :=
  C (120) * X ^ 5 + C (180 * rhoM + 1680) * X ^ 4 + C (60 * rhoM ^ 2 + 1860 * rhoM - 120 * vv ^ 2
    + 8520) * X ^ 3 + C (360 * rhoM ^ 2 - 180 * rhoM * vv ^ 2 + 6840 * rhoM - 1200 * vv ^ 2 +
    19920) * X ^ 2 + C (-60 * rhoM ^ 2 * vv ^ 2 + 720 * rhoM ^ 2 - 1140 * rhoM * vv ^ 2 + 10800 *
    rhoM - 3240 * vv ^ 2 + 21600) * X + C (-120 * rhoM ^ 2 * vv ^ 2 + 480 * rhoM ^ 2 - 1560 * rhoM
    * vv ^ 2 + 6240 * rhoM - 2160 * vv ^ 2 + 8640)

noncomputable def VU13 : P :=
  C (90) * X ^ 5 + C (135 * rhoM + 1260) * X ^ 4 + C (45 * rhoM ^ 2 + 1395 * rhoM - 90 * vv ^ 2 +
    6390) * X ^ 3 + C (270 * rhoM ^ 2 - 135 * rhoM * vv ^ 2 + 5130 * rhoM - 900 * vv ^ 2 + 14940)
    * X ^ 2 + C (-45 * rhoM ^ 2 * vv ^ 2 + 540 * rhoM ^ 2 - 855 * rhoM * vv ^ 2 + 8100 * rhoM -
    2430 * vv ^ 2 + 16200) * X + C (-90 * rhoM ^ 2 * vv ^ 2 + 360 * rhoM ^ 2 - 1170 * rhoM * vv ^
    2 + 4680 * rhoM - 1620 * vv ^ 2 + 6480)

noncomputable def VU14 : P :=
  C (60) * X ^ 5 + C (90 * rhoM + 840) * X ^ 4 + C (30 * rhoM ^ 2 + 930 * rhoM - 60 * vv ^ 2 +
    4260) * X ^ 3 + C (180 * rhoM ^ 2 - 90 * rhoM * vv ^ 2 + 3420 * rhoM - 600 * vv ^ 2 + 9960) *
    X ^ 2 + C (-30 * rhoM ^ 2 * vv ^ 2 + 360 * rhoM ^ 2 - 570 * rhoM * vv ^ 2 + 5400 * rhoM - 1620
    * vv ^ 2 + 10800) * X + C (-60 * rhoM ^ 2 * vv ^ 2 + 240 * rhoM ^ 2 - 780 * rhoM * vv ^ 2 +
    3120 * rhoM - 1080 * vv ^ 2 + 4320)

noncomputable def VU15 : P :=
  C (200) * X ^ 5 + C (300 * rhoM + 3000) * X ^ 4 + C (100 * rhoM ^ 2 + 3400 * rhoM - 200 * vv ^ 2
    - 200 * vv + 16600) * X ^ 3 + C (700 * rhoM ^ 2 - 300 * rhoM * vv ^ 2 - 300 * rhoM * vv +
    13900 * rhoM - 2000 * vv ^ 2 - 2000 * vv + 42600) * X ^ 2 + C (-100 * rhoM ^ 2 * vv ^ 2 - 100
    * rhoM ^ 2 * vv + 1600 * rhoM ^ 2 - 1900 * rhoM * vv ^ 2 - 1900 * rhoM * vv + 24400 * rhoM -
    5400 * vv ^ 2 - 5400 * vv + 50400) * X + C (-200 * rhoM ^ 2 * vv ^ 2 - 200 * rhoM ^ 2 * vv +
    1200 * rhoM ^ 2 - 2600 * rhoM * vv ^ 2 - 2600 * rhoM * vv + 15600 * rhoM - 3600 * vv ^ 2 -
    3600 * vv + 21600)

noncomputable def VU16 : P :=
  C (100) * X ^ 5 + C (150 * rhoM + 1200) * X ^ 4 + C (50 * rhoM ^ 2 + 1250 * rhoM - 100 * vv ^ 2
    + 200 * vv + 4700) * X ^ 3 + C (200 * rhoM ^ 2 - 150 * rhoM * vv ^ 2 + 300 * rhoM * vv + 3200
    * rhoM - 1000 * vv ^ 2 + 2000 * vv + 7200) * X ^ 2 + C (-50 * rhoM ^ 2 * vv ^ 2 + 100 * rhoM ^
    2 * vv + 200 * rhoM ^ 2 - 950 * rhoM * vv ^ 2 + 1900 * rhoM * vv + 2600 * rhoM - 2700 * vv ^ 2
    + 5400 * vv + 3600) * X + C (-100 * rhoM ^ 2 * vv ^ 2 + 200 * rhoM ^ 2 * vv - 1300 * rhoM * vv
    ^ 2 + 2600 * rhoM * vv - 1800 * vv ^ 2 + 3600 * vv)

noncomputable def VU17 : P :=
  C (50) * X ^ 5 + C (75 * rhoM + 900) * X ^ 4 + C (25 * rhoM ^ 2 + 1075 * rhoM - 50 * vv ^ 2 -
    200 * vv + 5950) * X ^ 3 + C (250 * rhoM ^ 2 - 75 * rhoM * vv ^ 2 - 300 * rhoM * vv + 5350 *
    rhoM - 500 * vv ^ 2 - 2000 * vv + 17700) * X ^ 2 + C (-25 * rhoM ^ 2 * vv ^ 2 - 100 * rhoM ^ 2
    * vv + 700 * rhoM ^ 2 - 475 * rhoM * vv ^ 2 - 1900 * rhoM * vv + 10900 * rhoM - 1350 * vv ^ 2
    - 5400 * vv + 23400) * X + C (-50 * rhoM ^ 2 * vv ^ 2 - 200 * rhoM ^ 2 * vv + 600 * rhoM ^ 2 -
    650 * rhoM * vv ^ 2 - 2600 * rhoM * vv + 7800 * rhoM - 900 * vv ^ 2 - 3600 * vv + 10800)

noncomputable def VU18 : P :=
  C (108) * X ^ 5 + C (162 * rhoM + 1656) * X ^ 4 + C (54 * rhoM ^ 2 + 1890 * rhoM - 108 * vv ^ 2
    + 144 * vv + 9396) * X ^ 3 + C (396 * rhoM ^ 2 - 162 * rhoM * vv ^ 2 + 216 * rhoM * vv + 7956
    * rhoM - 1080 * vv ^ 2 + 1440 * vv + 24696) * X ^ 2 + C (-54 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^
    2 * vv + 936 * rhoM ^ 2 - 1026 * rhoM * vv ^ 2 + 1368 * rhoM * vv + 14328 * rhoM - 2916 * vv ^
    2 + 3888 * vv + 29808) * X + C (-108 * rhoM ^ 2 * vv ^ 2 + 144 * rhoM ^ 2 * vv + 720 * rhoM ^
    2 - 1404 * rhoM * vv ^ 2 + 1872 * rhoM * vv + 9360 * rhoM - 1944 * vv ^ 2 + 2592 * vv + 12960)

noncomputable def VU19 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 864) * X ^ 4 + C (36 * rhoM ^ 2 + 900 * rhoM - 72 * vv ^ 2 -
    144 * vv + 3384) * X ^ 3 + C (144 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 - 216 * rhoM * vv + 2304 *
    rhoM - 720 * vv ^ 2 - 1440 * vv + 5184) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 *
    vv + 144 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1944 * vv ^ 2 -
    3888 * vv + 2592) * X + C (-72 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 936 * rhoM * vv ^ 2
    - 1872 * rhoM * vv - 1296 * vv ^ 2 - 2592 * vv)

noncomputable def VU20 : P :=
  C (54) * X ^ 5 + C (81 * rhoM + 828) * X ^ 4 + C (27 * rhoM ^ 2 + 945 * rhoM - 54 * vv ^ 2 + 72
    * vv + 4698) * X ^ 3 + C (198 * rhoM ^ 2 - 81 * rhoM * vv ^ 2 + 108 * rhoM * vv + 3978 * rhoM
    - 540 * vv ^ 2 + 720 * vv + 12348) * X ^ 2 + C (-27 * rhoM ^ 2 * vv ^ 2 + 36 * rhoM ^ 2 * vv +
    468 * rhoM ^ 2 - 513 * rhoM * vv ^ 2 + 684 * rhoM * vv + 7164 * rhoM - 1458 * vv ^ 2 + 1944 *
    vv + 14904) * X + C (-54 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 702 *
    rhoM * vv ^ 2 + 936 * rhoM * vv + 4680 * rhoM - 972 * vv ^ 2 + 1296 * vv + 6480)

noncomputable def VU21 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 432) * X ^ 4 + C (18 * rhoM ^ 2 + 450 * rhoM - 36 * vv ^ 2 - 72
    * vv + 1692) * X ^ 3 + C (72 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 - 108 * rhoM * vv + 1152 * rhoM -
    360 * vv ^ 2 - 720 * vv + 2592) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 342 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 972 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 648 * vv ^ 2 - 1296 * vv)

noncomputable def VU22 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 864) * X ^ 4 + C (36 * rhoM ^ 2 + 900 * rhoM - 72 * vv ^ 2 -
    144 * vv + 3384) * X ^ 3 + C (144 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 - 216 * rhoM * vv + 2304 *
    rhoM - 720 * vv ^ 2 - 1440 * vv + 5184) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 *
    vv + 144 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1944 * vv ^ 2 -
    3888 * vv + 2592) * X + C (-72 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 936 * rhoM * vv ^ 2
    - 1872 * rhoM * vv - 1296 * vv ^ 2 - 2592 * vv)

noncomputable def VU23 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 816) * X ^ 4 + C (24 * rhoM ^ 2 + 960 * rhoM - 48 * vv ^ 2 + 144
    * vv + 5136) * X ^ 3 + C (216 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 + 216 * rhoM * vv + 4536 * rhoM
    - 480 * vv ^ 2 + 1440 * vv + 14736) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv
    + 576 * rhoM ^ 2 - 456 * rhoM * vv ^ 2 + 1368 * rhoM * vv + 8928 * rhoM - 1296 * vv ^ 2 + 3888
    * vv + 19008) * X + C (-48 * rhoM ^ 2 * vv ^ 2 + 144 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 - 624 *
    rhoM * vv ^ 2 + 1872 * rhoM * vv + 6240 * rhoM - 864 * vv ^ 2 + 2592 * vv + 8640)

noncomputable def VU24 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 432) * X ^ 4 + C (18 * rhoM ^ 2 + 450 * rhoM - 36 * vv ^ 2 - 72
    * vv + 1692) * X ^ 3 + C (72 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 - 108 * rhoM * vv + 1152 * rhoM -
    360 * vv ^ 2 - 720 * vv + 2592) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 342 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 972 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 648 * vv ^ 2 - 1296 * vv)

noncomputable def VU25 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 408) * X ^ 4 + C (12 * rhoM ^ 2 + 480 * rhoM - 24 * vv ^ 2 + 72
    * vv + 2568) * X ^ 3 + C (108 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 108 * rhoM * vv + 2268 * rhoM
    - 240 * vv ^ 2 + 720 * vv + 7368) * X ^ 2 + C (-12 * rhoM ^ 2 * vv ^ 2 + 36 * rhoM ^ 2 * vv +
    288 * rhoM ^ 2 - 228 * rhoM * vv ^ 2 + 684 * rhoM * vv + 4464 * rhoM - 648 * vv ^ 2 + 1944 *
    vv + 9504) * X + C (-24 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 312 * rhoM
    * vv ^ 2 + 936 * rhoM * vv + 3120 * rhoM - 432 * vv ^ 2 + 1296 * vv + 4320)

noncomputable def VU26 : P :=
  C (108) * X ^ 5 + C (162 * rhoM + 1656) * X ^ 4 + C (54 * rhoM ^ 2 + 1890 * rhoM - 108 * vv ^ 2
    + 144 * vv + 9396) * X ^ 3 + C (396 * rhoM ^ 2 - 162 * rhoM * vv ^ 2 + 216 * rhoM * vv + 7956
    * rhoM - 1080 * vv ^ 2 + 1440 * vv + 24696) * X ^ 2 + C (-54 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^
    2 * vv + 936 * rhoM ^ 2 - 1026 * rhoM * vv ^ 2 + 1368 * rhoM * vv + 14328 * rhoM - 2916 * vv ^
    2 + 3888 * vv + 29808) * X + C (-108 * rhoM ^ 2 * vv ^ 2 + 144 * rhoM ^ 2 * vv + 720 * rhoM ^
    2 - 1404 * rhoM * vv ^ 2 + 1872 * rhoM * vv + 9360 * rhoM - 1944 * vv ^ 2 + 2592 * vv + 12960)

noncomputable def VU27 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 864) * X ^ 4 + C (36 * rhoM ^ 2 + 900 * rhoM - 72 * vv ^ 2 -
    144 * vv + 3384) * X ^ 3 + C (144 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 - 216 * rhoM * vv + 2304 *
    rhoM - 720 * vv ^ 2 - 1440 * vv + 5184) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 *
    vv + 144 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1944 * vv ^ 2 -
    3888 * vv + 2592) * X + C (-72 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 936 * rhoM * vv ^ 2
    - 1872 * rhoM * vv - 1296 * vv ^ 2 - 2592 * vv)

noncomputable def VU28 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 816) * X ^ 4 + C (24 * rhoM ^ 2 + 960 * rhoM - 48 * vv ^ 2 + 144
    * vv + 5136) * X ^ 3 + C (216 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 + 216 * rhoM * vv + 4536 * rhoM
    - 480 * vv ^ 2 + 1440 * vv + 14736) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv
    + 576 * rhoM ^ 2 - 456 * rhoM * vv ^ 2 + 1368 * rhoM * vv + 8928 * rhoM - 1296 * vv ^ 2 + 3888
    * vv + 19008) * X + C (-48 * rhoM ^ 2 * vv ^ 2 + 144 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 - 624 *
    rhoM * vv ^ 2 + 1872 * rhoM * vv + 6240 * rhoM - 864 * vv ^ 2 + 2592 * vv + 8640)

noncomputable def VU29 : P :=
  C (54) * X ^ 5 + C (81 * rhoM + 828) * X ^ 4 + C (27 * rhoM ^ 2 + 945 * rhoM - 54 * vv ^ 2 + 72
    * vv + 4698) * X ^ 3 + C (198 * rhoM ^ 2 - 81 * rhoM * vv ^ 2 + 108 * rhoM * vv + 3978 * rhoM
    - 540 * vv ^ 2 + 720 * vv + 12348) * X ^ 2 + C (-27 * rhoM ^ 2 * vv ^ 2 + 36 * rhoM ^ 2 * vv +
    468 * rhoM ^ 2 - 513 * rhoM * vv ^ 2 + 684 * rhoM * vv + 7164 * rhoM - 1458 * vv ^ 2 + 1944 *
    vv + 14904) * X + C (-54 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 702 *
    rhoM * vv ^ 2 + 936 * rhoM * vv + 4680 * rhoM - 972 * vv ^ 2 + 1296 * vv + 6480)

noncomputable def VU30 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 432) * X ^ 4 + C (18 * rhoM ^ 2 + 450 * rhoM - 36 * vv ^ 2 - 72
    * vv + 1692) * X ^ 3 + C (72 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 - 108 * rhoM * vv + 1152 * rhoM -
    360 * vv ^ 2 - 720 * vv + 2592) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 342 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 972 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-36 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 648 * vv ^ 2 - 1296 * vv)

noncomputable def VU31 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 408) * X ^ 4 + C (12 * rhoM ^ 2 + 480 * rhoM - 24 * vv ^ 2 + 72
    * vv + 2568) * X ^ 3 + C (108 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 108 * rhoM * vv + 2268 * rhoM
    - 240 * vv ^ 2 + 720 * vv + 7368) * X ^ 2 + C (-12 * rhoM ^ 2 * vv ^ 2 + 36 * rhoM ^ 2 * vv +
    288 * rhoM ^ 2 - 228 * rhoM * vv ^ 2 + 684 * rhoM * vv + 4464 * rhoM - 648 * vv ^ 2 + 1944 *
    vv + 9504) * X + C (-24 * rhoM ^ 2 * vv ^ 2 + 72 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 312 * rhoM
    * vv ^ 2 + 936 * rhoM * vv + 3120 * rhoM - 432 * vv ^ 2 + 1296 * vv + 4320)

noncomputable def VU32 : P :=
  C (120) * X ^ 5 + C (180 * rhoM + 1800) * X ^ 4 + C (60 * rhoM ^ 2 + 2040 * rhoM - 120 * vv ^ 2
    - 120 * vv + 9960) * X ^ 3 + C (420 * rhoM ^ 2 - 180 * rhoM * vv ^ 2 - 180 * rhoM * vv + 8340
    * rhoM - 1200 * vv ^ 2 - 1200 * vv + 25560) * X ^ 2 + C (-60 * rhoM ^ 2 * vv ^ 2 - 60 * rhoM ^
    2 * vv + 960 * rhoM ^ 2 - 1140 * rhoM * vv ^ 2 - 1140 * rhoM * vv + 14640 * rhoM - 3240 * vv ^
    2 - 3240 * vv + 30240) * X + C (-120 * rhoM ^ 2 * vv ^ 2 - 120 * rhoM ^ 2 * vv + 720 * rhoM ^
    2 - 1560 * rhoM * vv ^ 2 - 1560 * rhoM * vv + 9360 * rhoM - 2160 * vv ^ 2 - 2160 * vv + 12960)

noncomputable def VU33 : P :=
  C (80) * X ^ 5 + C (120 * rhoM + 1200) * X ^ 4 + C (40 * rhoM ^ 2 + 1360 * rhoM - 80 * vv ^ 2 -
    80 * vv + 6640) * X ^ 3 + C (280 * rhoM ^ 2 - 120 * rhoM * vv ^ 2 - 120 * rhoM * vv + 5560 *
    rhoM - 800 * vv ^ 2 - 800 * vv + 17040) * X ^ 2 + C (-40 * rhoM ^ 2 * vv ^ 2 - 40 * rhoM ^ 2 *
    vv + 640 * rhoM ^ 2 - 760 * rhoM * vv ^ 2 - 760 * rhoM * vv + 9760 * rhoM - 2160 * vv ^ 2 -
    2160 * vv + 20160) * X + C (-80 * rhoM ^ 2 * vv ^ 2 - 80 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 -
    1040 * rhoM * vv ^ 2 - 1040 * rhoM * vv + 6240 * rhoM - 1440 * vv ^ 2 - 1440 * vv + 8640)

noncomputable def VU34 : P :=
  C (60) * X ^ 5 + C (90 * rhoM + 720) * X ^ 4 + C (30 * rhoM ^ 2 + 750 * rhoM - 60 * vv ^ 2 + 120
    * vv + 2820) * X ^ 3 + C (120 * rhoM ^ 2 - 90 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1920 * rhoM
    - 600 * vv ^ 2 + 1200 * vv + 4320) * X ^ 2 + C (-30 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 570 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 1620 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-60 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 780 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 1080 * vv ^ 2 + 2160 * vv)

noncomputable def VU35 : P :=
  C (40) * X ^ 5 + C (60 * rhoM + 480) * X ^ 4 + C (20 * rhoM ^ 2 + 500 * rhoM - 40 * vv ^ 2 + 80
    * vv + 1880) * X ^ 3 + C (80 * rhoM ^ 2 - 60 * rhoM * vv ^ 2 + 120 * rhoM * vv + 1280 * rhoM -
    400 * vv ^ 2 + 800 * vv + 2880) * X ^ 2 + C (-20 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 380 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 1080 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-40 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 520 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 720 * vv ^ 2 + 1440 * vv)

noncomputable def VU36 : P :=
  C (120) * X ^ 5 + C (180 * rhoM + 1800) * X ^ 4 + C (60 * rhoM ^ 2 + 2040 * rhoM - 120 * vv ^ 2
    - 120 * vv + 9960) * X ^ 3 + C (420 * rhoM ^ 2 - 180 * rhoM * vv ^ 2 - 180 * rhoM * vv + 8340
    * rhoM - 1200 * vv ^ 2 - 1200 * vv + 25560) * X ^ 2 + C (-60 * rhoM ^ 2 * vv ^ 2 - 60 * rhoM ^
    2 * vv + 960 * rhoM ^ 2 - 1140 * rhoM * vv ^ 2 - 1140 * rhoM * vv + 14640 * rhoM - 3240 * vv ^
    2 - 3240 * vv + 30240) * X + C (-120 * rhoM ^ 2 * vv ^ 2 - 120 * rhoM ^ 2 * vv + 720 * rhoM ^
    2 - 1560 * rhoM * vv ^ 2 - 1560 * rhoM * vv + 9360 * rhoM - 2160 * vv ^ 2 - 2160 * vv + 12960)

noncomputable def VU37 : P :=
  C (80) * X ^ 5 + C (120 * rhoM + 1200) * X ^ 4 + C (40 * rhoM ^ 2 + 1360 * rhoM - 80 * vv ^ 2 -
    80 * vv + 6640) * X ^ 3 + C (280 * rhoM ^ 2 - 120 * rhoM * vv ^ 2 - 120 * rhoM * vv + 5560 *
    rhoM - 800 * vv ^ 2 - 800 * vv + 17040) * X ^ 2 + C (-40 * rhoM ^ 2 * vv ^ 2 - 40 * rhoM ^ 2 *
    vv + 640 * rhoM ^ 2 - 760 * rhoM * vv ^ 2 - 760 * rhoM * vv + 9760 * rhoM - 2160 * vv ^ 2 -
    2160 * vv + 20160) * X + C (-80 * rhoM ^ 2 * vv ^ 2 - 80 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 -
    1040 * rhoM * vv ^ 2 - 1040 * rhoM * vv + 6240 * rhoM - 1440 * vv ^ 2 - 1440 * vv + 8640)

noncomputable def VU38 : P :=
  C (60) * X ^ 5 + C (90 * rhoM + 720) * X ^ 4 + C (30 * rhoM ^ 2 + 750 * rhoM - 60 * vv ^ 2 + 120
    * vv + 2820) * X ^ 3 + C (120 * rhoM ^ 2 - 90 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1920 * rhoM
    - 600 * vv ^ 2 + 1200 * vv + 4320) * X ^ 2 + C (-30 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 570 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 1620 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-60 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 780 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 1080 * vv ^ 2 + 2160 * vv)

noncomputable def VU39 : P :=
  C (40) * X ^ 5 + C (60 * rhoM + 480) * X ^ 4 + C (20 * rhoM ^ 2 + 500 * rhoM - 40 * vv ^ 2 + 80
    * vv + 1880) * X ^ 3 + C (80 * rhoM ^ 2 - 60 * rhoM * vv ^ 2 + 120 * rhoM * vv + 1280 * rhoM -
    400 * vv ^ 2 + 800 * vv + 2880) * X ^ 2 + C (-20 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 380 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 1080 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-40 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 520 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 720 * vv ^ 2 + 1440 * vv)

noncomputable def VU40 : P :=
  C (30) * X ^ 5 + C (45 * rhoM + 540) * X ^ 4 + C (15 * rhoM ^ 2 + 645 * rhoM - 30 * vv ^ 2 - 120
    * vv + 3570) * X ^ 3 + C (150 * rhoM ^ 2 - 45 * rhoM * vv ^ 2 - 180 * rhoM * vv + 3210 * rhoM
    - 300 * vv ^ 2 - 1200 * vv + 10620) * X ^ 2 + C (-15 * rhoM ^ 2 * vv ^ 2 - 60 * rhoM ^ 2 * vv
    + 420 * rhoM ^ 2 - 285 * rhoM * vv ^ 2 - 1140 * rhoM * vv + 6540 * rhoM - 810 * vv ^ 2 - 3240
    * vv + 14040) * X + C (-30 * rhoM ^ 2 * vv ^ 2 - 120 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 390 *
    rhoM * vv ^ 2 - 1560 * rhoM * vv + 4680 * rhoM - 540 * vv ^ 2 - 2160 * vv + 6480)

noncomputable def VU41 : P :=
  C (20) * X ^ 5 + C (30 * rhoM + 360) * X ^ 4 + C (10 * rhoM ^ 2 + 430 * rhoM - 20 * vv ^ 2 - 80
    * vv + 2380) * X ^ 3 + C (100 * rhoM ^ 2 - 30 * rhoM * vv ^ 2 - 120 * rhoM * vv + 2140 * rhoM
    - 200 * vv ^ 2 - 800 * vv + 7080) * X ^ 2 + C (-10 * rhoM ^ 2 * vv ^ 2 - 40 * rhoM ^ 2 * vv +
    280 * rhoM ^ 2 - 190 * rhoM * vv ^ 2 - 760 * rhoM * vv + 4360 * rhoM - 540 * vv ^ 2 - 2160 *
    vv + 9360) * X + C (-20 * rhoM ^ 2 * vv ^ 2 - 80 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 260 * rhoM
    * vv ^ 2 - 1040 * rhoM * vv + 3120 * rhoM - 360 * vv ^ 2 - 1440 * vv + 4320)

noncomputable def VU42 : P :=
  C (60) * X ^ 5 + C (90 * rhoM + 720) * X ^ 4 + C (30 * rhoM ^ 2 + 750 * rhoM - 60 * vv ^ 2 + 120
    * vv + 2820) * X ^ 3 + C (120 * rhoM ^ 2 - 90 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1920 * rhoM
    - 600 * vv ^ 2 + 1200 * vv + 4320) * X ^ 2 + C (-30 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 570 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 1620 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-60 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 780 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 1080 * vv ^ 2 + 2160 * vv)

noncomputable def VU43 : P :=
  C (40) * X ^ 5 + C (60 * rhoM + 480) * X ^ 4 + C (20 * rhoM ^ 2 + 500 * rhoM - 40 * vv ^ 2 + 80
    * vv + 1880) * X ^ 3 + C (80 * rhoM ^ 2 - 60 * rhoM * vv ^ 2 + 120 * rhoM * vv + 1280 * rhoM -
    400 * vv ^ 2 + 800 * vv + 2880) * X ^ 2 + C (-20 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 380 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 1080 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-40 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 520 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 720 * vv ^ 2 + 1440 * vv)

noncomputable def VU44 : P :=
  C (30) * X ^ 5 + C (45 * rhoM + 540) * X ^ 4 + C (15 * rhoM ^ 2 + 645 * rhoM - 30 * vv ^ 2 - 120
    * vv + 3570) * X ^ 3 + C (150 * rhoM ^ 2 - 45 * rhoM * vv ^ 2 - 180 * rhoM * vv + 3210 * rhoM
    - 300 * vv ^ 2 - 1200 * vv + 10620) * X ^ 2 + C (-15 * rhoM ^ 2 * vv ^ 2 - 60 * rhoM ^ 2 * vv
    + 420 * rhoM ^ 2 - 285 * rhoM * vv ^ 2 - 1140 * rhoM * vv + 6540 * rhoM - 810 * vv ^ 2 - 3240
    * vv + 14040) * X + C (-30 * rhoM ^ 2 * vv ^ 2 - 120 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 390 *
    rhoM * vv ^ 2 - 1560 * rhoM * vv + 4680 * rhoM - 540 * vv ^ 2 - 2160 * vv + 6480)

noncomputable def VU45 : P :=
  C (20) * X ^ 5 + C (30 * rhoM + 360) * X ^ 4 + C (10 * rhoM ^ 2 + 430 * rhoM - 20 * vv ^ 2 - 80
    * vv + 2380) * X ^ 3 + C (100 * rhoM ^ 2 - 30 * rhoM * vv ^ 2 - 120 * rhoM * vv + 2140 * rhoM
    - 200 * vv ^ 2 - 800 * vv + 7080) * X ^ 2 + C (-10 * rhoM ^ 2 * vv ^ 2 - 40 * rhoM ^ 2 * vv +
    280 * rhoM ^ 2 - 190 * rhoM * vv ^ 2 - 760 * rhoM * vv + 4360 * rhoM - 540 * vv ^ 2 - 2160 *
    vv + 9360) * X + C (-20 * rhoM ^ 2 * vv ^ 2 - 80 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 260 * rhoM
    * vv ^ 2 - 1040 * rhoM * vv + 3120 * rhoM - 360 * vv ^ 2 - 1440 * vv + 4320)

noncomputable def VU46 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 1200) * X ^ 4 + C (36 * rhoM ^ 2 + 1380 * rhoM - 72 * vv ^ 2 +
    24 * vv + 7440) * X ^ 3 + C (300 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 + 36 * rhoM * vv + 6372 *
    rhoM - 744 * vv ^ 2 + 240 * vv + 21240) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 + 12 * rhoM ^ 2 *
    vv + 816 * rhoM ^ 2 - 696 * rhoM * vv ^ 2 + 228 * rhoM * vv + 12768 * rhoM - 2160 * vv ^ 2 +
    648 * vv + 27648) * X + C (-72 * rhoM ^ 2 * vv ^ 2 + 24 * rhoM ^ 2 * vv + 720 * rhoM ^ 2 - 960
    * rhoM * vv ^ 2 + 312 * rhoM * vv + 9360 * rhoM - 1728 * vv ^ 2 + 432 * vv + 12960)

noncomputable def VU47 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 600) * X ^ 4 + C (24 * rhoM ^ 2 + 660 * rhoM - 48 * vv ^ 2 - 144
    * vv + 2520) * X ^ 3 + C (120 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 - 216 * rhoM * vv + 1968 * rhoM
    - 456 * vv ^ 2 - 1440 * vv + 4320) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv +
    144 * rhoM ^ 2 - 444 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1080 * vv ^ 2 - 3888 *
    vv + 2592) * X + C (-48 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 600 * rhoM * vv ^ 2 - 1872
    * rhoM * vv - 432 * vv ^ 2 - 2592 * vv)

noncomputable def VU48 : P :=
  C (32) * X ^ 5 + C (48 * rhoM + 600) * X ^ 4 + C (16 * rhoM ^ 2 + 700 * rhoM - 32 * vv ^ 2 + 64
    * vv + 4120) * X ^ 3 + C (160 * rhoM ^ 2 - 48 * rhoM * vv ^ 2 + 96 * rhoM * vv + 3592 * rhoM -
    344 * vv ^ 2 + 640 * vv + 12720) * X ^ 2 + C (-16 * rhoM ^ 2 * vv ^ 2 + 32 * rhoM ^ 2 * vv +
    496 * rhoM ^ 2 - 316 * rhoM * vv ^ 2 + 608 * rhoM * vv + 7888 * rhoM - 1080 * vv ^ 2 + 1728 *
    vv + 17568) * X + C (-32 * rhoM ^ 2 * vv ^ 2 + 64 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 - 440 *
    rhoM * vv ^ 2 + 832 * rhoM * vv + 6240 * rhoM - 1008 * vv ^ 2 + 1152 * vv + 8640)

noncomputable def VU49 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 456) * X ^ 4 + C (18 * rhoM ^ 2 + 510 * rhoM - 36 * vv ^ 2 + 120
    * vv + 1956) * X ^ 3 + C (96 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1584 * rhoM -
    336 * vv ^ 2 + 1200 * vv + 3456) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 330 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 756 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-36 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 444 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 216 * vv ^ 2 + 2160 * vv)

noncomputable def VU50 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 264) * X ^ 4 + C (12 * rhoM ^ 2 + 240 * rhoM - 24 * vv ^ 2 +
    864) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 336 * rhoM - 264 * vv ^ 2 + 864) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 240 * rhoM * vv ^ 2 - 864 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 336 * rhoM * vv ^ 2 - 864 * vv ^ 2)

noncomputable def VU51 : P :=
  C (18) * X ^ 5 + C (27 * rhoM + 372) * X ^ 4 + C (9 * rhoM ^ 2 + 435 * rhoM - 18 * vv ^ 2 - 48 *
    vv + 2742) * X ^ 3 + C (102 * rhoM ^ 2 - 27 * rhoM * vv ^ 2 - 72 * rhoM * vv + 2394 * rhoM -
    204 * vv ^ 2 - 480 * vv + 8892) * X ^ 2 + C (-9 * rhoM ^ 2 * vv ^ 2 - 24 * rhoM ^ 2 * vv + 348
    * rhoM ^ 2 - 183 * rhoM * vv ^ 2 - 456 * rhoM * vv + 5604 * rhoM - 702 * vv ^ 2 - 1296 * vv +
    12744) * X + C (-18 * rhoM ^ 2 * vv ^ 2 - 48 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 258 * rhoM *
    vv ^ 2 - 624 * rhoM * vv + 4680 * rhoM - 756 * vv ^ 2 - 864 * vv + 6480)

noncomputable def VU52 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 264) * X ^ 4 + C (12 * rhoM ^ 2 + 240 * rhoM - 24 * vv ^ 2 +
    864) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 336 * rhoM - 264 * vv ^ 2 + 864) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 240 * rhoM * vv ^ 2 - 864 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 336 * rhoM * vv ^ 2 - 864 * vv ^ 2)

noncomputable def VU53 : P :=
  C (16) * X ^ 5 + C (24 * rhoM + 216) * X ^ 4 + C (8 * rhoM ^ 2 + 260 * rhoM - 16 * vv ^ 2 + 80 *
    vv + 1016) * X ^ 3 + C (56 * rhoM ^ 2 - 24 * rhoM * vv ^ 2 + 120 * rhoM * vv + 944 * rhoM -
    136 * vv ^ 2 + 800 * vv + 2016) * X ^ 2 + C (-8 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 140 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 216 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-16 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 184 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv + 144 * vv ^ 2 + 1440 * vv)

noncomputable def VU54 : P :=
  C (12) * X ^ 5 + C (18 * rhoM + 168) * X ^ 4 + C (6 * rhoM ^ 2 + 210 * rhoM - 12 * vv ^ 2 - 72 *
    vv + 828) * X ^ 3 + C (48 * rhoM ^ 2 - 18 * rhoM * vv ^ 2 - 108 * rhoM * vv + 816 * rhoM - 96
    * vv ^ 2 - 720 * vv + 1728) * X ^ 2 + C (-6 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72 *
    rhoM ^ 2 - 102 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 108 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-12 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 132 * rhoM * vv ^ 2 - 936 * rhoM
    * vv + 216 * vv ^ 2 - 1296 * vv)

noncomputable def VU55 : P :=
  C (8) * X ^ 5 + C (12 * rhoM + 192) * X ^ 4 + C (4 * rhoM ^ 2 + 220 * rhoM - 8 * vv ^ 2 - 8 * vv
    + 1552) * X ^ 3 + C (52 * rhoM ^ 2 - 12 * rhoM * vv ^ 2 - 12 * rhoM * vv + 1324 * rhoM - 104 *
    vv ^ 2 - 80 * vv + 5352) * X ^ 2 + C (-4 * rhoM ^ 2 * vv ^ 2 - 4 * rhoM ^ 2 * vv + 208 * rhoM
    ^ 2 - 88 * rhoM * vv ^ 2 - 76 * rhoM * vv + 3424 * rhoM - 432 * vv ^ 2 - 216 * vv + 8064) * X
    + C (-8 * rhoM ^ 2 * vv ^ 2 - 8 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 128 * rhoM * vv ^ 2 - 104 *
    rhoM * vv + 3120 * rhoM - 576 * vv ^ 2 - 144 * vv + 4320)

noncomputable def VU56 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 1176) * X ^ 4 + C (36 * rhoM ^ 2 + 1368 * rhoM - 72 * vv ^ 2 +
    24 * vv + 7248) * X ^ 3 + C (300 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 + 36 * rhoM * vv + 6348 *
    rhoM - 720 * vv ^ 2 + 240 * vv + 20952) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 + 12 * rhoM ^ 2 *
    vv + 816 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 + 228 * rhoM * vv + 12768 * rhoM - 1968 * vv ^ 2 +
    648 * vv + 27648) * X + C (-72 * rhoM ^ 2 * vv ^ 2 + 24 * rhoM ^ 2 * vv + 720 * rhoM ^ 2 - 936
    * rhoM * vv ^ 2 + 312 * rhoM * vv + 9360 * rhoM - 1440 * vv ^ 2 + 432 * vv + 12960)

noncomputable def VU57 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 624) * X ^ 4 + C (24 * rhoM ^ 2 + 672 * rhoM - 48 * vv ^ 2 - 144
    * vv + 2712) * X ^ 3 + C (120 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 - 216 * rhoM * vv + 1992 * rhoM
    - 480 * vv ^ 2 - 1440 * vv + 4608) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv +
    144 * rhoM ^ 2 - 456 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1272 * vv ^ 2 - 3888 *
    vv + 2592) * X + C (-48 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 624 * rhoM * vv ^ 2 - 1872
    * rhoM * vv - 720 * vv ^ 2 - 2592 * vv)

noncomputable def VU58 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 480) * X ^ 4 + C (18 * rhoM ^ 2 + 522 * rhoM - 36 * vv ^ 2 + 120
    * vv + 2148) * X ^ 3 + C (96 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1608 * rhoM -
    360 * vv ^ 2 + 1200 * vv + 3744) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 342 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 948 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-36 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 504 * vv ^ 2 + 2160 * vv)

noncomputable def VU59 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 240) * X ^ 4 + C (12 * rhoM ^ 2 + 228 * rhoM - 24 * vv ^ 2 +
    672) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 312 * rhoM - 240 * vv ^ 2 + 576) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 228 * rhoM * vv ^ 2 - 672 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 312 * rhoM * vv ^ 2 - 576 * vv ^ 2)

noncomputable def VU60 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 624) * X ^ 4 + C (24 * rhoM ^ 2 + 672 * rhoM - 48 * vv ^ 2 - 144
    * vv + 2712) * X ^ 3 + C (120 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 - 216 * rhoM * vv + 1992 * rhoM
    - 480 * vv ^ 2 - 1440 * vv + 4608) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv +
    144 * rhoM ^ 2 - 456 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1272 * vv ^ 2 - 3888 *
    vv + 2592) * X + C (-48 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 624 * rhoM * vv ^ 2 - 1872
    * rhoM * vv - 720 * vv ^ 2 - 2592 * vv)

noncomputable def VU61 : P :=
  C (32) * X ^ 5 + C (48 * rhoM + 576) * X ^ 4 + C (16 * rhoM ^ 2 + 688 * rhoM - 32 * vv ^ 2 + 64
    * vv + 3928) * X ^ 3 + C (160 * rhoM ^ 2 - 48 * rhoM * vv ^ 2 + 96 * rhoM * vv + 3568 * rhoM -
    320 * vv ^ 2 + 640 * vv + 12432) * X ^ 2 + C (-16 * rhoM ^ 2 * vv ^ 2 + 32 * rhoM ^ 2 * vv +
    496 * rhoM ^ 2 - 304 * rhoM * vv ^ 2 + 608 * rhoM * vv + 7888 * rhoM - 888 * vv ^ 2 + 1728 *
    vv + 17568) * X + C (-32 * rhoM ^ 2 * vv ^ 2 + 64 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 - 416 *
    rhoM * vv ^ 2 + 832 * rhoM * vv + 6240 * rhoM - 720 * vv ^ 2 + 1152 * vv + 8640)

noncomputable def VU62 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 240) * X ^ 4 + C (12 * rhoM ^ 2 + 228 * rhoM - 24 * vv ^ 2 +
    672) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 312 * rhoM - 240 * vv ^ 2 + 576) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 228 * rhoM * vv ^ 2 - 672 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 312 * rhoM * vv ^ 2 - 576 * vv ^ 2)

noncomputable def VU63 : P :=
  C (16) * X ^ 5 + C (24 * rhoM + 240) * X ^ 4 + C (8 * rhoM ^ 2 + 272 * rhoM - 16 * vv ^ 2 + 80 *
    vv + 1208) * X ^ 3 + C (56 * rhoM ^ 2 - 24 * rhoM * vv ^ 2 + 120 * rhoM * vv + 968 * rhoM -
    160 * vv ^ 2 + 800 * vv + 2304) * X ^ 2 + C (-8 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 152 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 408 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-16 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 208 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 144 * vv ^ 2 + 1440 * vv)

noncomputable def VU64 : P :=
  C (72) * X ^ 5 + C (108 * rhoM + 1176) * X ^ 4 + C (36 * rhoM ^ 2 + 1368 * rhoM - 72 * vv ^ 2 +
    24 * vv + 7224) * X ^ 3 + C (300 * rhoM ^ 2 - 108 * rhoM * vv ^ 2 + 36 * rhoM * vv + 6348 *
    rhoM - 720 * vv ^ 2 + 240 * vv + 20904) * X ^ 2 + C (-36 * rhoM ^ 2 * vv ^ 2 + 12 * rhoM ^ 2 *
    vv + 816 * rhoM ^ 2 - 684 * rhoM * vv ^ 2 + 228 * rhoM * vv + 12768 * rhoM - 1944 * vv ^ 2 +
    648 * vv + 27648) * X + C (-72 * rhoM ^ 2 * vv ^ 2 + 24 * rhoM ^ 2 * vv + 720 * rhoM ^ 2 - 936
    * rhoM * vv ^ 2 + 312 * rhoM * vv + 9360 * rhoM - 1392 * vv ^ 2 + 432 * vv + 12960)

noncomputable def VU65 : P :=
  C (48) * X ^ 5 + C (72 * rhoM + 624) * X ^ 4 + C (24 * rhoM ^ 2 + 672 * rhoM - 48 * vv ^ 2 - 144
    * vv + 2736) * X ^ 3 + C (120 * rhoM ^ 2 - 72 * rhoM * vv ^ 2 - 216 * rhoM * vv + 1992 * rhoM
    - 480 * vv ^ 2 - 1440 * vv + 4656) * X ^ 2 + C (-24 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv +
    144 * rhoM ^ 2 - 456 * rhoM * vv ^ 2 - 1368 * rhoM * vv + 1872 * rhoM - 1296 * vv ^ 2 - 3888 *
    vv + 2592) * X + C (-48 * rhoM ^ 2 * vv ^ 2 - 144 * rhoM ^ 2 * vv - 624 * rhoM * vv ^ 2 - 1872
    * rhoM * vv - 768 * vv ^ 2 - 2592 * vv)

noncomputable def VU66 : P :=
  C (32) * X ^ 5 + C (48 * rhoM + 576) * X ^ 4 + C (16 * rhoM ^ 2 + 688 * rhoM - 32 * vv ^ 2 + 64
    * vv + 3904) * X ^ 3 + C (160 * rhoM ^ 2 - 48 * rhoM * vv ^ 2 + 96 * rhoM * vv + 3568 * rhoM -
    320 * vv ^ 2 + 640 * vv + 12384) * X ^ 2 + C (-16 * rhoM ^ 2 * vv ^ 2 + 32 * rhoM ^ 2 * vv +
    496 * rhoM ^ 2 - 304 * rhoM * vv ^ 2 + 608 * rhoM * vv + 7888 * rhoM - 864 * vv ^ 2 + 1728 *
    vv + 17568) * X + C (-32 * rhoM ^ 2 * vv ^ 2 + 64 * rhoM ^ 2 * vv + 480 * rhoM ^ 2 - 416 *
    rhoM * vv ^ 2 + 832 * rhoM * vv + 6240 * rhoM - 672 * vv ^ 2 + 1152 * vv + 8640)

noncomputable def VU67 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 480) * X ^ 4 + C (18 * rhoM ^ 2 + 522 * rhoM - 36 * vv ^ 2 + 120
    * vv + 2148) * X ^ 3 + C (96 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1608 * rhoM -
    360 * vv ^ 2 + 1200 * vv + 3744) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 342 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 948 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-36 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 504 * vv ^ 2 + 2160 * vv)

noncomputable def VU68 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 240) * X ^ 4 + C (12 * rhoM ^ 2 + 228 * rhoM - 24 * vv ^ 2 +
    672) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 312 * rhoM - 240 * vv ^ 2 + 576) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 228 * rhoM * vv ^ 2 - 672 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 312 * rhoM * vv ^ 2 - 576 * vv ^ 2)

noncomputable def VU69 : P :=
  C (18) * X ^ 5 + C (27 * rhoM + 348) * X ^ 4 + C (9 * rhoM ^ 2 + 423 * rhoM - 18 * vv ^ 2 - 48 *
    vv + 2550) * X ^ 3 + C (102 * rhoM ^ 2 - 27 * rhoM * vv ^ 2 - 72 * rhoM * vv + 2370 * rhoM -
    180 * vv ^ 2 - 480 * vv + 8604) * X ^ 2 + C (-9 * rhoM ^ 2 * vv ^ 2 - 24 * rhoM ^ 2 * vv + 348
    * rhoM ^ 2 - 171 * rhoM * vv ^ 2 - 456 * rhoM * vv + 5604 * rhoM - 510 * vv ^ 2 - 1296 * vv +
    12744) * X + C (-18 * rhoM ^ 2 * vv ^ 2 - 48 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 234 * rhoM *
    vv ^ 2 - 624 * rhoM * vv + 4680 * rhoM - 468 * vv ^ 2 - 864 * vv + 6480)

noncomputable def VU70 : P :=
  C (12) * X ^ 5 + C (18 * rhoM + 192) * X ^ 4 + C (6 * rhoM ^ 2 + 222 * rhoM - 12 * vv ^ 2 - 72 *
    vv + 1020) * X ^ 3 + C (48 * rhoM ^ 2 - 18 * rhoM * vv ^ 2 - 108 * rhoM * vv + 840 * rhoM -
    120 * vv ^ 2 - 720 * vv + 2016) * X ^ 2 + C (-6 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 114 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 300 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-12 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 156 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 72 * vv ^ 2 - 1296 * vv)

noncomputable def VU71 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 240) * X ^ 4 + C (12 * rhoM ^ 2 + 228 * rhoM - 24 * vv ^ 2 +
    672) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 312 * rhoM - 240 * vv ^ 2 + 576) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 228 * rhoM * vv ^ 2 - 672 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 312 * rhoM * vv ^ 2 - 576 * vv ^ 2)

noncomputable def VU72 : P :=
  C (16) * X ^ 5 + C (24 * rhoM + 240) * X ^ 4 + C (8 * rhoM ^ 2 + 272 * rhoM - 16 * vv ^ 2 + 80 *
    vv + 1208) * X ^ 3 + C (56 * rhoM ^ 2 - 24 * rhoM * vv ^ 2 + 120 * rhoM * vv + 968 * rhoM -
    160 * vv ^ 2 + 800 * vv + 2304) * X ^ 2 + C (-8 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 152 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 408 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-16 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 208 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 144 * vv ^ 2 + 1440 * vv)

noncomputable def VU73 : P :=
  C (12) * X ^ 5 + C (18 * rhoM + 192) * X ^ 4 + C (6 * rhoM ^ 2 + 222 * rhoM - 12 * vv ^ 2 - 72 *
    vv + 1020) * X ^ 3 + C (48 * rhoM ^ 2 - 18 * rhoM * vv ^ 2 - 108 * rhoM * vv + 840 * rhoM -
    120 * vv ^ 2 - 720 * vv + 2016) * X ^ 2 + C (-6 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 114 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 300 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-12 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 156 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 72 * vv ^ 2 - 1296 * vv)

noncomputable def VU74 : P :=
  C (8) * X ^ 5 + C (12 * rhoM + 168) * X ^ 4 + C (4 * rhoM ^ 2 + 208 * rhoM - 8 * vv ^ 2 - 8 * vv
    + 1360) * X ^ 3 + C (52 * rhoM ^ 2 - 12 * rhoM * vv ^ 2 - 12 * rhoM * vv + 1300 * rhoM - 80 *
    vv ^ 2 - 80 * vv + 5064) * X ^ 2 + C (-4 * rhoM ^ 2 * vv ^ 2 - 4 * rhoM ^ 2 * vv + 208 * rhoM
    ^ 2 - 76 * rhoM * vv ^ 2 - 76 * rhoM * vv + 3424 * rhoM - 240 * vv ^ 2 - 216 * vv + 8064) * X
    + C (-8 * rhoM ^ 2 * vv ^ 2 - 8 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 104 * rhoM * vv ^ 2 - 104 *
    rhoM * vv + 3120 * rhoM - 288 * vv ^ 2 - 144 * vv + 4320)

noncomputable def VU75 : P :=
  C (36) * X ^ 5 + C (54 * rhoM + 480) * X ^ 4 + C (18 * rhoM ^ 2 + 522 * rhoM - 36 * vv ^ 2 + 120
    * vv + 2172) * X ^ 3 + C (96 * rhoM ^ 2 - 54 * rhoM * vv ^ 2 + 180 * rhoM * vv + 1608 * rhoM -
    360 * vv ^ 2 + 1200 * vv + 3792) * X ^ 2 + C (-18 * rhoM ^ 2 * vv ^ 2 + 60 * rhoM ^ 2 * vv +
    120 * rhoM ^ 2 - 342 * rhoM * vv ^ 2 + 1140 * rhoM * vv + 1560 * rhoM - 972 * vv ^ 2 + 3240 *
    vv + 2160) * X + C (-36 * rhoM ^ 2 * vv ^ 2 + 120 * rhoM ^ 2 * vv - 468 * rhoM * vv ^ 2 + 1560
    * rhoM * vv - 552 * vv ^ 2 + 2160 * vv)

noncomputable def VU76 : P :=
  C (24) * X ^ 5 + C (36 * rhoM + 240) * X ^ 4 + C (12 * rhoM ^ 2 + 228 * rhoM - 24 * vv ^ 2 +
    648) * X ^ 3 + C (24 * rhoM ^ 2 - 36 * rhoM * vv ^ 2 + 312 * rhoM - 240 * vv ^ 2 + 528) * X ^
    2 + C (-12 * rhoM ^ 2 * vv ^ 2 - 228 * rhoM * vv ^ 2 - 648 * vv ^ 2) * X + C (-24 * rhoM ^ 2 *
    vv ^ 2 - 312 * rhoM * vv ^ 2 - 528 * vv ^ 2)

noncomputable def VU77 : P :=
  C (16) * X ^ 5 + C (24 * rhoM + 240) * X ^ 4 + C (8 * rhoM ^ 2 + 272 * rhoM - 16 * vv ^ 2 + 80 *
    vv + 1232) * X ^ 3 + C (56 * rhoM ^ 2 - 24 * rhoM * vv ^ 2 + 120 * rhoM * vv + 968 * rhoM -
    160 * vv ^ 2 + 800 * vv + 2352) * X ^ 2 + C (-8 * rhoM ^ 2 * vv ^ 2 + 40 * rhoM ^ 2 * vv + 80
    * rhoM ^ 2 - 152 * rhoM * vv ^ 2 + 760 * rhoM * vv + 1040 * rhoM - 432 * vv ^ 2 + 2160 * vv +
    1440) * X + C (-16 * rhoM ^ 2 * vv ^ 2 + 80 * rhoM ^ 2 * vv - 208 * rhoM * vv ^ 2 + 1040 *
    rhoM * vv - 192 * vv ^ 2 + 1440 * vv)

noncomputable def VU78 : P :=
  C (18) * X ^ 5 + C (27 * rhoM + 348) * X ^ 4 + C (9 * rhoM ^ 2 + 423 * rhoM - 18 * vv ^ 2 - 48 *
    vv + 2526) * X ^ 3 + C (102 * rhoM ^ 2 - 27 * rhoM * vv ^ 2 - 72 * rhoM * vv + 2370 * rhoM -
    180 * vv ^ 2 - 480 * vv + 8556) * X ^ 2 + C (-9 * rhoM ^ 2 * vv ^ 2 - 24 * rhoM ^ 2 * vv + 348
    * rhoM ^ 2 - 171 * rhoM * vv ^ 2 - 456 * rhoM * vv + 5604 * rhoM - 486 * vv ^ 2 - 1296 * vv +
    12744) * X + C (-18 * rhoM ^ 2 * vv ^ 2 - 48 * rhoM ^ 2 * vv + 360 * rhoM ^ 2 - 234 * rhoM *
    vv ^ 2 - 624 * rhoM * vv + 4680 * rhoM - 420 * vv ^ 2 - 864 * vv + 6480)

noncomputable def VU79 : P :=
  C (12) * X ^ 5 + C (18 * rhoM + 192) * X ^ 4 + C (6 * rhoM ^ 2 + 222 * rhoM - 12 * vv ^ 2 - 72 *
    vv + 1044) * X ^ 3 + C (48 * rhoM ^ 2 - 18 * rhoM * vv ^ 2 - 108 * rhoM * vv + 840 * rhoM -
    120 * vv ^ 2 - 720 * vv + 2064) * X ^ 2 + C (-6 * rhoM ^ 2 * vv ^ 2 - 36 * rhoM ^ 2 * vv + 72
    * rhoM ^ 2 - 114 * rhoM * vv ^ 2 - 684 * rhoM * vv + 936 * rhoM - 324 * vv ^ 2 - 1944 * vv +
    1296) * X + C (-12 * rhoM ^ 2 * vv ^ 2 - 72 * rhoM ^ 2 * vv - 156 * rhoM * vv ^ 2 - 936 * rhoM
    * vv - 120 * vv ^ 2 - 1296 * vv)

noncomputable def VU80 : P :=
  C (8) * X ^ 5 + C (12 * rhoM + 168) * X ^ 4 + C (4 * rhoM ^ 2 + 208 * rhoM - 8 * vv ^ 2 - 8 * vv
    + 1336) * X ^ 3 + C (52 * rhoM ^ 2 - 12 * rhoM * vv ^ 2 - 12 * rhoM * vv + 1300 * rhoM - 80 *
    vv ^ 2 - 80 * vv + 5016) * X ^ 2 + C (-4 * rhoM ^ 2 * vv ^ 2 - 4 * rhoM ^ 2 * vv + 208 * rhoM
    ^ 2 - 76 * rhoM * vv ^ 2 - 76 * rhoM * vv + 3424 * rhoM - 216 * vv ^ 2 - 216 * vv + 8064) * X
    + C (-8 * rhoM ^ 2 * vv ^ 2 - 8 * rhoM ^ 2 * vv + 240 * rhoM ^ 2 - 104 * rhoM * vv ^ 2 - 104 *
    rhoM * vv + 3120 * rhoM - 240 * vv ^ 2 - 144 * vv + 4320)

noncomputable def ValU (s : St) : P :=
  if s = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ then VU0 else
  if s = ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ then VU1 else
  if s = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ then VU2 else
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ then VU3 else
  if s = ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ then VU4 else
  if s = ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ then VU5 else
  if s = ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ then VU6 else
  if s = ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ then VU7 else
  if s = ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ then VU8 else
  if s = ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ then VU9 else
  if s = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ then VU10 else
  if s = ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ then VU11 else
  if s = ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ then VU12 else
  if s = ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ then VU13 else
  if s = ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ then VU14 else
  if s = ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ then VU15 else
  if s = ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ then VU16 else
  if s = ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ then VU17 else
  if s = ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ then VU18 else
  if s = ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ then VU19 else
  if s = ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ then VU20 else
  if s = ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ then VU21 else
  if s = ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ then VU22 else
  if s = ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ then VU23 else
  if s = ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ then VU24 else
  if s = ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ then VU25 else
  if s = ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ then VU26 else
  if s = ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ then VU27 else
  if s = ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ then VU28 else
  if s = ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ then VU29 else
  if s = ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ then VU30 else
  if s = ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ then VU31 else
  if s = ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ then VU32 else
  if s = ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ then VU33 else
  if s = ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ then VU34 else
  if s = ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ then VU35 else
  if s = ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ then VU36 else
  if s = ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ then VU37 else
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ then VU38 else
  if s = ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ then VU39 else
  if s = ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ then VU40 else
  if s = ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ then VU41 else
  if s = ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ then VU42 else
  if s = ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ then VU43 else
  if s = ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ then VU44 else
  if s = ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ then VU45 else
  if s = ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ then VU46 else
  if s = ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ then VU47 else
  if s = ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ then VU48 else
  if s = ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ then VU49 else
  if s = ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ then VU50 else
  if s = ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ then VU51 else
  if s = ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ then VU52 else
  if s = ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ then VU53 else
  if s = ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ then VU54 else
  if s = ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ then VU55 else
  if s = ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ then VU56 else
  if s = ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ then VU57 else
  if s = ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ then VU58 else
  if s = ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ then VU59 else
  if s = ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ then VU60 else
  if s = ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ then VU61 else
  if s = ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ then VU62 else
  if s = ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ then VU63 else
  if s = ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ then VU64 else
  if s = ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ then VU65 else
  if s = ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ then VU66 else
  if s = ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ then VU67 else
  if s = ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ then VU68 else
  if s = ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ then VU69 else
  if s = ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ then VU70 else
  if s = ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ then VU71 else
  if s = ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ then VU72 else
  if s = ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ then VU73 else
  if s = ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ then VU74 else
  if s = ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ then VU75 else
  if s = ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ then VU76 else
  if s = ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ then VU77 else
  if s = ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ then VU78 else
  if s = ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ then VU79 else
  if s = ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ then VU80 else
  0

@[simp] theorem ValU_0 : ValU ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = VU0 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_1 : ValU ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = VU1 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_2 : ValU ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = VU2 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_3 : ValU ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = VU3 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_4 : ValU ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = VU4 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_5 : ValU ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = VU5 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_6 : ValU ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = VU6 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_7 : ValU ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = VU7 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_8 : ValU ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = VU8 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_9 : ValU ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = VU9 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_10 : ValU ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = VU10 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_11 : ValU ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = VU11 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_12 : ValU ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = VU12 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_13 : ValU ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = VU13 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_14 : ValU ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = VU14 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_15 : ValU ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = VU15 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_16 : ValU ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = VU16 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_17 : ValU ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = VU17 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_18 : ValU ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = VU18 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_19 : ValU ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = VU19 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_20 : ValU ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = VU20 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_21 : ValU ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = VU21 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_22 : ValU ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = VU22 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_23 : ValU ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = VU23 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_24 : ValU ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = VU24 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_25 : ValU ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = VU25 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_26 : ValU ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = VU26 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_27 : ValU ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = VU27 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_28 : ValU ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = VU28 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_29 : ValU ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = VU29 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_30 : ValU ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = VU30 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_31 : ValU ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = VU31 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_32 : ValU ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = VU32 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_33 : ValU ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = VU33 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_34 : ValU ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = VU34 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_35 : ValU ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = VU35 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_36 : ValU ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = VU36 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_37 : ValU ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = VU37 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_38 : ValU ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = VU38 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_39 : ValU ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = VU39 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_40 : ValU ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = VU40 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_41 : ValU ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = VU41 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_42 : ValU ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = VU42 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_43 : ValU ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = VU43 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_44 : ValU ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = VU44 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_45 : ValU ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = VU45 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_46 : ValU ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = VU46 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_47 : ValU ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ = VU47 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_48 : ValU ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ = VU48 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_49 : ValU ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ = VU49 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_50 : ValU ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ = VU50 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_51 : ValU ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ = VU51 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_52 : ValU ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ = VU52 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_53 : ValU ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ = VU53 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_54 : ValU ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ = VU54 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_55 : ValU ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ = VU55 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_56 : ValU ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ = VU56 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_57 : ValU ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ = VU57 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_58 : ValU ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ = VU58 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_59 : ValU ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ = VU59 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_60 : ValU ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = VU60 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_61 : ValU ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ = VU61 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_62 : ValU ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ = VU62 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_63 : ValU ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ = VU63 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_64 : ValU ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = VU64 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_65 : ValU ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = VU65 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_66 : ValU ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = VU66 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_67 : ValU ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = VU67 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_68 : ValU ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = VU68 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_69 : ValU ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ = VU69 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_70 : ValU ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ = VU70 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_71 : ValU ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = VU71 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_72 : ValU ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = VU72 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_73 : ValU ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = VU73 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_74 : ValU ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ = VU74 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_75 : ValU ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = VU75 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_76 : ValU ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = VU76 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_77 : ValU ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = VU77 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_78 : ValU ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = VU78 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_79 : ValU ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = VU79 := by
  simp only [ValU]
  norm_num

@[simp] theorem ValU_80 : ValU ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = VU80 := by
  simp only [ValU]
  norm_num

end Rhone.Algebra.KilledSystemULast
