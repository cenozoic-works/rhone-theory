/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GenotypicValue
public import Mathlib.Basic.Real.Basic

/-!
# Single-locus genotypic covariance between relatives

Source: kempthorne1954, p. 112. -/

@[expose] public section
namespace Rhone.Statistics

/--
Source: kempthorne1954, pp. 111–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def sharedAlleleProduct (p : ℝ) (G H : Fin 3 → ℝ) : ℝ :=
  (1-p) * ((1-p)*G 0+p*G 1) * ((1-p)*H 0+p*H 1) +
  p * ((1-p)*G 1+p*G 2) * ((1-p)*H 1+p*H 2)

/--
Source: kempthorne1954, pp. 111–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def sharedAlleleCov (p : ℝ) (G H : Fin 3 → ℝ) : ℝ :=
  sharedAlleleProduct p G H - genoMean p G * genoMean p H

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-53), p. 429. -/
noncomputable def parentOffspringCov (p : ℝ) (G : Fin 3 → ℝ) : ℝ :=
  sharedAlleleCov p G G

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-54), p. 429. -/
noncomputable def halfSibCov (p : ℝ) (G : Fin 3 → ℝ) : ℝ :=
  ((genoMean p G)^2 + sharedAlleleProduct p G G)/2 - (genoMean p G)^2

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-55), p. 429. -/
noncomputable def fullSibCov (p : ℝ) (G : Fin 3 → ℝ) : ℝ :=
  ((genoMean p G)^2 + 2*sharedAlleleProduct p G G +
    hwExp p (fun k => (G k)^2))/4 - (genoMean p G)^2

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
private theorem shared_cov_polynomial (p : ℝ) (G : Fin 3 → ℝ) :
    sharedAlleleCov p G G = varA p G / 2 := by
  rw [varA_eq]
  simp only [sharedAlleleCov, sharedAlleleProduct, genoMean, hwExp,
    avgEffect, addParam, domParam]
  ring

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-53), p. 429. -/
theorem parent_offspring_covariance
    (p : ℝ) (G : Fin 3 → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    parentOffspringCov p G = varA p G / 2 := by
  have _hp := And.intro hp0 hp1
  exact shared_cov_polynomial p G

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-54), p. 429. -/
theorem half_sib_covariance
    (p : ℝ) (G : Fin 3 → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    halfSibCov p G = varA p G / 4 := by
  have _hp := And.intro hp0 hp1
  have h := shared_cov_polynomial p G
  unfold sharedAlleleCov at h
  unfold halfSibCov
  nlinarith

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-55), p. 429. -/
theorem full_sib_covariance
    (p : ℝ) (G : Fin 3 → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fullSibCov p G = varA p G / 2 + varD p G / 4 := by
  have _hp := And.intro hp0 hp1
  rw [varA_eq, varD_eq]
  simp only [fullSibCov, sharedAlleleProduct, genoMean, hwExp,
    avgEffect, addParam, domParam]
  ring

end Rhone.Statistics
