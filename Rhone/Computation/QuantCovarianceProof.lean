/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.QuantCovariance
public import Rhone.Statistics.Relatives
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable single-locus quantitative genetics equals the specification

Source: kempthorne1954, pp. 106–107, 112; felsenstein_teg2019, sec. IX.5, eq. (IX-51)–(IX-55), pp.
428–429. -/
set_option linter.style.longLine false

@[expose] public section
namespace Rhone.Computation.QuantCovariance
open Statistics

def toReal (G : Values) : Fin 3 → ℝ := ![(G.g0 : ℝ), (G.g1 : ℝ), (G.g2 : ℝ)]

theorem validFreq_iff (p : Rat) : validFreq p = true ↔ 0 ≤ p ∧ p ≤ 1 := by
  simp [validFreq]

theorem hwExp_cast (p f0 f1 f2 : Rat) :
    ((hwExp p f0 f1 f2 : Rat) : ℝ) =
      Rhone.Statistics.hwExp (p : ℝ) ![(f0 : ℝ), (f1 : ℝ), (f2 : ℝ)] := by
  simp only [hwExp, Rhone.Statistics.hwExp]
  push_cast
  simp

theorem genoMean_cast (p : Rat) (G : Values) :
    ((genoMean p G : Rat) : ℝ) = Rhone.Statistics.genoMean (p : ℝ) (toReal G) := by
  simp [genoMean, hwExp_cast, Rhone.Statistics.genoMean, toReal]

theorem avgEffect_cast (p : Rat) (G : Values) :
    ((avgEffect p G : Rat) : ℝ) = Rhone.Statistics.avgEffect (p : ℝ) (toReal G) := by
  simp [avgEffect, Rhone.Statistics.avgEffect, Rhone.Statistics.addParam, Rhone.Statistics.domParam,
      toReal]

theorem breedingValue_cast (p : Rat) (G : Values) (k : Fin 3) :
    ((breedingValue p G k.val : Rat) : ℝ) = Rhone.Statistics.breedingValue (p : ℝ) (toReal G) k :=
        by
  fin_cases k
  all_goals simp [breedingValue, avgEffect_cast, Rhone.Statistics.breedingValue, Rhone.Statistics.count]

theorem domDev_cast (p : Rat) (G : Values) (k : Fin 3) :
    ((domDev p G k.val : Rat) : ℝ) = Rhone.Statistics.domDev (p : ℝ) (toReal G) k := by
  have h0 := breedingValue_cast p G 0
  have h1 := breedingValue_cast p G 1
  have h2 := breedingValue_cast p G 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  fin_cases k <;>
    simp [domDev, Values.get, genoMean_cast, Rhone.Statistics.domDev, toReal, h0, h1, h2]

theorem varARaw_cast (p : Rat) (G : Values) :
    ((varARaw p G : Rat) : ℝ) = Rhone.Statistics.varA (p : ℝ) (toReal G) := by
  have h0 := breedingValue_cast p G 0
  have h1 := breedingValue_cast p G 1
  have h2 := breedingValue_cast p G 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  rw [varARaw, hwExp_cast]
  simp only [Rhone.Statistics.varA, Rhone.Statistics.hwExp]
  push_cast
  simp [h0, h1, h2]

theorem varDRaw_cast (p : Rat) (G : Values) :
    ((varDRaw p G : Rat) : ℝ) = Rhone.Statistics.varD (p : ℝ) (toReal G) := by
  have h0 := domDev_cast p G 0
  have h1 := domDev_cast p G 1
  have h2 := domDev_cast p G 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  rw [varDRaw, hwExp_cast]
  simp only [Rhone.Statistics.varD, Rhone.Statistics.hwExp]
  push_cast
  simp [h0, h1, h2]

theorem sharedAlleleProduct_cast (p : Rat) (G : Values) :
    ((sharedAlleleProduct p G : Rat) : ℝ) =
      Rhone.Statistics.sharedAlleleProduct (p : ℝ) (toReal G) (toReal G) := by
  simp [sharedAlleleProduct, Rhone.Statistics.sharedAlleleProduct, toReal]

theorem eq_none_iff (p : Rat) (G : Values) :
    (varA p G = none ↔ p < 0 ∨ 1 < p) ∧ (varD p G = none ↔ p < 0 ∨ 1 < p) ∧
    (parentOffspringCov p G = none ↔ p < 0 ∨ 1 < p) ∧
    (halfSibCov p G = none ↔ p < 0 ∨ 1 < p) ∧
    (fullSibCov p G = none ↔ p < 0 ∨ 1 < p) := by
  by_cases h : 0 ≤ p ∧ p ≤ 1
  · have hv : validFreq p = true := (validFreq_iff p).2 h
    have hn : ¬ (p < 0 ∨ 1 < p) := by
      rintro (h1 | h1) <;> [exact absurd h.1 (not_le.2 h1); exact absurd h.2 (not_le.2 h1)]
    simp [varA, varD, parentOffspringCov, halfSibCov, fullSibCov, hv, hn]
  · have hv : validFreq p = false := by
      rw [Bool.eq_false_iff]
      intro hh
      exact h ((validFreq_iff p).1 hh)
    have hn : p < 0 ∨ 1 < p := by
      by_contra hc
      exact h ⟨not_lt.1 (fun h' => hc (Or.inl h')), not_lt.1 (fun h' => hc (Or.inr h'))⟩
    simp [varA, varD, parentOffspringCov, halfSibCov, fullSibCov, hv, hn]

theorem varA_eq (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ q : Rat, varA p G = some q ∧ (q : ℝ) = Rhone.Statistics.varA (p : ℝ) (toReal G) :=
  ⟨varARaw p G, by simp [varA, (validFreq_iff p).2 ⟨h0, h1⟩], varARaw_cast p G⟩

theorem varD_eq (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ q : Rat, varD p G = some q ∧ (q : ℝ) = Rhone.Statistics.varD (p : ℝ) (toReal G) :=
  ⟨varDRaw p G, by simp [varD, (validFreq_iff p).2 ⟨h0, h1⟩], varDRaw_cast p G⟩

theorem parentOffspringCov_eq (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ q : Rat, parentOffspringCov p G = some q ∧
      (q : ℝ) = Rhone.Statistics.parentOffspringCov (p : ℝ) (toReal G) := by
  refine ⟨sharedAlleleProduct p G - genoMean p G * genoMean p G,
    by simp [parentOffspringCov, (validFreq_iff p).2 ⟨h0, h1⟩], ?_⟩
  simp [sharedAlleleProduct_cast, genoMean_cast, Rhone.Statistics.parentOffspringCov,
    Rhone.Statistics.sharedAlleleCov]

theorem halfSibCov_eq (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ q : Rat, halfSibCov p G = some q ∧
      (q : ℝ) = Rhone.Statistics.halfSibCov (p : ℝ) (toReal G) := by
  refine ⟨(genoMean p G ^ 2 + sharedAlleleProduct p G) / 2 - genoMean p G ^ 2,
    by simp [halfSibCov, (validFreq_iff p).2 ⟨h0, h1⟩], ?_⟩
  simp [sharedAlleleProduct_cast, genoMean_cast, Rhone.Statistics.halfSibCov]

theorem fullSibCov_eq (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ q : Rat, fullSibCov p G = some q ∧
      (q : ℝ) = Rhone.Statistics.fullSibCov (p : ℝ) (toReal G) := by
  refine ⟨(genoMean p G ^ 2 + 2 * sharedAlleleProduct p G +
    hwExp p (G.g0 ^ 2) (G.g1 ^ 2) (G.g2 ^ 2)) / 4 - genoMean p G ^ 2,
    by simp [fullSibCov, (validFreq_iff p).2 ⟨h0, h1⟩], ?_⟩
  have hw := hwExp_cast p (G.g0 ^ 2) (G.g1 ^ 2) (G.g2 ^ 2)
  simp only [Rhone.Statistics.fullSibCov, Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
    Rat.cast_pow, genoMean_cast, sharedAlleleProduct_cast, hw]
  simp [toReal, Rhone.Statistics.hwExp]

theorem covariance_relations (p : Rat) (G : Values) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ a d po hs fs : Rat, varA p G = some a ∧ varD p G = some d ∧
      parentOffspringCov p G = some po ∧ halfSibCov p G = some hs ∧
      fullSibCov p G = some fs ∧ po = a / 2 ∧ hs = a / 4 ∧ fs = a / 2 + d / 4 := by
  obtain ⟨a, ha, hae⟩ := varA_eq p G h0 h1
  obtain ⟨d, hd, hde⟩ := varD_eq p G h0 h1
  obtain ⟨po, hpo, hpoe⟩ := parentOffspringCov_eq p G h0 h1
  obtain ⟨hs, hhs, hhse⟩ := halfSibCov_eq p G h0 h1
  obtain ⟨fs, hfs, hfse⟩ := fullSibCov_eq p G h0 h1
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h0
  have hp1 : (p : ℝ) ≤ 1 := by exact_mod_cast h1
  refine ⟨a, d, po, hs, fs, ha, hd, hpo, hhs, hfs, ?_, ?_, ?_⟩
  · have : (po : ℝ) = (a / 2 : Rat) := by
      rw [hpoe, parent_offspring_covariance _ _ hp0 hp1, ← hae]; push_cast; ring
    exact_mod_cast this
  · have : (hs : ℝ) = (a / 4 : Rat) := by
      rw [hhse, half_sib_covariance _ _ hp0 hp1, ← hae]; push_cast; ring
    exact_mod_cast this
  · have : (fs : ℝ) = (a / 2 + d / 4 : Rat) := by
      rw [hfse, full_sib_covariance _ _ hp0 hp1, ← hae, ← hde]; push_cast; ring
    exact_mod_cast this

end Rhone.Computation.QuantCovariance
