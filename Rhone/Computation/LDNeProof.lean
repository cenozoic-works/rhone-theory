/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.LDNe
public import Rhone.Computation.OhtaKimuraProof
public import Rhone.Statistics.LDNe
public import Mathlib.Basic.Real.Basic

/-!
# Executable LD-based effective size pieces equal the specification

Source: hill1981, eq. (1)–(3), pp. 210–211. -/

@[expose] public section
namespace Rhone.Computation.LDNe
open scoped Matrix

def toVec (v : Mom) : Fin 3 → ℝ := ![(v.h : ℝ), (v.z : ℝ), (v.d : ℝ)]

theorem toVec_injective {u v : Mom} (h : toVec u = toVec v) : u = v := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [toVec] at h0 h1 h2
  cases u
  cases v
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Rat.cast_inj] at h0 h1 h2
  simp [h0, h1, h2]

theorem samplingMoment_eq (S : ℕ) (v : Mom) :
    toVec (samplingMoment (S : Rat) v) =
      Rhone.MarkovChain.WFAllocationLD.samplingMomentMatrix S *ᵥ toVec v := by
  ext i
  fin_cases i <;>
    simp [toVec, samplingMoment, Rhone.MarkovChain.WFAllocationLD.samplingMomentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem samplingCorrection_eq (S : ℕ) (v : Mom) :
    toVec (samplingCorrection (S : Rat) v) =
      Rhone.Statistics.LDNe.samplingCorrection S *ᵥ toVec v := by
  ext i
  fin_cases i <;>
    simp [toVec, samplingCorrection, Rhone.Statistics.LDNe.samplingCorrection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem samplingCorrection_samplingMoment (S : ℕ) (hS : 4 ≤ S) (v : Mom) :
    samplingCorrection (S : Rat) (samplingMoment (S : Rat) v) = v := by
  apply toVec_injective
  rw [samplingCorrection_eq, samplingMoment_eq, Matrix.mulVec_mulVec,
    Rhone.Statistics.LDNe.samplingCorrection_mul S hS, Matrix.one_mulVec]

theorem correctedRatio_eq (S : ℕ) (v : Mom) :
    ((correctedRatio (S : Rat) v : Rat) : ℝ) =
      (Rhone.Statistics.LDNe.samplingCorrection S *ᵥ toVec v) 2 /
        (Rhone.Statistics.LDNe.samplingCorrection S *ᵥ toVec v) 0 := by
  rw [← samplingCorrection_eq, correctedRatio, Rat.cast_div]
  rfl

theorem corrected_sampled_ratio_eq (M S : ℕ) (hM : 3 ≤ M) (hS : 4 ≤ S) (c u : Rat)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * Rhone.MarkovChain.WFAllocationLD.forcedCountKernel M (c : ℝ) (u : ℝ) a
        b
      = π b) :
    (Rhone.Statistics.LDNe.samplingCorrection S *ᵥ Rhone.Statistics.LDNe.sampledMoments M S π) 2 /
        (Rhone.Statistics.LDNe.samplingCorrection S *ᵥ Rhone.Statistics.LDNe.sampledMoments M S π)
            0 =
      ((OhtaKimura.ldSigma (M : Rat) c u : Rat) : ℝ) := by
  rw [OhtaKimura.ldSigma_eq]
  have := Rhone.Statistics.LDNe.corrected_sampled_ratio M S hM hS (c : ℝ) (u : ℝ)
    (by exact_mod_cast hc0) (by exact_mod_cast hc1) (by exact_mod_cast hu0)
    (by have h := (Rat.cast_lt (K := ℝ)).2 hu1; simpa using h) π hπ hnorm hstat
  simpa using this

theorem ldNe_ldSigmaLimit (N : ℕ) (c : Rat) (hc : 0 < c) :
    Rhone.Statistics.LDNe.ldNe (c : ℝ) ((OhtaKimura.ldSigmaLimit (2 * (N : Rat) * c) : Rat) : ℝ) =
        N := by
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have := Rhone.Statistics.LDNe.ldNe_limit_value (N := N) hc'
  rw [OhtaKimura.ldSigmaLimit_eq]
  simpa using this

end Rhone.Computation.LDNe
