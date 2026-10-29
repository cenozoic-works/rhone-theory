/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Combinatorics.Pedigree
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform

/-!
# An additive trait with many unlinked loci on a pedigree

Source: barton_etheridge_veber2017, sec. 3. -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory Rhone.Combinatorics

variable {n : ℕ}

/-- Source: barton_etheridge_veber2017, sec. 3. -/
def geneFounder (P : Pedigree n) (c : Fin n → Bool) (i : Fin n) : Fin n :=
  match _h : P.parents i with
  | none => i
  | some p => geneFounder P c (if c i then p.1 else p.2)
termination_by i.val
decreasing_by
  have hlt := P.parents_lt i p (by assumption)
  split
  · exact hlt.1
  · exact hlt.2

theorem geneFounder_of_founder (P : Pedigree n) (c : Fin n → Bool) {i : Fin n}
    (h : P.parents i = none) : geneFounder P c i = i := by
  rw [geneFounder]
  split
  · rfl
  · simp_all

theorem parents_geneFounder (P : Pedigree n) (c : Fin n → Bool) (i : Fin n) :
    P.parents (geneFounder P c i) = none := by
  fun_induction geneFounder P c i with
  | case1 i h => exact h
  | case2 i p h ih => exact ih

/-- Source: barton_etheridge_veber2017, sec. 3. -/
noncomputable def identityByDescent (P : Pedigree n) (a b : Fin n) : ℝ :=
  ((Finset.univ.filter fun c : Fin n → Bool => geneFounder P c a = geneFounder P c b).card : ℝ)
    / 2 ^ n

theorem identityByDescent_self (P : Pedigree n) (a : Fin n) : identityByDescent P a a = 1 := by
  simp [identityByDescent]

theorem identityByDescent_of_founders (P : Pedigree n) {a b : Fin n}
    (ha : P.parents a = none) (hb : P.parents b = none) (hab : a ≠ b) :
    identityByDescent P a b = 0 := by
  simp [identityByDescent, geneFounder_of_founder P _ ha, geneFounder_of_founder P _ hb, hab]

theorem identityByDescent_nonneg (P : Pedigree n) (a b : Fin n) :
    0 ≤ identityByDescent P a b := by
  unfold identityByDescent
  positivity

theorem identityByDescent_le_one (P : Pedigree n) (a b : Fin n) :
    identityByDescent P a b ≤ 1 := by
  unfold identityByDescent
  rw [div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n → Bool))
    (fun c => geneFounder P c a = geneFounder P c b)
  have h2 : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
  rw [← h2]
  exact_mod_cast h

/-- Source: barton_etheridge_veber2017, sec. 3. -/
noncomputable def locusLaw (n : ℕ) (ν : Measure ℝ) : Measure ((Fin n → ℝ) × (Fin n → Bool)) :=
  (Measure.pi fun _ => ν).prod (Measure.pi fun _ => (PMF.uniformOfFintype Bool).toMeasure)

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (locusLaw n ν) := by
  unfold locusLaw
  infer_instance

/-- Source: barton_etheridge_veber2017, sec. 3. -/
noncomputable def genomeLaw (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (M : ℕ) :
    Measure (Fin M → (Fin n → ℝ) × (Fin n → Bool)) :=
  Measure.pi fun _ => locusLaw n ν

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] (M : ℕ) :
    IsProbabilityMeasure (genomeLaw n ν M) := by
  unfold genomeLaw
  infer_instance

/-- Source: barton_etheridge_veber2017, sec. 3. -/
noncomputable def traitDeviation (P : Pedigree n) (m : ℝ) (M : ℕ)
    (ω : Fin M → (Fin n → ℝ) × (Fin n → Bool)) (i : Fin n) : ℝ :=
  (√(M : ℝ))⁻¹ * ∑ l, ((ω l).1 (geneFounder P (ω l).2 i) - m)

/-- Source: barton_etheridge_veber2017, sec. 1. -/
noncomputable def segregationResidual (P : Pedigree n) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  match P.parents i with
  | none => z i
  | some p => z i - (z p.1 + z p.2) / 2

/-- Source: barton_etheridge_veber2017, sec. 1. -/
noncomputable def segregationVariance (P : Pedigree n) (v : ℝ) (i : Fin n) : ℝ :=
  match P.parents i with
  | none => v
  | some p => v / 2 * (1 - identityByDescent P p.1 p.2)

theorem segregationVariance_nonneg (P : Pedigree n) {v : ℝ} (hv : 0 ≤ v) (i : Fin n) :
    0 ≤ segregationVariance P v i := by
  unfold segregationVariance
  split
  · exact hv
  · rename_i p _
    have h := identityByDescent_le_one P p.1 p.2
    exact mul_nonneg (by linarith) (by linarith)

end Rhone.Statistics
