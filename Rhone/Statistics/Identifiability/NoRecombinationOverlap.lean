/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.NoRecombination
public import Rhone.Statistics.Identifiability.CommonSubmeasureTesting

/-! # A no-recombination overlap lower bound -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ENNReal
open Finset Set MeasureTheory

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem matrix_pow_le_of_nonneg {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (n : ℕ) :
    ∀ i j, (A ^ n) i j ≤ (B ^ n) i j := by
  induction n with
  | zero => intro i j; exact le_rfl
  | succ n ih =>
    intro i j
    simp only [pow_succ', Matrix.mul_apply]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul (hAB i k) (ih k j)
      (Matrix.pow_apply_nonneg hA n k j) ((hA i k).trans (hAB i k)))

theorem matrix_exp_le_of_nonneg {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) :
    ∀ i j, NormedSpace.exp A i j ≤ NormedSpace.exp B i j := by
  intro i j
  exact hasSum_le (fun n => mul_le_mul_of_nonneg_left
    (matrix_pow_le_of_nonneg hA hAB n i j) (by positivity))
    (exp_entry_hasSum A i j) (exp_entry_hasSum B i j)

theorem matrix_exp_add_identity {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (b t : ℝ) :
    NormedSpace.exp (t • (Q + b • 1)) =
      Real.exp (t * b) • NormedSpace.exp (t • Q) := by
  have hsplit : t • (Q + b • 1) = (t * b) • 1 + t • Q := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((t * b) • (1 : Matrix (Fin d) (Fin d) ℝ)) (t • Q) :=
    (Commute.one_left _).smul_left _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_identity,
    Matrix.smul_mul, Matrix.one_mul]

theorem matrix_exp_mono_of_metzler {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsMetzler A) (hAB : ∀ i j, A i j ≤ B i j) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i j, NormedSpace.exp (t • A) i j ≤ NormedSpace.exp (t • B) i j := by
  let b : ℝ := ∑ i, |A i i|
  have hdiag : ∀ i, -A i i ≤ b := by
    intro i
    exact le_trans (neg_le_abs (A i i))
      (Finset.single_le_sum (fun j _ => abs_nonneg (A j j)) (Finset.mem_univ i))
  have hshift : ∀ i j, 0 ≤ (A + b • 1) i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [add_comm] using (neg_le_iff_add_nonneg.mp (hdiag i))
    · simpa [Matrix.one_apply, hij] using hA i j hij
  have horder : ∀ i j, (A + b • 1) i j ≤ (B + b • 1) i j := by
    intro i j
    dsimp only [Matrix.add_apply]
    linarith [hAB i j]
  have hexp := matrix_exp_le_of_nonneg
    (A := t • (A + b • 1)) (B := t • (B + b • 1))
    (fun i j => mul_nonneg ht (hshift i j))
    (fun i j => mul_le_mul_of_nonneg_left (horder i j) ht)
  rw [matrix_exp_add_identity, matrix_exp_add_identity] at hexp
  intro i j
  have hh := hexp i j
  simp only [Matrix.smul_apply, smul_eq_mul] at hh
  nlinarith [Real.exp_pos (t * b)]

theorem metzler_sub_identity {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : IsMetzler Q) (b : ℝ) : IsMetzler (Q - b • 1) := by
  intro i j hij
  simpa [Matrix.one_apply, hij] using hQ i j hij

theorem recombination_table_add_two_identity_nonneg : ∀ i j : MarkovChain.Identifiability.State,
    0 ≤ MarkovChain.Identifiability.recombinationTable i j + 2 *
        (1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℤ) i j := by
  intro i
  fin_cases i <;> decide

theorem killed_zero_generator_le (k : ℕ) (c q : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ i j, (MarkovChain.Identifiability.generator k c q 0 - (2 * r) • 1) i j ≤
        MarkovChain.Identifiability.generator k c q r i j := by
  intro i j
  have hR : 0 ≤ (MarkovChain.Identifiability.recombinationTable i j : ℝ) + 2 *
      (1 : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ) i j := by
    have hZ := recombination_table_add_two_identity_nonneg i j
    simp only [Matrix.one_apply] at hZ ⊢
    split_ifs at hZ ⊢ <;> exact_mod_cast hZ
  have hp := mul_nonneg hr hR
  simp only [MarkovChain.Identifiability.generator, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul,
    zero_mul, add_zero]
  nlinarith

theorem no_recombination_transition_lower (k : ℕ) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ∀ i j, Real.exp (-(2 * r * t)) * NormedSpace.exp
        (t • MarkovChain.Identifiability.generator k c q 0) i j ≤
      NormedSpace.exp (t • MarkovChain.Identifiability.generator k c q r) i j := by
  have h := matrix_exp_mono_of_metzler
    (metzler_sub_identity (generator_metzler k hc hq (le_refl 0)) (2 * r))
    (killed_zero_generator_le k c q hr) ht
  have heq : MarkovChain.Identifiability.generator k c q 0 - (2 * r) • 1 =
      MarkovChain.Identifiability.generator k c q 0 + (-(2 * r)) • 1 := by
    simp [sub_eq_add_neg]
  rw [heq, matrix_exp_add_identity] at h
  have ht' : t * -(2 * r) = -(2 * r * t) := by ring
  simpa only [Matrix.smul_apply, smul_eq_mul, ht'] using h

theorem no_recombination_flow_lower (k : ℕ) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (v : MarkovChain.Identifiability.State → ℝ) (hv : ∀ i, 0 ≤ v i)
        (i : MarkovChain.Identifiability.State) :
    Real.exp (-(2 * r * t)) * flowOutput (MarkovChain.Identifiability.generator k c q 0) i v 0 t ≤
      flowOutput (MarkovChain.Identifiability.generator k c q r) i v 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (no_recombination_transition_lower k hc hq hr ht i j) (hv j)

theorem no_recombination_diagonal_flux_lower (k : ℕ) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Real.exp (-(2 * r * t)) * densityJet k c q 0 t ≤ markFlux k c q r 0 t := by
  have h := no_recombination_flow_lower k hc hq hr ht
    (fun i => markRates c i 0) (fun i => markRates_nonneg hc i 0) 0
  change Real.exp (-(2 * r * t)) * markFlux k c q 0 0 t ≤ markFlux k c q r 0 t at h
  simpa [no_recombination_markFlux] using h

noncomputable def noRecombinationTimeLaw (k : ℕ) (c q r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (Real.exp (-(2 * r * t)) * densityJet k c q 0 t))

noncomputable def noRecombinationOverlap (k : ℕ) (c q r : ℝ) : Measure (ℝ × ℝ) :=
  (noRecombinationTimeLaw k c q r).map (fun t => (t, t))

theorem noRecombinationTimeLaw_le_markLaw (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    noRecombinationTimeLaw k c q r ≤ markLaw k c q r 0 := by
  unfold noRecombinationTimeLaw markLaw
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact ENNReal.ofReal_le_ofReal (no_recombination_diagonal_flux_lower k hc hq hr ht.le)

theorem zero_mark_component_eq_diagonal (k : ℕ) (c q r : ℝ) :
    ((markLaw k c q r 0).prod (lagLaw k c q 0)).map (recoverTimes 0) =
      (markLaw k c q r 0).map (fun t => (t, t)) := by
  have : SFinite (markLaw k c q r 0) := by
    unfold markLaw
    infer_instance
  rw [lagLaw, ite_eq_left rfl, Measure.prod_dirac,
    Measure.map_map (f := fun x : ℝ => (x, 0)) (g := recoverTimes 0)
      (recoverTimes_continuous 0).measurable
      (measurable_id.prodMk measurable_const)]
  rfl

theorem noRecombinationOverlap_le_jointLaw (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    noRecombinationOverlap k c q r ≤ jointLaw k c q r := by
  calc
    noRecombinationOverlap k c q r ≤
        (markLaw k c q r 0).map (fun t => (t, t)) :=
      Measure.map_mono (noRecombinationTimeLaw_le_markLaw k hc hq hr)
        (measurable_id.prodMk measurable_id)
    _ = ((markLaw k c q r 0).prod (lagLaw k c q 0)).map (recoverTimes 0) :=
      (zero_mark_component_eq_diagonal k c q r).symm
    _ ≤ jointLaw k c q r := by
      unfold jointLaw
      exact Measure.le_sum
        (fun m => ((markLaw k c q r m).prod (lagLaw k c q m)).map (recoverTimes m)) 0

theorem noRecombinationTimeLaw_le_pairLaw (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    noRecombinationTimeLaw k c q r ≤ firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
        0 := by
  unfold noRecombinationTimeLaw firstExitLaw
  rw [pair_exitRate]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply ENNReal.ofReal_le_ofReal
  change Real.exp (-(2 * r * t)) * densityJet k c q 0 t ≤ densityJet k c q 0 t
  have hf : 0 ≤ densityJet k c q 0 t := by
    simpa [no_recombination_markFlux] using
      markFlux_nonneg k hc hq (le_refl 0) ht.le 0
  have he : Real.exp (-(2 * r * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) hr) ht.le)
  nlinarith

theorem noRecombinationOverlap_le_zero_jointLaw (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    noRecombinationOverlap k c q r ≤ jointLaw k c q 0 := by
  rw [no_recombination_joint_diagonal]
  exact Measure.map_mono (noRecombinationTimeLaw_le_pairLaw k hc hq hr)
    (measurable_id.prodMk measurable_id)

theorem noRecombinationOverlap_le_diagonalPanLaw (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    noRecombinationOverlap k c q r ≤ diagonalPanLaw (pairHazard k c q) := by
  rw [← zero_recombination_law_identity k c hq]
  exact noRecombinationOverlap_le_zero_jointLaw k hc hq hr

theorem noRecombinationOverlap_isFinite (k : ℕ) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    IsFiniteMeasure (noRecombinationOverlap k c q r) := by
  have := jointLaw_probability k hc hq hr
  exact isFiniteMeasure_of_le _ (noRecombinationOverlap_le_jointLaw k hc.le hq.le hr)

theorem noRecombinationOverlap_mass (k : ℕ) (c q r : ℝ) :
    noRecombinationOverlap k c q r univ =
      ∫⁻ t in Ioi 0, ENNReal.ofReal
        (Real.exp (-(2 * r * t)) * densityJet k c q 0 t) := by
  rw [noRecombinationOverlap, Measure.map_apply (f := fun t : ℝ => (t, t))
    (measurable_id.prodMk measurable_id)
    MeasurableSet.univ, preimage_univ, noRecombinationTimeLaw,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]

theorem island_iid_power_le_overlap (k : ℕ) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) (N : ℕ)
    {A : Set (Fin N → ℝ × ℝ)} (hA : MeasurableSet A) {α : ℝ}
    (hlevel : (Measure.pi (fun _ : Fin N =>
      diagonalPanLaw (pairHazard k c q))).real A ≤ α) :
    (Measure.pi (fun _ : Fin N => jointLaw k c q r)).real A ≤
      α + 1 - ((noRecombinationOverlap k c q r).real univ) ^ N := by
  have := jointLaw_probability k hc hq hr
  have := noRecombinationOverlap_isFinite k hc hq hr
  have hprob : IsProbabilityMeasure (diagonalPanLaw (pairHazard k c q)) := by
    rw [← zero_recombination_law_identity k c hq.le]
    exact jointLaw_probability k hc hq (le_refl 0)
  have := hprob
  exact iid_power_le_of_common_submeasure
    (noRecombinationOverlap_le_jointLaw k hc.le hq.le hr)
    (noRecombinationOverlap_le_diagonalPanLaw k hc.le hq.le hr) N hA hlevel

theorem island_iid_overlap_necessary (k : ℕ) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) (N : ℕ)
    {A : Set (Fin N → ℝ × ℝ)} (hA : MeasurableSet A) {α β : ℝ}
    (hlevel : (Measure.pi (fun _ : Fin N =>
      diagonalPanLaw (pairHazard k c q))).real A ≤ α)
    (hpower : 1 - β ≤ (Measure.pi (fun _ : Fin N => jointLaw k c q r)).real A) :
    ((noRecombinationOverlap k c q r).real univ) ^ N ≤ α + β := by
  have h := island_iid_power_le_overlap k hc hq hr N hA hlevel
  linarith

end Rhone.Statistics.Identifiability
