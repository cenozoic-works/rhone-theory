/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranAbsorptionTrajectory
public import Rhone.MarkovChain.FixationTrajectory
public import Rhone.MarkovChain.Shift

/-!
# Fixation-weighted selected Moran occupation times

Source: ewens2004, sec. 3.4. -/

@[expose] public section
namespace Rhone.MarkovChain
open Finset MoranSelectionSupport MeasureTheory

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranFixationWeightedTime (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (N - 1),
    moranSelectionGreen N r i j * moranFixProb N r j

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranConditionalFixationTime (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (N - 1),
    moranSelectionGreen N r i j * moranFixProb N r j) /
      moranFixProb N r i

/-- Source: ewens2004, sec. 3.4. -/
theorem moranFixationWeightedTime_poisson (N : ℕ) {r : ℝ} (hr : 0 < r) (i : Fin (N + 1)) :
    (moran N r).expect (fun j => moranFixationWeightedTime N r j) i =
      moranFixationWeightedTime N r i -
        (if 0 < (i : ℕ) ∧ (i : ℕ) < N then moranFixProb N r i.val else 0) := by
  rw [moran_expect (moranFixationWeightedTime N r) i]
  by_cases hi0 : (i : ℕ) = 0
  · simp [hi0, moranUp_zero, moranDown_zero]
  by_cases hiN : (i : ℕ) = N
  · simp [hiN, moranUp_self, moranDown_self]
  have hi : 0 < (i : ℕ) ∧ (i : ℕ) < N := by have := i.2; omega
  have hm : (i : ℕ) ∈ Icc 1 (N - 1) := by simp only [mem_Icc]; omega
  have hsum :
      moranUp N r i * (moranFixationWeightedTime N r (i + 1) - moranFixationWeightedTime N r i) +
      moranDown N r i * (moranFixationWeightedTime N r (i - 1) -
        moranFixationWeightedTime N r i) = -moranFixProb N r i.val := by
    unfold moranFixationWeightedTime
    calc
      _ = ∑ j ∈ Icc 1 (N - 1),
          (moranUp N r i * (moranSelectionGreen N r (i + 1) j * moranFixProb N r j -
            moranSelectionGreen N r i j * moranFixProb N r j) +
          moranDown N r i * (moranSelectionGreen N r (i - 1) j * moranFixProb N r j -
            moranSelectionGreen N r i j * moranFixProb N r j)) := by
        simp only [mul_sub, mul_sum, sum_add_distrib, sum_sub_distrib]
      _ = ∑ j ∈ Icc 1 (N - 1), (if j = (i : ℕ) then (-1 : ℝ) else 0) * moranFixProb N r j := by
        apply sum_congr rfl
        intro j hj
        simp only [mem_Icc] at hj
        have hp := green_poisson hr hi.1 hi.2 (by omega : 0 < j) (by omega : j < N)
        rw [← hp]
        ring
      _ = -moranFixProb N r i.val := by simp [hm]
  rw [ite_eq_left hi]
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moranFixationWeightedTime_eq_potential (N : ℕ) {r : ℝ} (hr : 0 < r)
    (i : Fin (N + 1)) :
    moranFixationWeightedTime N r i.val =
      (moranChain N r hr).potential (fixationBoundary N)
        (fun j => moranFixProb N r j.val) i := by
  have he : (fun i : Fin (N + 1) => moranFixationWeightedTime N r i.val) =
      (moranChain N r hr).potential (fixationBoundary N)
        (fun j => moranFixProb N r j.val) := by
    apply FinChain.eq_potential_of_step (moranChain_isAbsorbingSet N hr)
      (moranChain_reaches N hr)
    · intro a ha
      rcases mem_fixationBoundary.mp ha with rfl | rfl
      · simp [moranFixationWeightedTime, moranSelectionGreen, moranFixProb_zero]
      · unfold moranFixationWeightedTime
        apply sum_eq_zero
        intro j hj
        have hjN : j ≤ N := by simp only [mem_Icc] at hj; omega
        simp [moranSelectionGreen, max_eq_left hjN]
    · intro j hj
      have hint := pos_and_lt_of_notMem_fixationBoundary hj
      have hp := moranFixationWeightedTime_poisson N hr j
      rw [ite_eq_left hint] at hp
      change (∑ k, moran N r j k * moranFixationWeightedTime N r k) =
        moranFixationWeightedTime N r j - moranFixProb N r j at hp
      change moranFixationWeightedTime N r j =
        moranFixProb N r j + ∑ k, moran N r j k * moranFixationWeightedTime N r k
      linarith
  exact congrFun he i

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_fixation_joint_state {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (i j : Fin (N + 1)) (n : ℕ) :
    ((moranChain N r hr).pathLaw i).real
      {ω | ω n = j ∧ ∃ t, ω t = Fin.last N} =
      (moranChain N r hr).stepN n i j * moranFixProb N r j.val := by
  classical
  let C := moranChain N r hr
  let B : Set (ℕ → Fin (N + 1)) :=
    {ω | ω 0 = j ∧ ∃ t, ω t = Fin.last N}
  have hB : MeasurableSet B := by
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
    · have hs : ({ω : ℕ → Fin (N + 1) | ∃ t, ω t = Fin.last N} : Set _) =
          (⋃ t : ℕ, {ω : ℕ → Fin (N + 1) | ω t = Fin.last N} : Set _) := by
        ext ω
        simp
      change MeasurableSet ({ω : ℕ → Fin (N + 1) | ∃ t, ω t = Fin.last N} : Set _)
      rw [hs]
      exact MeasurableSet.iUnion fun t =>
        measurableSet_eq_fun (measurable_pi_apply t) measurable_const
  have hrow (y : Fin (N + 1)) : (C.pathLaw y).real B =
      if y = j then moranFixProb N r j.val else 0 := by
    have hinit : ∀ᵐ ω ∂C.pathLaw y, ω 0 = y := by
      have hz : C.pathLaw y {ω | ω 0 ≠ y} = 0 := by
        have he := C.map_eval_singleton 0 y y
        rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton y)] at he
        have hm : MeasurableSet {ω : ℕ → Fin (N + 1) | ω 0 = y} :=
          measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
        have hone : C.pathLaw y {ω | ω 0 = y} = 1 := by
          convert he using 1
          · congr 1
          · simp [FinChain.stepN_zero]
        exact (prob_compl_eq_zero_iff hm).2 hone
      exact ae_iff.2 hz
    by_cases hy : y = j
    · subst y
      rw [ite_eq_left rfl, ← moran_fixation_real hN hr j]
      apply measureReal_congr
      filter_upwards [hinit] with ω hω
      simp [B, hω]
    · rw [ite_eq_right hy]
      have he : B =ᵐ[C.pathLaw y] (∅ : Set (ℕ → Fin (N + 1))) := by
        filter_upwards [hinit] with ω hω
        simp [B, hω, hy]
      rw [measureReal_congr he, measureReal_empty]
  have hevent : {ω : ℕ → Fin (N + 1) | ω n = j ∧ ∃ t, ω t = Fin.last N} =ᵐ[C.pathLaw i]
      {ω | (fun k => ω (n + k)) ∈ B} := by
    filter_upwards [FinChain.ae_stays (moranChain_isAbsorbing_last N hr) i] with ω hω
    have hlater {a b : ℕ} (hab : a ≤ b) (ha : ω a = Fin.last N) :
        ω b = Fin.last N := by
      induction b, hab using Nat.le_induction with
      | base => exact ha
      | succ k _ ih => exact hω k ih
    simp only [B, Set.mem_ofPred_eq, Nat.add_zero]
    apply propext
    constructor
    · rintro ⟨hj, t, ht⟩
      exact ⟨hj, t, hlater (by omega) ht⟩
    · rintro ⟨hj, t, ht⟩
      exact ⟨hj, n + t, ht⟩
  rw [measureReal_congr hevent, C.pathLaw_real_shift i n hB]
  simp_rw [hrow]
  simp [C]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranFixationWeightedTime_lintegral {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (i : Fin (N + 1)) :
    (∫⁻ ω in {ω : ℕ → Fin (N + 1) | ∃ t, ω t = Fin.last N},
      (Rhone.MarkovChain.hitTime (Rhone.MarkovChain.fixationBoundary N) ω : ENNReal)
      ∂(Rhone.MarkovChain.moranChain N r hr).pathLaw i) =
      ENNReal.ofReal (moranFixationWeightedTime N r i.val) := by
  classical
  let C := moranChain N r hr
  let A := fixationBoundary N
  let E : Set (ℕ → Fin (N + 1)) := {ω | ∃ t, ω t = Fin.last N}
  have hE : MeasurableSet E := by
    have hs : E = ⋃ t : ℕ, {ω : ℕ → Fin (N + 1) | ω t = Fin.last N} := by
      ext ω; simp [E]
    rw [hs]
    exact MeasurableSet.iUnion fun t =>
      measurableSet_eq_fun (measurable_pi_apply t) measurable_const
  have hc (j : Fin (N + 1)) : 0 ≤ moranFixProb N r j.val := by
    rw [← moran_fixation_real hN hr j]
    exact measureReal_nonneg
  have hterm (n : ℕ) :
      (∫⁻ ω in E, (if ω n ∈ A then 0 else (1 : ENNReal)) ∂C.pathLaw i) =
        ENNReal.ofReal (∑ j ∈ Aᶜ, C.stepN n i j * moranFixProb N r j.val) := by
    let f : Fin (N + 1) → ENNReal := fun j => if j ∈ A then 0 else 1
    have hm (j : Fin (N + 1)) :
        ((C.pathLaw i).restrict E).map (fun ω => ω n) {j} =
          ENNReal.ofReal (C.stepN n i j * moranFixProb N r j.val) := by
      rw [Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton j),
        Measure.restrict_apply (measurable_pi_apply n (measurableSet_singleton j))]
      have hs : ((fun ω : ℕ → Fin (N + 1) => ω n) ⁻¹' {j}) ∩ E =
          {ω : ℕ → Fin (N + 1) | ω n = j ∧ ∃ t, ω t = Fin.last N} := by
        ext ω; simp [E]
      rw [hs, ← moran_fixation_joint_state hN hr i j n]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    change (∫⁻ ω, f (ω n) ∂(C.pathLaw i).restrict E) = _
    rw [← lintegral_map (Measurable.of_discrete (f := f)) (measurable_pi_apply n),
      lintegral_fintype]
    simp_rw [hm]
    rw [← Finset.sum_add_sum_compl A]
    have hz : ∑ j ∈ A, f j * ENNReal.ofReal (C.stepN n i j * moranFixProb N r j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [f, hj]
    rw [hz, zero_add, ENNReal.ofReal_sum_of_nonneg
      (fun j _ => mul_nonneg (C.stepN_nonneg n i j) (hc j))]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, Finset.mem_compl.mp hj]
  have hae : (fun ω : ℕ → Fin (N + 1) => (hitTime A ω : ENNReal)) =ᵐ[(C.pathLaw i).restrict E]
      pathCost A (fun _ => 1) := by
    apply ae_restrict_of_ae
    filter_upwards [FinChain.ae_stays_mem (moranChain_isAbsorbingSet N hr) i] with ω hω
    exact (pathCost_one_eq_hitTime hω).symm
  change (∫⁻ ω, (hitTime A ω : ENNReal) ∂(C.pathLaw i).restrict E) = _
  rw [lintegral_congr_ae hae]
  unfold pathCost
  simp only [ENNReal.ofReal_one]
  have hmeas (n : ℕ) : AEMeasurable
      (fun ω : ℕ → Fin (N + 1) => if ω n ∈ A then (0 : ENNReal) else 1)
      ((C.pathLaw i).restrict E) :=
    ((Measurable.of_discrete
      (f := fun j : Fin (N + 1) => if j ∈ A then (0 : ENNReal) else 1)).comp
        (measurable_pi_apply n)).aemeasurable
  rw [lintegral_tsum hmeas]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => Finset.sum_nonneg fun j _ => mul_nonneg (C.stepN_nonneg n i j) (hc j))
    (FinChain.summable_potential (moranChain_isAbsorbingSet N hr)
      (moranChain_reaches N hr) (fun j => moranFixProb N r j.val) i)]
  rw [moranFixationWeightedTime_eq_potential N hr i]
  rfl

/-- Source: ewens2004, sec. 3.4. -/
theorem moranConditionalFixationTime_lintegral
    {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (i : Fin (N + 1)) (hi : 0 < i.val) :
    (∫⁻ ω in {ω : ℕ → Fin (N + 1) | ∃ t, (ω t).val = N},
      (Rhone.MarkovChain.hitTime (Rhone.MarkovChain.fixationBoundary N) ω : ENNReal)
      ∂(Rhone.MarkovChain.moranChain N r hr).pathLaw i) /
        ENNReal.ofReal (moranFixProb N r i.val) =
      ENNReal.ofReal (moranConditionalFixationTime N r i.val) := by
  have hp : 0 < moranFixProb N r i.val := by
    unfold moranFixProb
    exact div_pos (geom_pos hi hr) (geom_pos hN hr)
  have hs : {ω : ℕ → Fin (N + 1) | ∃ t, (ω t).val = N} =
      {ω : ℕ → Fin (N + 1) | ∃ t, ω t = Fin.last N} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Fin.ext_iff, Fin.val_last]
  rw [hs, moranFixationWeightedTime_lintegral hN hr i,
    ← ENNReal.ofReal_div_of_pos hp]
  rfl

end Rhone.MarkovChain
