/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FullARGTerminationFoster

/-!
# A weighted first-exit identity for discrete-time Markov processes, in extended nonnegative reals
-/
@[expose] public section

namespace Rhone.MarkovChain.IntervalProcess
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {S : Type*} [MeasurableSpace S]

theorem pathLaw_setLIntegral_eval_succ (P : DiscreteProcess S) (x : S) (n : ℕ)
    {g : S → ℝ≥0∞} (hg : Measurable g) {B : Set (ℕ → S)}
    (hB : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B) :
    ∫⁻ ω in B, g (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ ω in B, ∫⁻ y, g y ∂P.step (ω n) ∂P.pathLaw x := by
  have hB' : MeasurableSet B := (Filtration.piLE (X := fun _ : ℕ => S)).le n _ hB
  have hmeas : ((P.pathLaw x).restrict B).map (fun ω => ω (n + 1)) =
      (((P.pathLaw x).restrict B).map (fun ω => ω n)).bind P.step := by
    ext C hC
    have hev : MeasurableSet ((fun ω : ℕ → S => ω (n + 1)) ⁻¹' C) :=
      hC.preimage (measurable_pi_apply _)
    have hmass : Measurable fun ω : ℕ → S => (P.step (ω n)).real C :=
      ((P.step.measurable_coe hC).ennreal_toReal).comp (measurable_pi_apply n)
    have hmassI : Integrable (fun ω : ℕ → S => (P.step (ω n)).real C)
        ((P.pathLaw x).restrict B) :=
      Integrable.of_bound hmass.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
          exact measureReal_le_one)
    have hreal : ∫ ω in B, C.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        ∫ ω in B, ∫ y, C.indicator (fun _ => (1 : ℝ)) y ∂P.step (ω n) ∂P.pathLaw x :=
      P.setIntegral_eval_succ x n (measurable_const.indicator hC) (M := 1)
        (fun s => by
          by_cases hs : s ∈ C
          · rw [Set.indicator_of_mem hs, abs_one]
          · rw [Set.indicator_of_notMem hs, abs_zero]
            exact zero_le_one) hB
    have hleft : ∫ ω in B, C.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        ((P.pathLaw x).restrict B).real ((fun ω : ℕ → S => ω (n + 1)) ⁻¹' C) := by
      have : (fun ω : ℕ → S => C.indicator (fun _ => (1 : ℝ)) (ω (n + 1))) =
          ((fun ω : ℕ → S => ω (n + 1)) ⁻¹' C).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        rfl
      rw [this]
      exact integral_indicator_one hev
    have hright : ∫ ω in B, ∫ y, C.indicator (fun _ => (1 : ℝ)) y ∂P.step (ω n) ∂P.pathLaw x =
        ∫ ω in B, (P.step (ω n)).real C ∂P.pathLaw x :=
      setIntegral_congr_fun hB' fun ω _ => integral_indicator_one hC
    rw [Measure.map_apply (measurable_pi_apply _) hC,
      Measure.bind_apply hC (Kernel.measurable _).aemeasurable,
      lintegral_map (P.step.measurable_coe hC) (measurable_pi_apply n)]
    have hfin : ((P.pathLaw x).restrict B) ((fun ω : ℕ → S => ω (n + 1)) ⁻¹' C) ≠ ∞ :=
      measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin, ← measureReal_def, ← hleft, hreal, hright,
      ofReal_integral_eq_lintegral_ofReal hmassI
        (Filter.Eventually.of_forall fun ω => measureReal_nonneg)]
    refine lintegral_congr fun ω => ?_
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have h1 : ∫⁻ ω in B, g (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ y, g y ∂((P.pathLaw x).restrict B).map (fun ω => ω (n + 1)) :=
    (lintegral_map hg (measurable_pi_apply (n + 1))).symm
  rw [h1, hmeas, Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable,
    lintegral_map hg.lintegral_kernel (measurable_pi_apply n)]

theorem pathLaw_lintegral_mul_eval_succ (P : DiscreteProcess S) (x : S) (n : ℕ)
    {g : S → ℝ≥0∞} (hg : Measurable g) {W : (ℕ → S) → ℝ≥0∞}
    (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] W) :
    ∫⁻ ω, W ω * g (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ ω, W ω * ∫⁻ y, g y ∂P.step (ω n) ∂P.pathLaw x := by
  have hle := (Filtration.piLE (X := fun _ : ℕ => S)).le n
  have hG : Measurable (fun ω : ℕ → S => ∫⁻ y, g y ∂P.step (ω n)) :=
    hg.lintegral_kernel.comp (measurable_pi_apply n)
  have hge : Measurable (fun ω : ℕ → S => g (ω (n + 1))) := hg.comp (measurable_pi_apply _)
  refine @Measurable.ennreal_induction (ℕ → S) (Filtration.piLE (X := fun _ : ℕ => S) n)
    (fun W => ∫⁻ ω, W ω * g (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ ω, W ω * ∫⁻ y, g y ∂P.step (ω n) ∂P.pathLaw x) ?_ ?_ ?_ W hW
  · intro c B hB
    have hB' := hle _ hB
    have e : ∀ F : (ℕ → S) → ℝ≥0∞, (fun ω => B.indicator (fun _ => c) ω * F ω) =
        B.indicator (fun ω => c * F ω) := by
      intro F
      funext ω
      by_cases h : ω ∈ B <;> simp [h]
    change ∫⁻ ω, B.indicator (fun _ => c) ω * g (ω (n + 1)) ∂P.pathLaw x =
      ∫⁻ ω, B.indicator (fun _ => c) ω * ∫⁻ y, g y ∂P.step (ω n) ∂P.pathLaw x
    rw [e (fun ω => g (ω (n + 1))), e (fun ω => ∫⁻ y, g y ∂P.step (ω n)),
      lintegral_indicator hB', lintegral_indicator hB', lintegral_const_mul _ hge,
      lintegral_const_mul _ hG, pathLaw_setLIntegral_eval_succ P x n hg hB]
  · intro f1 f2 _ hf1 hf2 h1 h2
    have m1 : Measurable fun ω : ℕ → S => f1 ω * g (ω (n + 1)) :=
      (hf1.mono hle le_rfl).mul hge
    have m2 : Measurable fun ω : ℕ → S => f1 ω * ∫⁻ y, g y ∂P.step (ω n) :=
      (hf1.mono hle le_rfl).mul hG
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left m1, lintegral_add_left m2, h1, h2]
  · intro f hf hmono hall
    have m1 : ∀ i, Measurable fun ω : ℕ → S => f i ω * g (ω (n + 1)) :=
      fun i => ((hf i).mono hle le_rfl).mul hge
    have m2 : ∀ i, Measurable fun ω : ℕ → S => f i ω * ∫⁻ y, g y ∂P.step (ω n) :=
      fun i => ((hf i).mono hle le_rfl).mul hG
    have o1 : Monotone fun (i : ℕ) (ω : ℕ → S) => f i ω * g (ω (n + 1)) :=
      fun i j hij ω => mul_le_mul_left (hmono hij ω) _
    have o2 : Monotone fun (i : ℕ) (ω : ℕ → S) => f i ω * ∫⁻ y, g y ∂P.step (ω n) :=
      fun i j hij ω => mul_le_mul_left (hmono hij ω) _
    simp only [ENNReal.iSup_mul]
    rw [lintegral_iSup m1 o1, lintegral_iSup m2 o2]
    exact iSup_congr hall

open scoped Classical in
noncomputable def exitValue (A : Set S) (g : S → ℝ≥0∞) (m : ℕ) (ω : ℕ → S) : ℝ≥0∞ :=
  ∑' k, if m ≤ k ∧ ω k ∈ A ∧ ω (k + 1) ∉ A then g (ω (k + 1)) else 0

open scoped Classical in
theorem pathLaw_lintegral_exit_step (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {g : S → ℝ≥0∞} (hg : Measurable g)
    (hstep : ∀ s ∈ A, ∫⁻ y, g y ∂P.step s = g s) (x : S) {m n : ℕ} (hmn : m ≤ n)
    {W : (ℕ → S) → ℝ≥0∞} (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) m] W)
    (hmono : ∀ᵐ ω ∂P.pathLaw x, ∀ k, ω (k + 1) ∈ A → ω k ∈ A) :
    ∫⁻ ω, W ω * A.indicator g (ω n) ∂P.pathLaw x =
      ∫⁻ ω, W ω * (if m ≤ n ∧ ω n ∈ A ∧ ω (n + 1) ∉ A then g (ω (n + 1)) else 0)
          ∂P.pathLaw x +
        ∫⁻ ω, W ω * A.indicator g (ω (n + 1)) ∂P.pathLaw x := by
  have hWn : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] W :=
    hW.mono ((Filtration.piLE (X := fun _ : ℕ => S)).mono hmn) le_rfl
  have hW' : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      (fun ω : ℕ → S => W ω * A.indicator (fun _ => (1 : ℝ≥0∞)) (ω n)) :=
    hWn.mul ((measurable_const.indicator hA).comp (DiscreteProcess.measurable_eval_piLE n))
  have hWa : Measurable W := hW.mono ((Filtration.piLE (X := fun _ : ℕ => S)).le m) le_rfl
  have h1 := pathLaw_lintegral_mul_eval_succ P x n hg hW'
  have hr : ∀ ω : ℕ → S, W ω * A.indicator (fun _ => (1 : ℝ≥0∞)) (ω n) *
      ∫⁻ y, g y ∂P.step (ω n) = W ω * A.indicator g (ω n) := by
    intro ω
    by_cases h : ω n ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one, hstep _ h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, zero_mul]
  have hl : ∀ᵐ ω ∂P.pathLaw x, W ω * A.indicator (fun _ => (1 : ℝ≥0∞)) (ω n) *
      g (ω (n + 1)) =
      W ω * (if m ≤ n ∧ ω n ∈ A ∧ ω (n + 1) ∉ A then g (ω (n + 1)) else 0) +
        W ω * A.indicator g (ω (n + 1)) := by
    filter_upwards [hmono] with ω hω
    by_cases h : ω n ∈ A
    · by_cases h' : ω (n + 1) ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h', mul_one,
          ite_eq_right (fun hh => hh.2.2 h'), mul_zero, zero_add]
      · rw [Set.indicator_of_mem h, Set.indicator_of_notMem h', mul_one,
          ite_eq_left ⟨hmn, h, h'⟩, mul_zero, add_zero]
    · have h' : ω (n + 1) ∉ A := fun hh => h (hω n hh)
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', mul_zero, zero_mul,
        ite_eq_right (fun hh => h hh.2.1), mul_zero, add_zero]
  have hexitm : Measurable fun ω : ℕ → S =>
      W ω * (if m ≤ n ∧ ω n ∈ A ∧ ω (n + 1) ∉ A then g (ω (n + 1)) else 0) := by
    refine hWa.mul (Measurable.ite ?_ (hg.comp (measurable_pi_apply _)) measurable_const)
    exact MeasurableSet.inter (MeasurableSet.const _)
      ((hA.preimage (measurable_pi_apply n)).inter
        (hA.preimage (measurable_pi_apply (n + 1))).compl)
  rw [← lintegral_add_left hexitm, ← lintegral_congr_ae hl, h1]
  exact lintegral_congr fun ω => (hr ω).symm

open scoped Classical in
theorem pathLaw_lintegral_exit_sum (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {g : S → ℝ≥0∞} (hg : Measurable g)
    (hstep : ∀ s ∈ A, ∫⁻ y, g y ∂P.step s = g s) (x : S) (m : ℕ)
    {W : (ℕ → S) → ℝ≥0∞} (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) m] W)
    (hmono : ∀ᵐ ω ∂P.pathLaw x, ∀ k, ω (k + 1) ∈ A → ω k ∈ A) (j : ℕ) :
    ∫⁻ ω, W ω * A.indicator g (ω m) ∂P.pathLaw x =
      ∑ k ∈ Finset.range (j + m),
          ∫⁻ ω, W ω * (if m ≤ k ∧ ω k ∈ A ∧ ω (k + 1) ∉ A then g (ω (k + 1)) else 0)
            ∂P.pathLaw x +
        ∫⁻ ω, W ω * A.indicator g (ω (j + m)) ∂P.pathLaw x := by
  induction j with
  | zero =>
    rw [zero_add, Finset.sum_eq_zero, zero_add]
    intro k hk
    have hkm : ¬m ≤ k := by
      have := Finset.mem_range.mp hk
      omega
    simp [hkm]
  | succ j ih =>
    have e : j + 1 + m = j + m + 1 := by omega
    rw [e, Finset.sum_range_succ, add_assoc,
      ← pathLaw_lintegral_exit_step P hA hg hstep x (Nat.le_add_left m j) hW hmono]
    exact ih

open scoped Classical in
theorem pathLaw_lintegral_mul_exitValue_le (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {g : S → ℝ≥0∞} (hg : Measurable g)
    (hstep : ∀ s ∈ A, ∫⁻ y, g y ∂P.step s = g s) (x : S) (m : ℕ)
    {W : (ℕ → S) → ℝ≥0∞} (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) m] W)
    (hmono : ∀ᵐ ω ∂P.pathLaw x, ∀ k, ω (k + 1) ∈ A → ω k ∈ A) :
    ∫⁻ ω, W ω * exitValue A g m ω ∂P.pathLaw x ≤
      ∫⁻ ω, W ω * A.indicator g (ω m) ∂P.pathLaw x := by
  have hWa : Measurable W := hW.mono ((Filtration.piLE (X := fun _ : ℕ => S)).le m) le_rfl
  have hterm : ∀ k, Measurable fun ω : ℕ → S =>
      W ω * (if m ≤ k ∧ ω k ∈ A ∧ ω (k + 1) ∉ A then g (ω (k + 1)) else 0) := by
    intro k
    refine hWa.mul (Measurable.ite ?_ (hg.comp (measurable_pi_apply _)) measurable_const)
    exact MeasurableSet.inter (MeasurableSet.const _)
      ((hA.preimage (measurable_pi_apply k)).inter
        (hA.preimage (measurable_pi_apply (k + 1))).compl)
  unfold exitValue
  simp only [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun k => (hterm k).aemeasurable]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have h := pathLaw_lintegral_exit_sum P hA hg hstep x m hW hmono n
  rw [h]
  exact le_trans (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_add_right n m)))
    le_self_add

open scoped Classical in
theorem pathLaw_lintegral_mul_exitValue (P : DiscreteProcess S) {A : Set S}
    (hA : MeasurableSet A) {g : S → ℝ≥0∞} (hg : Measurable g)
    (hstep : ∀ s ∈ A, ∫⁻ y, g y ∂P.step s = g s) (x : S) (m : ℕ)
    {W : (ℕ → S) → ℝ≥0∞} (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => S) m] W)
    (hmono : ∀ᵐ ω ∂P.pathLaw x, ∀ k, ω (k + 1) ∈ A → ω k ∈ A)
    (hexit : ∀ᵐ ω ∂P.pathLaw x, ∃ n, ω n ∉ A)
    {D : (ℕ → S) → ℝ≥0∞} (hD : ∫⁻ ω, D ω ∂P.pathLaw x ≠ ∞)
    (hdom : ∀ᵐ ω ∂P.pathLaw x, ∀ n, m ≤ n → ω n ∈ A → W ω * g (ω n) ≤ D ω) :
    ∫⁻ ω, W ω * A.indicator g (ω m) ∂P.pathLaw x =
      ∫⁻ ω, W ω * exitValue A g m ω ∂P.pathLaw x := by
  have hWa : Measurable W := hW.mono ((Filtration.piLE (X := fun _ : ℕ => S)).le m) le_rfl
  have hterm : ∀ k, Measurable fun ω : ℕ → S =>
      W ω * (if m ≤ k ∧ ω k ∈ A ∧ ω (k + 1) ∉ A then g (ω (k + 1)) else 0) := by
    intro k
    refine hWa.mul (Measurable.ite ?_ (hg.comp (measurable_pi_apply _)) measurable_const)
    exact MeasurableSet.inter (MeasurableSet.const _)
      ((hA.preimage (measurable_pi_apply k)).inter
        (hA.preimage (measurable_pi_apply (k + 1))).compl)
  have hrem : Tendsto (fun j : ℕ => ∫⁻ ω, W ω * A.indicator g (ω (j + m)) ∂P.pathLaw x)
      atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_of_dominated_convergence (μ := P.pathLaw x)
      (F := fun (j : ℕ) (ω : ℕ → S) => W ω * A.indicator g (ω (j + m)))
      (f := fun _ => 0) D
      (fun j => hWa.mul ((hg.indicator hA).comp (measurable_pi_apply _)))
      (fun j => by
        filter_upwards [hdom] with ω hω
        by_cases h : ω (j + m) ∈ A
        · rw [Set.indicator_of_mem h]
          exact hω (j + m) (Nat.le_add_left m j) h
        · rw [Set.indicator_of_notMem h, mul_zero]
          exact bot_le)
      hD
      (by
        filter_upwards [hmono, hexit] with ω hω hex
        obtain ⟨n0, hn0⟩ := hex
        have hout : ∀ n, n0 ≤ n → ω n ∉ A := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => exact hn0
          | succ n _ ih => exact fun hh => ih (hω n hh)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop n0] with j hj
        rw [Set.indicator_of_notMem (hout (j + m) (by omega)), mul_zero])
    simpa using hlim
  unfold exitValue
  simp only [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun k => (hterm k).aemeasurable]
  have hpart := (ENNReal.tendsto_nat_tsum fun k => ∫⁻ ω, W ω *
    (if m ≤ k ∧ ω k ∈ A ∧ ω (k + 1) ∉ A then g (ω (k + 1)) else 0) ∂P.pathLaw x).comp
    (tendsto_add_atTop_nat m)
  have hsum := hpart.add hrem
  rw [add_zero] at hsum
  refine tendsto_nhds_unique ?_ hsum
  refine tendsto_const_nhds.congr fun j => ?_
  exact pathLaw_lintegral_exit_sum P hA hg hstep x m hW hmono j

end Rhone.MarkovChain.IntervalProcess
