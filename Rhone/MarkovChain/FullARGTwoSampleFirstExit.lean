/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Process
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # A first-exit identity for discrete-time Markov processes on a measurable state space -/
@[expose] public section

namespace Rhone.MarkovChain.IntervalProcess
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {S : Type*} [MeasurableSpace S]

def stayedIn (A : Set S) (n : ℕ) : Set (ℕ → S) := {ω | ∀ k ≤ n, ω k ∈ A}

theorem stayedIn_measurableSet_piLE {A : Set S} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] (stayedIn A n) := by
  have h : stayedIn A n = ⋂ (k : ℕ) (_ : k ≤ n), (fun ω : ℕ → S => ω k) ⁻¹' A := by
    ext ω
    simp [stayedIn]
  rw [h]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => ?_
  exact (Filtration.piLE (X := fun _ : ℕ => S)).mono hk _
    (DiscreteProcess.measurable_eval_piLE k hA)

theorem stayedIn_measurableSet {A : Set S} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (stayedIn A n) :=
  (Filtration.piLE (X := fun _ : ℕ => S)).le n _ (stayedIn_measurableSet_piLE hA n)

theorem pathLaw_stayedIn_succ (P : DiscreteProcess S) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {h : S → ℝ} (hh : Measurable h)
    {M : ℝ} (hM : ∀ s, |h s| ≤ M)
    (hstep : ∀ s ∈ A, ∫ y, A.indicator h y ∂P.step s + (P.step s).real B = h s)
    (x : S) (n : ℕ) :
    ∫ ω in stayedIn A (n + 1), h (ω (n + 1)) ∂P.pathLaw x =
      ∫ ω in stayedIn A n, h (ω n) ∂P.pathLaw x -
        (P.pathLaw x).real (stayedIn A n ∩ {ω | ω (n + 1) ∈ B}) := by
  have hM0 : 0 ≤ M := (abs_nonneg (h x)).trans (hM x)
  have hsn := stayedIn_measurableSet_piLE hA n
  have hsn' := stayedIn_measurableSet hA n
  have hevA : MeasurableSet {ω : ℕ → S | ω (n + 1) ∈ A} := hA.preimage (measurable_pi_apply _)
  have hevB : MeasurableSet {ω : ℕ → S | ω (n + 1) ∈ B} := hB.preimage (measurable_pi_apply _)
  have hsplit : stayedIn A (n + 1) = stayedIn A n ∩ {ω | ω (n + 1) ∈ A} := by
    ext ω
    simp only [stayedIn, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro hω
      exact ⟨fun k hk => hω k (by omega), hω (n + 1) le_rfl⟩
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact h1 k (by omega)
      · have : k = n + 1 := by omega
        rw [this]
        exact h2
  have hmass : Measurable fun ω : ℕ → S => (P.step (ω n)).real B :=
    ((P.step.measurable_coe hB).ennreal_toReal).comp (measurable_pi_apply n)
  have hmassI : Integrable (fun ω : ℕ → S => (P.step (ω n)).real B) (P.pathLaw x) :=
    Integrable.of_bound hmass.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have hhI : Integrable (fun ω : ℕ → S => h (ω n)) (P.pathLaw x) :=
    Integrable.of_bound (hh.comp (measurable_pi_apply n)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa using hM (ω n))
  have h1 : ∫ ω in stayedIn A (n + 1), h (ω (n + 1)) ∂P.pathLaw x =
      ∫ ω in stayedIn A n, ∫ y, A.indicator h y ∂P.step (ω n) ∂P.pathLaw x := by
    rw [hsplit, ← setIntegral_indicator hevA]
    exact P.setIntegral_eval_succ x n (hh.indicator hA) (M := M)
      (fun s => by
        by_cases hs : s ∈ A
        · rw [Set.indicator_of_mem hs]
          exact hM s
        · rw [Set.indicator_of_notMem hs, abs_zero]
          exact hM0) hsn
  have h2 : (P.pathLaw x).real (stayedIn A n ∩ {ω | ω (n + 1) ∈ B}) =
      ∫ ω in stayedIn A n, (P.step (ω n)).real B ∂P.pathLaw x := by
    have hone : ∫ ω in stayedIn A n, B.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        ∫ ω in stayedIn A n, ∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂P.step (ω n)
          ∂P.pathLaw x :=
      P.setIntegral_eval_succ x n (measurable_const.indicator hB) (M := 1)
        (fun s => by
          by_cases hs : s ∈ B
          · rw [Set.indicator_of_mem hs, abs_one]
          · rw [Set.indicator_of_notMem hs, abs_zero]
            exact zero_le_one) hsn
    have hleft : ∫ ω in stayedIn A n, B.indicator (fun _ => (1 : ℝ)) (ω (n + 1)) ∂P.pathLaw x =
        (P.pathLaw x).real (stayedIn A n ∩ {ω | ω (n + 1) ∈ B}) := by
      have : (fun ω : ℕ → S => B.indicator (fun _ => (1 : ℝ)) (ω (n + 1))) =
          {ω : ℕ → S | ω (n + 1) ∈ B}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp [Set.indicator]
      rw [this, setIntegral_indicator hevB, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hleft, hone]
    refine setIntegral_congr_fun hsn' fun ω _ => ?_
    exact integral_indicator_one hB
  rw [h1, h2, ← integral_sub hhI.integrableOn hmassI.integrableOn]
  refine setIntegral_congr_fun hsn' fun ω hω => ?_
  have := hstep (ω n) (hω n le_rfl)
  change ∫ y, A.indicator h y ∂P.step (ω n) = h (ω n) - (P.step (ω n)).real B
  linarith

theorem pathLaw_real_firstExit (P : DiscreteProcess S) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B)
    {h : S → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ s, |h s| ≤ M)
    (hstep : ∀ s ∈ A, ∫ y, A.indicator h y ∂P.step s + (P.step s).real B = h s)
    (x : S) (hx : x ∈ A)
    (hlim : Tendsto (fun n => (P.pathLaw x).real {ω | ω n ∈ A}) atTop (𝓝 0)) :
    (P.pathLaw x).real {ω | ∃ n, (∀ k ≤ n, ω k ∈ A) ∧ ω (n + 1) ∈ B} = h x := by
  set μ := P.pathLaw x with hμ
  let F : ℕ → Set (ℕ → S) := fun n => stayedIn A n ∩ {ω | ω (n + 1) ∈ B}
  let a : ℕ → ℝ := fun n => ∫ ω in stayedIn A n, h (ω n) ∂μ
  have hFm : ∀ n, MeasurableSet (F n) := fun n =>
    (stayedIn_measurableSet hA n).inter (hB.preimage (measurable_pi_apply _))
  have hzero : ∀ᵐ ω ∂μ, ω 0 ∈ A ∧ h (ω 0) = h x := by
    have hset : MeasurableSet {y : S | y ∈ A ∧ h y = h x} :=
      hA.inter (hh (measurableSet_singleton (h x)))
    apply ae_of_ae_map (μ := μ) (f := fun ω : ℕ → S => ω 0)
      (p := fun y => y ∈ A ∧ h y = h x) (measurable_pi_apply 0).aemeasurable
    rw [hμ, P.map_eval_zero]
    exact (ae_dirac_iff hset).mpr ⟨hx, rfl⟩
  have ha0 : a 0 = h x := by
    change ∫ ω in stayedIn A 0, h (ω 0) ∂μ = h x
    rw [← integral_indicator (stayedIn_measurableSet hA 0)]
    have : (stayedIn A 0).indicator (fun ω : ℕ → S => h (ω 0)) =ᵐ[μ] fun _ => h x := by
      filter_upwards [hzero] with ω hω
      have hmem : ω ∈ stayedIn A 0 := by
        intro k hk
        have : k = 0 := by omega
        rw [this]
        exact hω.1
      rw [Set.indicator_of_mem hmem, hω.2]
    rw [integral_congr_ae this, integral_const, probReal_univ, one_smul]
  have hsum : ∀ n, ∑ k ∈ Finset.range n, μ.real (F k) = h x - a n := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have := pathLaw_stayedIn_succ P hA hB hh hM hstep x n
      change a (n + 1) = a n - μ.real (F n) at this
      linarith
  have hM0 : 0 ≤ M := (abs_nonneg (h x)).trans (hM x)
  have habs : ∀ n, |a n| ≤ M * μ.real {ω | ω n ∈ A} := by
    intro n
    have h1 : ‖∫ ω in stayedIn A n, h (ω n) ∂μ‖ ≤ M * μ.real (stayedIn A n) :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
        (fun ω _ => by simpa using hM (ω n))
    have h2 : μ.real (stayedIn A n) ≤ μ.real {ω | ω n ∈ A} :=
      measureReal_mono (fun ω hω => hω n le_rfl)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
  have ha : Tendsto a atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by simpa using habs n)
    simpa using hlim.const_mul M
  have hpart : Tendsto (fun n => ∑ k ∈ Finset.range n, μ.real (F k)) atTop (𝓝 (h x)) := by
    have : Tendsto (fun n => h x - a n) atTop (𝓝 (h x - 0)) := tendsto_const_nhds.sub ha
    rw [sub_zero] at this
    exact this.congr fun n => (hsum n).symm
  have hhas : HasSum (fun k => μ.real (F k)) (h x) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun _ => measureReal_nonneg) _).mpr hpart
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    have key : ∀ n m, n < m → Disjoint (F n) (F m) := by
      intro n m hnm
      rw [Set.disjoint_left]
      intro ω hn hm
      exact Set.disjoint_left.mp hAB (hm.1 (n + 1) hnm) hn.2
    intro n m hnm
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · exact key n m hlt
    · exact (key m n hgt).symm
  have hE : {ω : ℕ → S | ∃ n, (∀ k ≤ n, ω k ∈ A) ∧ ω (n + 1) ∈ B} = ⋃ n, F n := by
    ext ω
    simp [F, stayedIn]
  rw [hE, measureReal_def, measure_iUnion hdisj hFm,
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  exact hhas.tsum_eq

end Rhone.MarkovChain.IntervalProcess
