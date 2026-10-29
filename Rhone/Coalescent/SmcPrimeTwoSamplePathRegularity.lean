/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleFixedPosition

/-!
# Almost sure regularity of the paths of the SMC′ chain

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

theorem spatialProcess_law_ae_step (N : ℕ) (R : ℝ) (μ₀ : Measure (SpatialState N))
    (Q : Set (SpatialState N × SpatialState N)) (hQ : MeasurableSet Q)
    (h : ∀ n, ∀ᵐ ω ∂(spatialProcess N R).law μ₀,
      ∀ᵐ a ∂proposalNoiseLaw, (ω n, spatialStep N R (ω n) a) ∈ Q) :
    ∀ᵐ ω ∂(spatialProcess N R).law μ₀, ∀ n, (ω n, ω (n + 1)) ∈ Q := by
  rw [ae_all_iff]
  intro n
  have hΦ : Measurable (Qᶜ.indicator (1 : SpatialState N × SpatialState N → ℝ≥0∞)) :=
    measurable_one.indicator hQ.compl
  have hstep := spatialProcess_law_lintegral_step N R μ₀ n _ hΦ
  have hzero : ∫⁻ ω, ∫⁻ a, Qᶜ.indicator (1 : SpatialState N × SpatialState N → ℝ≥0∞)
      (ω n, spatialStep N R (ω n) a) ∂proposalNoiseLaw ∂(spatialProcess N R).law μ₀ = 0 := by
    refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
    filter_upwards [h n] with ω hω
    refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
    filter_upwards [hω] with a ha
    exact indicator_of_notMem (not_not.mpr ha) _
  rw [hzero] at hstep
  have hm : Measurable fun ω : ℕ → SpatialState N =>
      Qᶜ.indicator (1 : SpatialState N × SpatialState N → ℝ≥0∞) (ω n, ω (n + 1)) :=
    hΦ.comp ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
  rw [lintegral_eq_zero_iff hm] at hstep
  filter_upwards [hstep] with ω hω
  by_contra hc
  have h1 : Qᶜ.indicator (1 : SpatialState N × SpatialState N → ℝ≥0∞) (ω n, ω (n + 1)) = 1 :=
    indicator_of_mem (show (ω n, ω (n + 1)) ∈ Qᶜ from hc) _
  rw [h1] at hω
  exact one_ne_zero hω

theorem spatialProcess_law_ae_shift (N : ℕ) (R : ℝ) (μ₀ : Measure (SpatialState N)) (k : ℕ)
    (B : Set (ℕ → SpatialState N)) (hB : MeasurableSet B)
    (h : ∀ᵐ ω ∂(spatialProcess N R).law μ₀,
      ∀ᵐ ω' ∂(spatialProcess N R).pathLaw (ω k), ω' ∈ B) :
    ∀ᵐ ω ∂(spatialProcess N R).law μ₀, (fun j => ω (k + j)) ∈ B := by
  have hF : Measurable (Bᶜ.indicator (1 : (ℕ → SpatialState N) → ℝ≥0∞)) :=
    measurable_one.indicator hB.compl
  have hshift := spatialProcess_law_lintegral_shift N R μ₀ k _ hF
  have hzero : ∫⁻ ω, ∫⁻ ω', Bᶜ.indicator (1 : (ℕ → SpatialState N) → ℝ≥0∞) ω'
      ∂(spatialProcess N R).pathLaw (ω k) ∂(spatialProcess N R).law μ₀ = 0 := by
    refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
    filter_upwards [h] with ω hω
    refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
    filter_upwards [hω] with ω' hω'
    exact indicator_of_notMem (not_not.mpr hω') _
  rw [hzero] at hshift
  have hm : Measurable fun ω : ℕ → SpatialState N =>
      Bᶜ.indicator (1 : (ℕ → SpatialState N) → ℝ≥0∞) (fun j => ω (k + j)) :=
    hF.comp (Rhone.MarkovChain.DiscreteProcess.measurable_shift (S := SpatialState N) k)
  rw [lintegral_eq_zero_iff hm] at hshift
  filter_upwards [hshift] with ω hω
  by_contra hc
  have h1 : Bᶜ.indicator (1 : (ℕ → SpatialState N) → ℝ≥0∞) (fun j => ω (k + j)) = 1 :=
    indicator_of_mem (show (fun j => ω (k + j)) ∈ Bᶜ from hc) _
  rw [h1] at hω
  exact one_ne_zero hω

theorem spatialProcess_pathLaw_ae_eval_zero (N : ℕ) (R : ℝ) (w : SpatialState N)
    (s : Set (SpatialState N)) (hs : MeasurableSet s) (hw : w ∈ s) :
    ∀ᵐ ω ∂(spatialProcess N R).pathLaw w, ω 0 ∈ s := by
  have h1 : ∀ᵐ z ∂((spatialProcess N R).pathLaw w).map (fun ω => ω 0), z ∈ s := by
    rw [Rhone.MarkovChain.DiscreteProcess.map_eval_zero]
    exact (ae_dirac_iff hs).mpr hw
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
    (show MeasurableSet {z : SpatialState N | z ∈ s} from hs)).mp h1

theorem spatialStep_position_ae (N : ℕ) (R : ℝ) (z : SpatialState N) :
    ∀ᵐ a ∂proposalNoiseLaw, (spatialStep N R z a).1 ≤ 1 ∧
      (1 < z.1 ∨ z.1 ≤ (spatialStep N R z a).1) := by
  filter_upwards [proposalNoiseLaw_ae_marks] with a ha
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · simp only [spatialStep, hstop, ↓reduceIte, le_refl, true_and]
    exact lt_or_ge 1 z.1
  · by_cases hin : z.1 + (proposal R z.2 a).1 < 1
    · simp only [spatialStep, hstop, ↓reduceIte, hin]
      refine ⟨hin.le, Or.inr ?_⟩
      have hstop' := not_or.mp hstop
      have hR : 0 < R := not_le.mp (not_or.mp hstop'.2).1
      have hL : 0 < treeLength z.2 := not_le.mp (not_or.mp hstop'.2).2
      have hd : 0 ≤ (proposal R z.2 a).1 := by
        rw [proposal_distance]
        exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (ha 0).1.le (ha 0).2.le))
          (mul_nonneg (div_nonneg hR.le (by norm_num)) hL.le)
      exact le_add_of_nonneg_right hd
    · simp only [spatialStep, hstop, ↓reduceIte, hin, le_refl, true_and]
      exact lt_or_ge 1 z.1

theorem spatialProcess_law_initial_position_ae (N : ℕ) (R : ℝ) :
    ∀ᵐ ω ∂(spatialProcess N R).law (spatialInitialLaw N), (ω 0).1 = 0 := by
  have hset : MeasurableSet {z : SpatialState N | z.1 = 0} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hinit : ∀ᵐ z ∂spatialInitialLaw N, z.1 = 0 := by
    unfold spatialInitialLaw
    rw [ae_map_iff (show Measurable (fun T : Tree N => ((0 : ℝ), T)) from
      measurable_const.prodMk measurable_id).aemeasurable hset]
    exact Filter.Eventually.of_forall fun T => rfl
  have h1 : ∀ᵐ z ∂((spatialProcess N R).law (spatialInitialLaw N)).map (fun ω => ω 0),
      z.1 = 0 := by
    rw [spatialProcess_law_map_eval_zero]
    exact hinit
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hset).mp h1

theorem spatialProcess_law_position_ae (N : ℕ) (R : ℝ) :
    ∀ᵐ ω ∂(spatialProcess N R).law (spatialInitialLaw N),
      ∀ n, (ω n).1 ≤ 1 ∧ (ω n).1 ≤ (ω (n + 1)).1 := by
  let Q : Set (SpatialState N × SpatialState N) :=
    {w | w.2.1 ≤ 1} ∩ ({w | 1 < w.1.1} ∪ {w | w.1.1 ≤ w.2.1})
  have h21 : Measurable fun w : SpatialState N × SpatialState N => w.2.1 :=
    measurable_fst.comp measurable_snd
  have h11 : Measurable fun w : SpatialState N × SpatialState N => w.1.1 :=
    measurable_fst.comp measurable_fst
  have hQ : MeasurableSet Q :=
    (measurableSet_le h21 measurable_const).inter
      ((measurableSet_lt measurable_const h11).union (measurableSet_le h11 h21))
  have hpair := spatialProcess_law_ae_step N R (spatialInitialLaw N) Q hQ fun n =>
    Filter.Eventually.of_forall fun ω => by
      filter_upwards [spatialStep_position_ae N R (ω n)] with a ha
      exact ⟨ha.1, ha.2⟩
  filter_upwards [hpair, spatialProcess_law_initial_position_ae N R] with ω hω h0
  have hle : ∀ n, (ω n).1 ≤ 1 := by
    intro n
    cases n with
    | zero =>
      rw [h0]
      exact zero_le_one
    | succ m => exact (hω m).1
  intro n
  refine ⟨hle n, ?_⟩
  rcases (hω n).2 with hgt | hmono
  · exact absurd (hle n) (not_le.mpr hgt)
  · exact hmono

theorem TwoSampleArray.spatialStep_rootHeight_ne_ae {T : Tree 2} (hT : TwoSampleArray T)
    {R : ℝ} (hR : 0 < R) (hh : 0 < rootHeight T) (p c : ℝ) :
    ∀ᵐ u ∂proposalNoiseLaw,
      rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2 ≠ c ∨
        rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2 = rootHeight T := by
  by_cases hp : 1 ≤ p
  · refine Filter.Eventually.of_forall fun a => Or.inr ?_
    simp only [SmcPrime.spatialStep, hp, true_or, ↓reduceIte]
  · have hp1 : p < 1 := not_le.mp hp
    let Ψ : ℝ × ℝ → ℝ≥0∞ := fun q => if q.2 = c ∧ q.2 ≠ rootHeight T then 1 else 0
    have hΨ : Measurable Ψ := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_eq_fun measurable_snd measurable_const).inter
        (measurableSet_eq_fun measurable_snd measurable_const).compl
    have hstep := hT.spatialStep_lintegral hR hh hp1 Ψ hΨ
    have hself : ∀ d : ℝ, Ψ (d, rootHeight T) = 0 := by
      intro d
      simp only [Ψ, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    have hjump : ∀ d : ℝ, ∫⁻ a in Ioi 0,
        ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * Ψ (d, a) = 0 := by
      intro d
      refine Eq.trans (lintegral_congr_ae ?_) lintegral_zero
      filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume c)] with a ha
      simp only [Ψ, ha, false_and, ↓reduceIte, mul_zero]
    have hzero : ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (if p + e / (R * rootHeight T) < 1 then
          ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
              Ψ (p + e / (R * rootHeight T), rootHeight T) +
            ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
              Ψ (p + e / (R * rootHeight T), a)
        else Ψ (1, rootHeight T)) = 0 := by
      refine Eq.trans (lintegral_congr fun e => ?_) lintegral_zero
      simp only [hself, hjump, mul_zero, add_zero, ite_self]
    rw [hzero] at hstep
    have hstepm : Measurable fun a : ProposalNoise =>
        SmcPrime.spatialStep 2 R (p, T) a :=
      (spatialStep_measurable 2 R).comp (measurable_const.prodMk measurable_id)
    have hm : Measurable fun u : ProposalNoise =>
        Ψ ((SmcPrime.spatialStep 2 R (p, T) u).1,
          rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2) :=
      hΨ.comp ((measurable_fst.comp hstepm).prodMk
        ((rootHeight_measurable 2).comp (measurable_snd.comp hstepm)))
    rw [lintegral_eq_zero_iff hm] at hstep
    filter_upwards [hstep] with u hu
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    have h3 : Ψ ((SmcPrime.spatialStep 2 R (p, T) u).1,
        rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2) = 1 := by
      exact ite_eq_left_iff.mpr fun hn => absurd ⟨not_not.mp h1, h2⟩ hn
    rw [h3] at hu
    exact one_ne_zero hu

theorem spatialProcess_two_pathLaw_noReturn_ae {R : ℝ} (hR : 0 < R) (z : SpatialState 2)
    (hz : TwoSampleArray z.2) (hh : 0 < rootHeight z.2) :
    ∀ᵐ ω ∂(spatialProcess 2 R).pathLaw z, ∀ j,
      rootHeight (ω (j + 1)).2 ≠ rootHeight (ω 0).2 ∨
        rootHeight (ω (j + 1)).2 = rootHeight (ω j).2 := by
  let Q : Set (SpatialState 2 × SpatialState 2) :=
    {w | rootHeight w.2.2 = rootHeight z.2}ᶜ ∪ {w | rootHeight w.2.2 = rootHeight w.1.2}
  have h22 : Measurable fun w : SpatialState 2 × SpatialState 2 => rootHeight w.2.2 :=
    (rootHeight_measurable 2).comp (measurable_snd.comp measurable_snd)
  have h12 : Measurable fun w : SpatialState 2 × SpatialState 2 => rootHeight w.1.2 :=
    (rootHeight_measurable 2).comp (measurable_snd.comp measurable_fst)
  have hQ : MeasurableSet Q :=
    (measurableSet_eq_fun h22 measurable_const).compl.union (measurableSet_eq_fun h22 h12)
  have hpair := spatialProcess_law_ae_step 2 R (Measure.dirac z) Q hQ fun n => by
    rw [Rhone.MarkovChain.DiscreteProcess.law_dirac]
    filter_upwards [spatialProcess_pathLaw_twoSampleArray_ae R z hz hh] with ω hω
    filter_upwards [(hω n).1.spatialStep_rootHeight_ne_ae hR (hω n).2 (ω n).1
      (rootHeight z.2)] with a ha
    rcases ha with hne | heq
    · exact Or.inl hne
    · exact Or.inr heq
  rw [Rhone.MarkovChain.DiscreteProcess.law_dirac] at hpair
  have hs : MeasurableSet {w : SpatialState 2 | rootHeight w.2 = rootHeight z.2} :=
    measurableSet_eq_fun ((rootHeight_measurable 2).comp measurable_snd) measurable_const
  have h0 := spatialProcess_pathLaw_ae_eval_zero 2 R z _ hs rfl
  filter_upwards [hpair, h0] with ω hω hω0 j
  rcases hω j with hne | heq
  · left
    intro hc
    exact hne (hc.trans hω0)
  · exact Or.inr heq

theorem spatialProcess_two_law_noReturn_ae {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2), ∀ k j,
      rootHeight (ω (k + j + 1)).2 = rootHeight (ω k).2 →
        rootHeight (ω (k + j + 1)).2 = rootHeight (ω (k + j)).2 := by
  rw [ae_all_iff]
  intro k
  let B : Set (ℕ → SpatialState 2) := ⋂ j : ℕ,
    ({ω | rootHeight (ω (j + 1)).2 = rootHeight (ω 0).2}ᶜ ∪
      {ω | rootHeight (ω (j + 1)).2 = rootHeight (ω j).2})
  have hH : ∀ i : ℕ, Measurable fun ω : ℕ → SpatialState 2 => rootHeight (ω i).2 := fun i =>
    (rootHeight_measurable 2).comp (measurable_snd.comp (measurable_pi_apply i))
  have hB : MeasurableSet B := MeasurableSet.iInter fun j =>
    (measurableSet_eq_fun (hH (j + 1)) (hH 0)).compl.union
      (measurableSet_eq_fun (hH (j + 1)) (hH j))
  have hshift := spatialProcess_law_ae_shift 2 R (spatialInitialLaw 2) k B hB (by
    filter_upwards [spatialProcess_two_law_twoSampleArray_ae R] with ω hω
    filter_upwards [spatialProcess_two_pathLaw_noReturn_ae hR (ω k) (hω k).1 (hω k).2]
      with ω' hω'
    refine mem_iInter.mpr fun j => ?_
    rcases hω' j with hne | heq
    · exact Or.inl hne
    · exact Or.inr heq)
  filter_upwards [hshift] with ω hω j hj
  rcases mem_iInter.mp hω j with hne | heq
  · exact absurd hj hne
  · exact heq

end Rhone.Coalescent.SmcPrime
