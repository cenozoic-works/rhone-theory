/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSamplePathInvariant
public import Rhone.Coalescent.SmcPrimeSpatialFirstStep
public import Rhone.Analysis.SmcPrimeTwoSampleFormulas

/-!
# Two samples: no change of height between two positions of the SMC′ chain

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”; wilton_carmi_hobolth2015, eq. (7). -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

noncomputable def heldWeight (s L : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-L) * (s * L) ^ n / (n.factorial : ℝ)

theorem heldWeight_nonneg {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ heldWeight s L n :=
  div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (mul_nonneg hs hL) n))
    (Nat.cast_nonneg _)

theorem lintegral_Ioi_exp_neg (L : ℝ) :
    ∫⁻ e in Ioi L, ENNReal.ofReal (Real.exp (-e)) = ENNReal.ofReal (Real.exp (-L)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi L)
    (Filter.Eventually.of_forall fun e => Real.exp_nonneg _), integral_exp_neg_Ioi]

theorem lintegral_Ioi_exp_neg_gt {L : ℝ} (hL : 0 ≤ L) :
    ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) * (if L < e then 1 else 0) =
      ENNReal.ofReal (Real.exp (-L)) := by
  have h : ∀ e : ℝ, ENNReal.ofReal (Real.exp (-e)) * (if L < e then (1 : ℝ≥0∞) else 0) =
      (Ioi L).indicator (fun e => ENNReal.ofReal (Real.exp (-e))) e := by
    intro e
    by_cases he : L < e
    · rw [indicator_of_mem (show e ∈ Ioi L from he)]
      simp only [he, ↓reduceIte, mul_one]
    · rw [indicator_of_notMem (show e ∉ Ioi L from he)]
      simp only [he, ↓reduceIte, mul_zero]
  rw [lintegral_congr h, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr hL]
  exact lintegral_Ioi_exp_neg L

theorem lintegral_heldWeight_step {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) (n : ℕ) :
    ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (ENNReal.ofReal s * (if e ≤ L then ENNReal.ofReal (heldWeight s (L - e) n) else 0)) =
      ENNReal.ofReal (heldWeight s L (n + 1)) := by
  let C : ℝ := s ^ (n + 1) * Real.exp (-L) / (n.factorial : ℝ)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (pow_nonneg hs _) (Real.exp_nonneg _))
    (Nat.cast_nonneg _)
  let f : ℝ → ℝ := fun e => C * (L - e) ^ n
  let F : ℝ → ℝ := fun e => -(C / ((n : ℝ) + 1)) * (L - e) ^ (n + 1)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hpt : ∀ e : ℝ, ENNReal.ofReal (Real.exp (-e)) *
      (ENNReal.ofReal s * (if e ≤ L then ENNReal.ofReal (heldWeight s (L - e) n) else 0)) =
      (Iic L).indicator (fun e => ENNReal.ofReal (f e)) e := by
    intro e
    by_cases hle : e ≤ L
    · rw [indicator_of_mem (show e ∈ Iic L from hle)]
      simp only [hle, ↓reduceIte]
      rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      simp only [heldWeight, f, C]
      rw [mul_pow, show -L = -e + -(L - e) by ring, Real.exp_add]
      ring
    · rw [indicator_of_notMem (show e ∉ Iic L from hle)]
      simp only [hle, ↓reduceIte, mul_zero]
  have hF : ∀ e : ℝ, HasDerivAt F (f e) e := by
    intro e
    have h1 : HasDerivAt (fun x : ℝ => L - x) (-1) e := by
      simpa using (hasDerivAt_id e).const_sub L
    have h2 := (h1.pow (n + 1)).const_mul (-(C / ((n : ℝ) + 1)))
    convert h2 using 1
    simp only [f, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hf : Continuous f := by fun_prop
  rw [lintegral_congr hpt, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic,
    ← setLIntegral_congr Ioo_ae_eq_Ioc,
    lintegral_Ioo_ofReal_of_hasDerivAt hL hF hf
      (fun e he => mul_nonneg hC (pow_nonneg (sub_nonneg.mpr he.2.le) n))]
  congr 1
  simp only [F, heldWeight, C, sub_self, sub_zero, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp
  ring

theorem tsum_heldWeight {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) :
    ∑' n, ENNReal.ofReal (heldWeight s L n) =
      ENNReal.ofReal (Real.exp (-((1 - s) * L))) := by
  have h1 : HasSum (fun n : ℕ => (s * L) ^ n / (n.factorial : ℝ)) (Real.exp (s * L)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (s * L)
  have h2 : HasSum (fun n : ℕ => heldWeight s L n) (Real.exp (-L) * Real.exp (s * L)) := by
    have h3 := h1.mul_left (Real.exp (-L))
    refine h3.congr_fun ?_
    intro n
    simp only [heldWeight]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => heldWeight_nonneg hs hL n) h2.summable,
    h2.tsum_eq, ← Real.exp_add]
  congr 2
  ring

noncomputable def heldTerm (y c : ℝ) (n : ℕ) (ω : ℕ → SpatialState 2) : ℝ≥0∞ :=
  (if (ω n).1 ≤ y then 1 else 0) * (if y < (ω (n + 1)).1 then 1 else 0) *
    ∏ j ∈ Finset.range (n + 1), (if rootHeight (ω j).2 = c then 1 else 0)

theorem measurable_heldTerm (y c : ℝ) (n : ℕ) : Measurable (heldTerm y c n) := by
  unfold heldTerm
  refine (Measurable.mul ?_ ?_).mul (Finset.measurable_prod _ fun j _ => ?_)
  · exact Measurable.ite (measurableSet_le (measurable_fst.comp (measurable_pi_apply n))
      measurable_const) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const
      (measurable_fst.comp (measurable_pi_apply (n + 1)))) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_eq_fun ((rootHeight_measurable 2).comp
      (measurable_snd.comp (measurable_pi_apply j))) measurable_const)
      measurable_const measurable_const

theorem heldTerm_streamCons_zero (y c : ℝ) (z : SpatialState 2) (ω' : ℕ → SpatialState 2) :
    heldTerm y c 0 (streamCons (z, ω')) =
      (if z.1 ≤ y then 1 else 0) * (if rootHeight z.2 = c then 1 else 0) *
        (if y < (ω' 0).1 then 1 else 0) := by
  simp only [heldTerm, zero_add, Finset.range_one, Finset.prod_singleton]
  change (if z.1 ≤ y then (1 : ℝ≥0∞) else 0) * (if y < (ω' 0).1 then 1 else 0) *
    (if rootHeight z.2 = c then 1 else 0) = _
  ring

theorem heldTerm_streamCons_succ (y c : ℝ) (n : ℕ) (z : SpatialState 2)
    (ω' : ℕ → SpatialState 2) :
    heldTerm y c (n + 1) (streamCons (z, ω')) =
      (if rootHeight z.2 = c then 1 else 0) * heldTerm y c n ω' := by
  unfold heldTerm
  rw [Finset.prod_range_succ' _ (n + 1)]
  change (if (ω' n).1 ≤ y then (1 : ℝ≥0∞) else 0) * (if y < (ω' (n + 1)).1 then 1 else 0) *
    ((∏ j ∈ Finset.range (n + 1), (if rootHeight (ω' j).2 = c then 1 else 0)) *
      (if rootHeight z.2 = c then 1 else 0)) = _
  ring

theorem spatialProcess_pathLaw_lintegral_eval_zero (N : ℕ) (R : ℝ) (w : SpatialState N)
    (F : SpatialState N → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂(spatialProcess N R).pathLaw w = F w := by
  rw [← lintegral_map hF (measurable_pi_apply 0), Rhone.MarkovChain.DiscreteProcess.map_eval_zero,
    lintegral_dirac' _ hF]

theorem TwoSampleArray.spatialStep_position_gt_lintegral {T : Tree 2} (hT : TwoSampleArray T)
    {R : ℝ} (hR : 0 < R) (hh : 0 < rootHeight T) {p t : ℝ} (hpt : p ≤ t) (ht : t < 1) :
    ∫⁻ u, (if t < (SmcPrime.spatialStep 2 R (p, T) u).1 then (1 : ℝ≥0∞) else 0)
        ∂proposalNoiseLaw =
      ENNReal.ofReal (Real.exp (-(R * rootHeight T * (t - p)))) := by
  have hΨ : Measurable (fun q : ℝ × ℝ => if t < q.1 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      measurable_const
  have hRh : 0 < R * rootHeight T := mul_pos hR hh
  have hL : 0 ≤ R * rootHeight T * (t - p) := mul_nonneg hRh.le (sub_nonneg.mpr hpt)
  have hmass := lintegral_twoSampleJumpDensity hh
  have hone : ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) +
      ENNReal.ofReal (1 - twoSampleSelfMass (rootHeight T)) = 1 := by
    rw [← ENNReal.ofReal_add (twoSampleSelfMass_nonneg hh)
      (sub_nonneg.mpr (twoSampleSelfMass_le_one hh)), add_sub_cancel, ENNReal.ofReal_one]
  refine (hT.spatialStep_lintegral hR hh (hpt.trans_lt ht) _ hΨ).trans ?_
  rw [← lintegral_Ioi_exp_neg_gt hL]
  refine setLIntegral_congr_fun measurableSet_Ioi fun e he => ?_
  have hiff : t < p + e / (R * rootHeight T) ↔ R * rootHeight T * (t - p) < e := by
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hRh, mul_comm]
  dsimp only
  congr 1
  by_cases h1 : p + e / (R * rootHeight T) < 1
  · by_cases h2 : t < p + e / (R * rootHeight T)
    · simp only [h1, h2, hiff.mp h2, ↓reduceIte, mul_one, hmass, hone]
    · simp only [h1, h2, mt hiff.mpr h2, ↓reduceIte, mul_zero, lintegral_zero, add_zero]
  · have h2 : t < p + e / (R * rootHeight T) := ht.trans_le (not_lt.mp h1)
    simp only [h1, ht, hiff.mp h2, ↓reduceIte]

theorem spatialProcess_two_heldTerm_lintegral {R : ℝ} (hR : 0 < R) {y : ℝ} (hy : y < 1)
    (c : ℝ) (n : ℕ) :
    ∀ z : SpatialState 2, TwoSampleArray z.2 → 0 < rootHeight z.2 →
      ∫⁻ ω, heldTerm y c n ω ∂(spatialProcess 2 R).pathLaw z =
        if rootHeight z.2 = c ∧ z.1 ≤ y then
          ENNReal.ofReal (heldWeight (twoSampleSelfMass c) (R * c * (y - z.1)) n)
        else 0 := by
  induction n with
  | zero =>
    rintro ⟨p, T⟩ hz hh
    dsimp only at hz hh ⊢
    rw [spatialProcess_pathLaw_lintegral_first_step 2 R _ _ (measurable_heldTerm y c 0)]
    simp only [heldTerm_streamCons_zero]
    have hev : ∀ w : SpatialState 2,
        ∫⁻ ω', (if y < (ω' 0).1 then (1 : ℝ≥0∞) else 0) ∂(spatialProcess 2 R).pathLaw w =
          if y < w.1 then 1 else 0 := fun w =>
      spatialProcess_pathLaw_lintegral_eval_zero 2 R w
        (fun w : SpatialState 2 => if y < w.1 then (1 : ℝ≥0∞) else 0)
        (Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
          measurable_const)
    by_cases hc : rootHeight T = c
    · by_cases hpy : p ≤ y
      · subst hc
        simp only [hpy, ↓reduceIte, one_mul, and_self, hev]
        rw [hz.spatialStep_position_gt_lintegral hR hh hpy hy]
        simp only [heldWeight, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      · simp [hpy]
    · simp [hc]
  | succ n ih =>
    rintro ⟨p, T⟩ hz hh
    dsimp only at hz hh ⊢
    rw [spatialProcess_pathLaw_lintegral_first_step 2 R _ _
      (measurable_heldTerm y c (n + 1))]
    simp only [heldTerm_streamCons_succ]
    by_cases hc : rootHeight T = c
    swap
    · simp [hc]
    subst hc
    simp only [↓reduceIte, one_mul, true_and]
    by_cases hp1 : 1 ≤ p
    · have hstep : ∀ a, SmcPrime.spatialStep 2 R (p, T) a = (1, T) := by
        intro a
        simp only [SmcPrime.spatialStep, hp1, true_or, ↓reduceIte]
      have hpy : ¬ p ≤ y := fun h => absurd (hp1.trans h) (not_le.mpr hy)
      have h1y : ¬ (1 : ℝ) ≤ y := not_le.mpr hy
      simp only [hstep, lintegral_const, measure_univ, mul_one, hpy, ↓reduceIte]
      rw [ih (1, T) hz hh]
      simp only [h1y, and_false, ↓reduceIte]
    · have hp1' : p < 1 := not_le.mp hp1
      have hRh : 0 < R * rootHeight T := mul_pos hR hh
      let Ψ : ℝ × ℝ → ℝ≥0∞ := fun q =>
        if q.2 = rootHeight T ∧ q.1 ≤ y then
          ENNReal.ofReal (heldWeight (twoSampleSelfMass (rootHeight T))
            (R * rootHeight T * (y - q.1)) n)
        else 0
      have hΨ : Measurable Ψ := by
        refine Measurable.ite ?_ ?_ measurable_const
        · exact (measurableSet_eq_fun measurable_snd measurable_const).inter
            (measurableSet_le measurable_fst measurable_const)
        · unfold heldWeight
          exact ENNReal.measurable_ofReal.comp (by fun_prop)
      have hae : ∀ᵐ a ∂proposalNoiseLaw,
          ∫⁻ ω', heldTerm y (rootHeight T) n ω'
            ∂(spatialProcess 2 R).pathLaw (SmcPrime.spatialStep 2 R (p, T) a) =
          Ψ ((SmcPrime.spatialStep 2 R (p, T) a).1,
            rootHeight (SmcPrime.spatialStep 2 R (p, T) a).2) := by
        filter_upwards [hz.spatialStep_good_ae R hh p] with a ha
        exact ih _ ha.1 ha.2
      rw [lintegral_congr_ae hae, hz.spatialStep_lintegral hR hh hp1' Ψ hΨ]
      have hzero : ∀ d : ℝ, ∫⁻ a in Ioi 0,
          ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * Ψ (d, a) = 0 := by
        intro d
        rw [← lintegral_zero (μ := volume.restrict (Ioi (0 : ℝ)))]
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (rootHeight T))] with a ha
        simp only [Ψ, ha, false_and, ↓reduceIte, mul_zero]
      have hpt : ∀ e ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-e)) *
          (if p + e / (R * rootHeight T) < 1 then
            ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
                Ψ (p + e / (R * rootHeight T), rootHeight T) +
              ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
                Ψ (p + e / (R * rootHeight T), a)
          else Ψ (1, rootHeight T)) =
          ENNReal.ofReal (Real.exp (-e)) *
            (ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
              (if e ≤ R * rootHeight T * (y - p) then
                ENNReal.ofReal (heldWeight (twoSampleSelfMass (rootHeight T))
                  (R * rootHeight T * (y - p) - e) n)
              else 0)) := by
        intro e he
        have hiff : p + e / (R * rootHeight T) ≤ y ↔ e ≤ R * rootHeight T * (y - p) := by
          rw [← le_sub_iff_add_le', div_le_iff₀ hRh, mul_comm]
        have harg : R * rootHeight T * (y - (p + e / (R * rootHeight T))) =
            R * rootHeight T * (y - p) - e := by
          field_simp
          ring
        congr 1
        by_cases h1 : p + e / (R * rootHeight T) < 1
        · simp only [h1, ↓reduceIte, hzero, add_zero]
          congr 1
          by_cases h2 : p + e / (R * rootHeight T) ≤ y
          · simp only [Ψ, h2, hiff.mp h2, and_self, ↓reduceIte, harg]
          · simp only [Ψ, h2, mt hiff.mpr h2, and_false, ↓reduceIte]
        · have h2 : ¬ p + e / (R * rootHeight T) ≤ y := fun h =>
            h1 (h.trans_lt hy)
          have h1y : ¬ (1 : ℝ) ≤ y := not_le.mpr hy
          simp only [h1, Ψ, h1y, mt hiff.mpr h2, and_false, ↓reduceIte, mul_zero]
      rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
      by_cases hpy : p ≤ y
      · simp only [hpy, ↓reduceIte]
        exact lintegral_heldWeight_step (twoSampleSelfMass_nonneg hh)
          (mul_nonneg hRh.le (sub_nonneg.mpr hpy)) n
      · simp only [hpy, ↓reduceIte]
        refine Eq.trans (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)
          fun e he => ?_) lintegral_zero
        have hneg : R * rootHeight T * (y - p) < 0 :=
          mul_neg_of_pos_of_neg hRh (sub_neg.mpr (not_le.mp hpy))
        have hle : ¬ e ≤ R * rootHeight T * (y - p) := not_le.mpr (hneg.trans he)
        simp only [hle, ↓reduceIte, mul_zero]

theorem mul_one_sub_twoSampleSelfMass {h : ℝ} (hh : 0 < h) :
    (1 - twoSampleSelfMass h) * h = Analysis.SmcPrime.smcPrimeLambda h := by
  unfold twoSampleSelfMass Analysis.SmcPrime.smcPrimeLambda
  rw [show (-2 * h) = -(2 * h) by ring]
  field_simp
  ring

/-- Source: wilton_carmi_hobolth2015, eq. (7). -/
theorem spatialProcess_two_noChange {R : ℝ} (hR : 0 < R) {y : ℝ} (hy : y < 1) (c : ℝ)
    (z : SpatialState 2) (hz : TwoSampleArray z.2) (hh : 0 < rootHeight z.2) :
    ∑' n, ∫⁻ ω, heldTerm y c n ω ∂(spatialProcess 2 R).pathLaw z =
      if rootHeight z.2 = c ∧ z.1 ≤ y then
        ENNReal.ofReal (Real.exp (-(R * Analysis.SmcPrime.smcPrimeLambda c * (y - z.1))))
      else 0 := by
  simp only [spatialProcess_two_heldTerm_lintegral hR hy c _ z hz hh]
  by_cases hc : rootHeight z.2 = c ∧ z.1 ≤ y
  · simp only [hc, and_self, ↓reduceIte]
    have hcpos : 0 < c := hc.1 ▸ hh
    rw [tsum_heldWeight (twoSampleSelfMass_nonneg hcpos)
      (mul_nonneg (mul_nonneg hR.le hcpos.le) (sub_nonneg.mpr hc.2))]
    congr 3
    rw [← mul_one_sub_twoSampleSelfMass hcpos]
    ring
  · simp only [hc, ↓reduceIte, tsum_zero]

end Rhone.Coalescent.SmcPrime
