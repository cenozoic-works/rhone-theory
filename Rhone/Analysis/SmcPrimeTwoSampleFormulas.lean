/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Real-analysis facts about two explicit functions of a scaled distance `ρ`

Source: wilton_carmi_hobolth2015, eq. (5), (7), (10). -/
@[expose] public section
namespace Rhone.Analysis.SmcPrime
open MeasureTheory Set Filter Topology

/-- Source: wilton_carmi_hobolth2015, eq. (5). -/
noncomputable def argAgreementProb (ρ : ℝ) : ℝ := (ρ + 18) / (ρ ^ 2 + 13 * ρ + 18)

/-- Source: wilton_carmi_hobolth2015, eq. (7). -/
noncomputable def smcPrimeLambda (h : ℝ) : ℝ := (2 * h + 1 - Real.exp (-2 * h)) / 4

/-- Source: wilton_carmi_hobolth2015, eq. (7). -/
noncomputable def smcPrimeAgreementProb (ρ : ℝ) : ℝ :=
  ∫ h in Set.Ioi (0 : ℝ), Real.exp (-h - ρ * smcPrimeLambda h)

theorem smcPrimeAgreementProb_eq_integral (ρ : ℝ) :
    smcPrimeAgreementProb ρ =
      ∫ h in Set.Ioi (0 : ℝ), Real.exp (-h - ρ * ((2 * h + 1 - Real.exp (-2 * h)) / 4)) :=
  rfl

theorem half_le_smcPrimeLambda {h : ℝ} (hh : 0 ≤ h) : h / 2 ≤ smcPrimeLambda h := by
  have : Real.exp (-2 * h) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold smcPrimeLambda
  linarith

theorem smcPrimeLambda_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ smcPrimeLambda h :=
  le_trans (by linarith) (half_le_smcPrimeLambda hh)

theorem smcPrimeLambda_le (h : ℝ) : smcPrimeLambda h ≤ h := by
  have := Real.add_one_le_exp (-2 * h)
  unfold smcPrimeLambda
  linarith

theorem integral_pow_mul_exp_neg_pow_Ioi (i m : ℕ) (hm : 0 < m) :
    IntegrableOn (fun h : ℝ => h ^ i * Real.exp (-h) ^ m) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), h ^ i * Real.exp (-h) ^ m =
        (i.factorial : ℝ) / (m : ℝ) ^ (i + 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (i : ℝ) + 1) (r := m)
    (by positivity) hm'
  have hfun : ∀ h ∈ Ioi (0 : ℝ),
      h ^ ((i : ℝ) + 1 - 1) * Real.exp (-((m : ℝ) * h)) = h ^ i * Real.exp (-h) ^ m := by
    intro h _
    rw [add_sub_cancel_right, Real.rpow_natCast, ← Real.exp_nat_mul]
    congr 2
    ring
  have hval : (1 / (m : ℝ)) ^ ((i : ℝ) + 1) * Real.Gamma ((i : ℝ) + 1) =
      (i.factorial : ℝ) / (m : ℝ) ^ (i + 1) := by
    rw [Real.Gamma_nat_eq_factorial, show (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, one_div, inv_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, hval] at key
  refine ⟨?_, key⟩
  refine Integrable.of_integral_ne_zero ?_
  rw [key]
  positivity

theorem integrableOn_Ioi_and_integral_add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntegrableOn f (Ioi 0) ∧ ∫ h in Ioi (0 : ℝ), f h = a)
    (hg : IntegrableOn g (Ioi 0) ∧ ∫ h in Ioi (0 : ℝ), g h = b) :
    IntegrableOn (fun h => f h + g h) (Ioi 0) ∧ ∫ h in Ioi (0 : ℝ), (f h + g h) = a + b :=
  ⟨Integrable.add hf.1 hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2]⟩

theorem integrableOn_Ioi_and_integral_const_mul {f : ℝ → ℝ} {a : ℝ} (c : ℝ)
    (hf : IntegrableOn f (Ioi 0) ∧ ∫ h in Ioi (0 : ℝ), f h = a) :
    IntegrableOn (fun h => c * f h) (Ioi 0) ∧ ∫ h in Ioi (0 : ℝ), c * f h = c * a :=
  ⟨Integrable.const_mul hf.1 c, by rw [integral_const_mul, hf.2]⟩

noncomputable def smcPrimeMomentCoeff (k m i : ℕ) : ℝ :=
  (1 / 4) ^ k * (-1) ^ (k - m) * (k.choose m) * 2 ^ i * (m.choose i)

theorem smcPrimeLambda_pow_mul_exp (k : ℕ) (h : ℝ) :
    smcPrimeLambda h ^ k * Real.exp (-h) =
      ∑ m ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (m + 1),
        smcPrimeMomentCoeff k m i * (h ^ i * Real.exp (-h) ^ (2 * (k - m) + 1)) := by
  have hE : Real.exp (-2 * h) = Real.exp (-h) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold smcPrimeLambda
  rw [hE, show (2 * h + 1 - Real.exp (-h) ^ 2) / 4 =
    (1 / 4) * ((2 * h + 1) + -(Real.exp (-h) ^ 2)) by ring, mul_pow, add_pow, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [add_pow]
  simp only [Finset.sum_mul, Finset.mul_sum, one_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold smcPrimeMomentCoeff
  ring

theorem smcPrimeLambda_moment (k : ℕ) :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ k * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ k * Real.exp (-h) =
        ∑ m ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (m + 1),
          smcPrimeMomentCoeff k m i *
            ((i.factorial : ℝ) / ((2 * (k - m) + 1 : ℕ) : ℝ) ^ (i + 1)) := by
  have hterm : ∀ m i : ℕ, IntegrableOn (fun h : ℝ =>
      smcPrimeMomentCoeff k m i * (h ^ i * Real.exp (-h) ^ (2 * (k - m) + 1))) (Ioi 0) :=
    fun m i => Integrable.const_mul
      (integral_pow_mul_exp_neg_pow_Ioi i _ (Nat.succ_pos _)).1 _
  simp_rw [smcPrimeLambda_pow_mul_exp]
  refine ⟨integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun i _ => hterm m i, ?_⟩
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun i _ => hterm m i]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun i _ => hterm m i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, (integral_pow_mul_exp_neg_pow_Ioi i _ (Nat.succ_pos _)).2]

theorem smcPrimeLambda_moment_one :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ 1 * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ 1 * Real.exp (-h) = 2 / 3 := by
  refine ⟨(smcPrimeLambda_moment 1).1, ?_⟩
  rw [(smcPrimeLambda_moment 1).2]
  norm_num [Finset.sum_range_succ, smcPrimeMomentCoeff, Nat.choose, Nat.factorial]

theorem smcPrimeLambda_moment_zero :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ 0 * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ 0 * Real.exp (-h) = 1 := by
  refine ⟨(smcPrimeLambda_moment 0).1, ?_⟩
  rw [(smcPrimeLambda_moment 0).2]
  norm_num [Finset.sum_range_succ, smcPrimeMomentCoeff, Nat.choose, Nat.factorial]

theorem smcPrimeLambda_moment_two :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ 2 * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ 2 * Real.exp (-h) = 34 / 45 := by
  refine ⟨(smcPrimeLambda_moment 2).1, ?_⟩
  rw [(smcPrimeLambda_moment 2).2]
  norm_num [Finset.sum_range_succ, smcPrimeMomentCoeff, Nat.choose, Nat.factorial]

theorem smcPrimeLambda_moment_three :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ 3 * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ 3 * Real.exp (-h) = 1882 / 1575 := by
  refine ⟨(smcPrimeLambda_moment 3).1, ?_⟩
  rw [(smcPrimeLambda_moment 3).2]
  norm_num [Finset.sum_range_succ, smcPrimeMomentCoeff, Nat.choose, Nat.factorial]

theorem smcPrimeLambda_moment_four :
    IntegrableOn (fun h : ℝ => smcPrimeLambda h ^ 4 * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ), smcPrimeLambda h ^ 4 * Real.exp (-h) = 403744 / 165375 := by
  refine ⟨(smcPrimeLambda_moment 4).1, ?_⟩
  rw [(smcPrimeLambda_moment 4).2]
  norm_num [Finset.sum_range_succ, smcPrimeMomentCoeff, Nat.choose, Nat.factorial]

theorem integral_smcPrimeLambda_poly_mul_exp (a0 a1 a2 a3 a4 : ℝ) :
    IntegrableOn (fun h : ℝ =>
        (a0 + a1 * smcPrimeLambda h + a2 * smcPrimeLambda h ^ 2 + a3 * smcPrimeLambda h ^ 3 +
          a4 * smcPrimeLambda h ^ 4) * Real.exp (-h)) (Ioi 0) ∧
      ∫ h in Ioi (0 : ℝ),
        (a0 + a1 * smcPrimeLambda h + a2 * smcPrimeLambda h ^ 2 + a3 * smcPrimeLambda h ^ 3 +
          a4 * smcPrimeLambda h ^ 4) * Real.exp (-h) =
        a0 + a1 * (2 / 3) + a2 * (34 / 45) + a3 * (1882 / 1575) +
          a4 * (403744 / 165375) := by
  have key := integrableOn_Ioi_and_integral_add (integrableOn_Ioi_and_integral_add
    (integrableOn_Ioi_and_integral_add (integrableOn_Ioi_and_integral_add
      (integrableOn_Ioi_and_integral_const_mul a0 smcPrimeLambda_moment_zero)
      (integrableOn_Ioi_and_integral_const_mul a1 smcPrimeLambda_moment_one))
      (integrableOn_Ioi_and_integral_const_mul a2 smcPrimeLambda_moment_two))
      (integrableOn_Ioi_and_integral_const_mul a3 smcPrimeLambda_moment_three))
      (integrableOn_Ioi_and_integral_const_mul a4 smcPrimeLambda_moment_four)
  have hfun : (fun h : ℝ =>
      (a0 + a1 * smcPrimeLambda h + a2 * smcPrimeLambda h ^ 2 + a3 * smcPrimeLambda h ^ 3 +
        a4 * smcPrimeLambda h ^ 4) * Real.exp (-h)) =
      fun h : ℝ => a0 * (smcPrimeLambda h ^ 0 * Real.exp (-h)) +
        a1 * (smcPrimeLambda h ^ 1 * Real.exp (-h)) +
        a2 * (smcPrimeLambda h ^ 2 * Real.exp (-h)) +
        a3 * (smcPrimeLambda h ^ 3 * Real.exp (-h)) +
        a4 * (smcPrimeLambda h ^ 4 * Real.exp (-h)) := by
    funext h
    ring
  rw [hfun]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  ring

theorem nonneg_of_hasDerivAt_nonneg {f g : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, 0 ≤ t → 0 ≤ g t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hd t).deriv]
        exact hg t (interior_subset ht))
  intro t ht
  have := hmono self_mem_Ici ht ht
  rwa [h0] at this

theorem hasDerivAt_exp_neg (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
  have := (hasDerivAt_neg t).exp
  simpa using this

theorem exp_neg_le_order_two {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2 - Real.exp (-t))
      (Real.exp (-t) - (1 - t)) t := by
    intro t
    have h := ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
      ((hasDerivAt_pow 2 t).div_const 2)).sub (hasDerivAt_exp_neg t))
    refine h.congr_deriv ?_
    simp
    ring
  have := nonneg_of_hasDerivAt_nonneg (by simp) hd
    (fun t _ => by have := Real.add_one_le_exp (-t); linarith) t ht
  linarith

theorem order_three_le_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    1 - t + t ^ 2 / 2 - t ^ 3 / 6 ≤ Real.exp (-t) := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6))
      (1 - t + t ^ 2 / 2 - Real.exp (-t)) t := by
    intro t
    have h := (hasDerivAt_exp_neg t).sub
      ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6))
    refine h.congr_deriv ?_
    simp
    ring
  have := nonneg_of_hasDerivAt_nonneg (by simp) hd
    (fun t ht => by have := exp_neg_le_order_two ht; linarith) t ht
  linarith

theorem exp_neg_le_order_four {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 := by
  have hd : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => 1 - t + t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 24 - Real.exp (-t))
      (Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)) t := by
    intro t
    have h := (((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (hasDerivAt_exp_neg t)
    refine h.congr_deriv ?_
    simp
    ring
  have := nonneg_of_hasDerivAt_nonneg (by simp) hd
    (fun t ht => by have := order_three_le_exp_neg ht; linarith) t ht
  linarith

theorem argAgreementProb_denominator_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < ρ ^ 2 + 13 * ρ + 18 := by
  positivity

theorem argAgreementProb_zero : argAgreementProb 0 = 1 := by
  norm_num [argAgreementProb]

theorem argAgreementProb_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < argAgreementProb ρ :=
  div_pos (by linarith) (argAgreementProb_denominator_pos hρ)

theorem argAgreementProb_le_two_div {ρ : ℝ} (hρ : 0 ≤ ρ) :
    argAgreementProb ρ ≤ 2 / (2 + ρ) := by
  unfold argAgreementProb
  rw [div_le_div_iff₀ (argAgreementProb_denominator_pos hρ) (by linarith)]
  nlinarith [mul_nonneg hρ hρ]

theorem argAgreementProb_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) : argAgreementProb ρ ≤ 1 := by
  unfold argAgreementProb
  rw [div_le_one (argAgreementProb_denominator_pos hρ)]
  nlinarith [mul_nonneg hρ hρ]

theorem argAgreementProb_antitoneOn : AntitoneOn argAgreementProb (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  unfold argAgreementProb
  rw [div_le_div_iff₀ (argAgreementProb_denominator_pos hb')
    (argAgreementProb_denominator_pos ha')]
  have key : (a + 18) * (b ^ 2 + 13 * b + 18) - (b + 18) * (a ^ 2 + 13 * a + 18) =
      (b - a) * (a * b + 18 * (a + b) + 216) := by ring
  have : 0 ≤ (b - a) * (a * b + 18 * (a + b) + 216) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

theorem tendsto_two_div_two_add_atTop :
    Tendsto (fun ρ : ℝ => 2 / (2 + ρ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)

theorem argAgreementProb_tendsto_atTop : Tendsto argAgreementProb atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_two_div_two_add_atTop ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ using (argAgreementProb_pos hρ).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ using argAgreementProb_le_two_div hρ

theorem argAgreementProb_le_order_two {ρ : ℝ} (hρ : 0 ≤ ρ) :
    argAgreementProb ρ ≤ 1 - 2 / 3 * ρ + 23 / 54 * ρ ^ 2 := by
  unfold argAgreementProb
  rw [div_le_iff₀ (argAgreementProb_denominator_pos hρ)]
  nlinarith [pow_nonneg hρ 3, pow_nonneg hρ 4]

theorem order_three_le_argAgreementProb {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 - 2 / 3 * ρ + 23 / 54 * ρ ^ 2 - 263 / 972 * ρ ^ 3 ≤ argAgreementProb ρ := by
  unfold argAgreementProb
  rw [le_div_iff₀ (argAgreementProb_denominator_pos hρ)]
  nlinarith [pow_nonneg hρ 4, pow_nonneg hρ 5]

theorem order_one_le_argAgreementProb {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 - 2 / 3 * ρ ≤ argAgreementProb ρ := by
  unfold argAgreementProb
  rw [le_div_iff₀ (argAgreementProb_denominator_pos hρ)]
  nlinarith [pow_nonneg hρ 2, pow_nonneg hρ 3]

theorem smcPrimeAgreementIntegrand_integrableOn {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IntegrableOn (fun h : ℝ => Real.exp (-h - ρ * smcPrimeLambda h)) (Ioi 0) := by
  have hdom : IntegrableOn (fun h : ℝ => Real.exp (-h)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  refine Integrable.mono' hdom ?_ ?_
  · exact Continuous.aestronglyMeasurable (by unfold smcPrimeLambda; fun_prop)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun h hh => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    have := mul_nonneg hρ (smcPrimeLambda_nonneg (le_of_lt hh))
    exact Real.exp_le_exp.2 (by linarith)

theorem smcPrimeAgreementProb_zero : smcPrimeAgreementProb 0 = 1 := by
  unfold smcPrimeAgreementProb
  simp only [zero_mul, sub_zero]
  exact integral_exp_neg_Ioi_zero

theorem integral_exp_neg_mul_Ioi_zero {a : ℝ} (ha : 0 < a) :
    ∫ h in Ioi (0 : ℝ), Real.exp (-a * h) = 1 / a := by
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp [neg_div_neg_eq]

theorem smcPrimeAgreementProb_le_two_div {ρ : ℝ} (hρ : 0 ≤ ρ) :
    smcPrimeAgreementProb ρ ≤ 2 / (2 + ρ) := by
  have ha : 0 < 1 + ρ / 2 := by linarith
  have hle : smcPrimeAgreementProb ρ ≤ ∫ h in Ioi (0 : ℝ), Real.exp (-(1 + ρ / 2) * h) := by
    refine setIntegral_mono_on (smcPrimeAgreementIntegrand_integrableOn hρ)
      (exp_neg_integrableOn_Ioi 0 ha) measurableSet_Ioi fun h hh => ?_
    have := mul_le_mul_of_nonneg_left (half_le_smcPrimeLambda (le_of_lt hh)) hρ
    exact Real.exp_le_exp.2 (by linarith)
  rw [integral_exp_neg_mul_Ioi_zero ha] at hle
  have : 1 / (1 + ρ / 2) = 2 / (2 + ρ) := by
    field_simp
  rwa [this] at hle

theorem one_div_one_add_le_smcPrimeAgreementProb {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 / (1 + ρ) ≤ smcPrimeAgreementProb ρ := by
  have ha : 0 < 1 + ρ := by linarith
  have hle : ∫ h in Ioi (0 : ℝ), Real.exp (-(1 + ρ) * h) ≤ smcPrimeAgreementProb ρ := by
    refine setIntegral_mono_on (exp_neg_integrableOn_Ioi 0 ha)
      (smcPrimeAgreementIntegrand_integrableOn hρ) measurableSet_Ioi fun h hh => ?_
    have := mul_le_mul_of_nonneg_left (smcPrimeLambda_le h) hρ
    exact Real.exp_le_exp.2 (by linarith)
  rwa [integral_exp_neg_mul_Ioi_zero ha] at hle

theorem smcPrimeAgreementProb_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < smcPrimeAgreementProb ρ :=
  lt_of_lt_of_le (by positivity) (one_div_one_add_le_smcPrimeAgreementProb hρ)

theorem smcPrimeAgreementProb_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) : smcPrimeAgreementProb ρ ≤ 1 := by
  refine (smcPrimeAgreementProb_le_two_div hρ).trans ?_
  rw [div_le_one (by linarith)]
  linarith

theorem smcPrimeAgreementProb_antitoneOn : AntitoneOn smcPrimeAgreementProb (Ici 0) := by
  intro a ha b hb hab
  refine setIntegral_mono_on (smcPrimeAgreementIntegrand_integrableOn hb)
    (smcPrimeAgreementIntegrand_integrableOn ha) measurableSet_Ioi fun h hh => ?_
  have := mul_le_mul_of_nonneg_right hab (smcPrimeLambda_nonneg (le_of_lt hh))
  exact Real.exp_le_exp.2 (by linarith)

theorem smcPrimeAgreementProb_tendsto_atTop : Tendsto smcPrimeAgreementProb atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_two_div_two_add_atTop ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ using
      (smcPrimeAgreementProb_pos hρ).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ using
      smcPrimeAgreementProb_le_two_div hρ

theorem exp_neg_sub_eq_mul (h t : ℝ) : Real.exp (-h - t) = Real.exp (-t) * Real.exp (-h) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem order_one_le_smcPrimeAgreementProb {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 - 2 / 3 * ρ ≤ smcPrimeAgreementProb ρ := by
  have hp := integral_smcPrimeLambda_poly_mul_exp 1 (-ρ) 0 0 0
  have hle := setIntegral_mono_on hp.1 (smcPrimeAgreementIntegrand_integrableOn hρ)
    measurableSet_Ioi fun h _ => by
      rw [exp_neg_sub_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have := Real.add_one_le_exp (-(ρ * smcPrimeLambda h))
      linarith
  rw [hp.2] at hle
  unfold smcPrimeAgreementProb
  linarith

theorem smcPrimeAgreementProb_le_order_two {ρ : ℝ} (hρ : 0 ≤ ρ) :
    smcPrimeAgreementProb ρ ≤ 1 - 2 / 3 * ρ + 17 / 45 * ρ ^ 2 := by
  have hp := integral_smcPrimeLambda_poly_mul_exp 1 (-ρ) (ρ ^ 2 / 2) 0 0
  have hle := setIntegral_mono_on (smcPrimeAgreementIntegrand_integrableOn hρ) hp.1
    measurableSet_Ioi fun h hh => by
      rw [exp_neg_sub_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have := exp_neg_le_order_two (mul_nonneg hρ (smcPrimeLambda_nonneg (le_of_lt hh)))
      linarith
  rw [hp.2] at hle
  unfold smcPrimeAgreementProb
  linarith

theorem order_three_le_smcPrimeAgreementProb {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 - 2 / 3 * ρ + 17 / 45 * ρ ^ 2 - 941 / 4725 * ρ ^ 3 ≤ smcPrimeAgreementProb ρ := by
  have hp := integral_smcPrimeLambda_poly_mul_exp 1 (-ρ) (ρ ^ 2 / 2) (-(ρ ^ 3 / 6)) 0
  have hle := setIntegral_mono_on hp.1 (smcPrimeAgreementIntegrand_integrableOn hρ)
    measurableSet_Ioi fun h hh => by
      rw [exp_neg_sub_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have := order_three_le_exp_neg (mul_nonneg hρ (smcPrimeLambda_nonneg (le_of_lt hh)))
      linarith
  rw [hp.2] at hle
  unfold smcPrimeAgreementProb
  linarith

theorem smcPrimeAgreementProb_le_order_four {ρ : ℝ} (hρ : 0 ≤ ρ) :
    smcPrimeAgreementProb ρ ≤
      1 - 2 / 3 * ρ + 17 / 45 * ρ ^ 2 - 941 / 4725 * ρ ^ 3 + 50468 / 496125 * ρ ^ 4 := by
  have hp := integral_smcPrimeLambda_poly_mul_exp 1 (-ρ) (ρ ^ 2 / 2) (-(ρ ^ 3 / 6))
    (ρ ^ 4 / 24)
  have hle := setIntegral_mono_on (smcPrimeAgreementIntegrand_integrableOn hρ) hp.1
    measurableSet_Ioi fun h hh => by
      rw [exp_neg_sub_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have := exp_neg_le_order_four (mul_nonneg hρ (smcPrimeLambda_nonneg (le_of_lt hh)))
      linarith
  rw [hp.2] at hle
  unfold smcPrimeAgreementProb
  linarith

theorem hasDerivWithinAt_Ici_zero_of_quadratic_bound {f : ℝ → ℝ} {c C : ℝ}
    (hb : ∀ ρ, 0 ≤ ρ → |f ρ - (1 + c * ρ)| ≤ C * ρ ^ 2) :
    HasDerivWithinAt f c (Ici 0) 0 := by
  have h0 : f 0 = 1 := by
    have := hb 0 le_rfl
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith [abs_eq_zero.1 (le_antisymm this (abs_nonneg _))]
  rw [hasDerivWithinAt_iff_isLittleO]
  have hO : (fun ρ : ℝ => f ρ - f 0 - (ρ - 0) • c) =O[𝓝[Ici 0] 0] fun ρ : ℝ => ρ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    have := hb ρ hρ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), h0]
    have he : f ρ - 1 - (ρ - 0) • c = f ρ - (1 + c * ρ) := by
      rw [smul_eq_mul]
      ring
    rw [he]
    exact this
  have ho : (fun ρ : ℝ => ρ ^ 2) =o[𝓝[Ici 0] 0] fun ρ : ℝ => ρ - 0 := by
    simpa using (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) one_lt_two).mono nhdsWithin_le_nhds
  exact hO.trans_isLittleO ho

theorem argAgreementProb_hasDerivAt_zero : HasDerivAt argAgreementProb (-2 / 3) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).add_const 18).div
    (((hasDerivAt_pow 2 (0 : ℝ)).add ((hasDerivAt_id (0 : ℝ)).const_mul 13)).add_const 18)
    (by norm_num)
  refine (h.congr_deriv ?_)
  norm_num

theorem smcPrimeAgreementProb_hasDerivWithinAt_zero :
    HasDerivWithinAt smcPrimeAgreementProb (-2 / 3) (Ici 0) 0 := by
  refine hasDerivWithinAt_Ici_zero_of_quadratic_bound (C := 17 / 45) fun ρ hρ => ?_
  have h1 := order_one_le_smcPrimeAgreementProb hρ
  have h2 := smcPrimeAgreementProb_le_order_two hρ
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ρ]

theorem argAgreementProb_first_order :
    (fun ρ : ℝ => argAgreementProb ρ - (1 - 2 / 3 * ρ))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun ρ : ℝ => ρ ^ 2) := by
  refine Asymptotics.IsBigO.of_bound (23 / 54) ?_
  filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
  have hρ' : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have h1 := order_one_le_argAgreementProb hρ'
  have h2 := argAgreementProb_le_order_two hρ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), abs_le]
  constructor <;> nlinarith [sq_nonneg ρ]

theorem smcPrimeAgreementProb_first_order :
    (fun ρ : ℝ => smcPrimeAgreementProb ρ - (1 - 2 / 3 * ρ))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun ρ : ℝ => ρ ^ 2) := by
  refine Asymptotics.IsBigO.of_bound (17 / 45) ?_
  filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
  have hρ' : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have h1 := order_one_le_smcPrimeAgreementProb hρ'
  have h2 := smcPrimeAgreementProb_le_order_two hρ'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ), abs_le]
  constructor <;> nlinarith [sq_nonneg ρ]

theorem argAgreementProb_sub_smcPrimeAgreementProb_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2 ≤ 941 / 4725 * ρ ^ 3 := by
  have h1 := argAgreementProb_le_order_two hρ
  have h2 := order_three_le_smcPrimeAgreementProb hρ
  linarith

theorem le_argAgreementProb_sub_smcPrimeAgreementProb_sub {ρ : ℝ} (hρ : 0 ≤ ρ) :
    -(12149 / 170100 * ρ ^ 3) - 50468 / 496125 * ρ ^ 4 ≤
      argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2 := by
  have h1 := order_three_le_argAgreementProb hρ
  have h2 := smcPrimeAgreementProb_le_order_four hρ
  linarith

theorem abs_argAgreementProb_sub_smcPrimeAgreementProb_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    |argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2| ≤
      263 / 972 * ρ ^ 3 := by
  have h1 := order_three_le_argAgreementProb hρ
  have h2 := smcPrimeAgreementProb_le_order_two hρ
  have h3 := argAgreementProb_sub_smcPrimeAgreementProb_sub_le hρ
  have h4 := pow_nonneg hρ 3
  rw [abs_le]
  constructor <;> linarith

theorem abs_argAgreementProb_sub_smcPrimeAgreementProb_sub_le_of_le_one {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    |argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2| ≤
      941 / 4725 * ρ ^ 3 := by
  have h1 := le_argAgreementProb_sub_smcPrimeAgreementProb_sub hρ
  have h3 := argAgreementProb_sub_smcPrimeAgreementProb_sub_le hρ
  have h4 : ρ ^ 4 ≤ ρ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hρ1 (pow_nonneg hρ 3)
    nlinarith
  have h5 := pow_nonneg hρ 3
  rw [abs_le]
  constructor <;> linarith

theorem argAgreementProb_sub_smcPrimeAgreementProb_isLittleO :
    (fun ρ : ℝ => argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2)
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun ρ : ℝ => ρ ^ 2) := by
  have hO : (fun ρ : ℝ => argAgreementProb ρ - smcPrimeAgreementProb ρ - 13 / 270 * ρ ^ 2)
      =O[𝓝[Ioi 0] 0] fun ρ : ℝ => ρ ^ 3 := by
    refine Asymptotics.IsBigO.of_bound (263 / 972) ?_
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    have hρ' : (0 : ℝ) ≤ ρ := le_of_lt hρ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ' 3)]
    exact abs_argAgreementProb_sub_smcPrimeAgreementProb_sub_le hρ'
  exact hO.trans_isLittleO
    ((Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by norm_num : 2 < 3)).mono nhdsWithin_le_nhds)

theorem argAgreementProb_sub_smcPrimeAgreementProb_pos {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 2 / 5) : 0 < argAgreementProb ρ - smcPrimeAgreementProb ρ := by
  have h1 := le_argAgreementProb_sub_smcPrimeAgreementProb_sub hρ.le
  have h2 : 0 < ρ ^ 2 * (13 / 270 - 12149 / 170100 * ρ - 50468 / 496125 * ρ ^ 2) := by
    refine mul_pos (by positivity) ?_
    nlinarith
  nlinarith

theorem argAgreementProb_sub_smcPrimeAgreementProb_ge {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1 / 6) :
    ρ ^ 2 / 30 ≤ argAgreementProb ρ - smcPrimeAgreementProb ρ := by
  have h1 := le_argAgreementProb_sub_smcPrimeAgreementProb_sub hρ
  have h2 : 0 ≤ ρ ^ 2 * (2 / 135 - 12149 / 170100 * ρ - 50468 / 496125 * ρ ^ 2) := by
    refine mul_nonneg (by positivity) ?_
    nlinarith
  nlinarith

end Rhone.Analysis.SmcPrime
