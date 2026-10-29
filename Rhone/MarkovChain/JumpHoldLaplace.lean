/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.JumpHold
public import Rhone.MarkovChain.PathProduct
public import Rhone.Analysis.ExpLaplace
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-! # The Laplace transform of the cost of a jump-and-hold path -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace FinChain

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

theorem lintegral_shift_one (x : S) {G : (ℕ → S) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, G (fun k => ω (1 + k)) ∂C.pathLaw x =
      ∑ y, ENNReal.ofReal (C.P x y) * ∫⁻ ω, G ω ∂C.pathLaw y := by
  rw [← lintegral_map hG (DiscreteProcess.measurable_shift 1), C.map_shift_one x,
    Measure.lintegral_bind C.toProcess.traj.measurable.aemeasurable hG.aemeasurable,
    lintegral_fintype]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [kernel_apply_singleton, mul_comm]
  rfl

theorem lintegral_prod_succ (g : S → ℝ≥0∞) (x : S) (n : ℕ) :
    ∫⁻ ω, ∏ k ∈ range (n + 1), g (ω k) ∂C.pathLaw x =
      g x * ∑ y, ENNReal.ofReal (C.P x y) * ∫⁻ ω, ∏ k ∈ range n, g (ω k) ∂C.pathLaw y := by
  have hG : Measurable fun ω : ℕ → S => ∏ k ∈ range n, g (ω k) :=
    Finset.measurable_prod _ fun k _ =>
      (Measurable.of_discrete (f := g)).comp (measurable_pi_apply k)
  have hae : (fun ω : ℕ → S => ∏ k ∈ range (n + 1), g (ω k)) =ᵐ[C.pathLaw x]
      fun ω => g x * ∏ k ∈ range n, g (ω (1 + k)) := by
    filter_upwards [C.ae_eval_zero x] with ω hω
    rw [prod_range_succ', hω, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [add_comm]
  have hG1 : Measurable fun ω : ℕ → S => ∏ k ∈ range n, g (ω (1 + k)) :=
    hG.comp (DiscreteProcess.measurable_shift 1)
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hG1]
  congr 1
  exact C.lintegral_shift_one x hG

end FinChain

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in
noncomputable def discount (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-max 0 (c (p.1 k) * R.holdTime p k)))

omit [DecidableEq S] in
noncomputable def discountUpTo (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) (n : ℕ) : ℝ≥0∞ :=
  ∏ k ∈ range n, R.discount c p k

omit [DecidableEq S] in
noncomputable def laplaceCost (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  ⨅ n, R.discountUpTo c p n

omit [DecidableEq S] in
noncomputable def holdFactor (c : S → ℝ) (y : S) : ℝ := (1 + c y / R.rate y)⁻¹

omit [DecidableEq S] in
theorem discount_le_one (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) :
    R.discount c p k ≤ 1 := by
  rw [discount, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact le_max_left _ _

omit [DecidableEq S] in
theorem discountUpTo_antitone (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) :
    Antitone (R.discountUpTo c p) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [discountUpTo, discountUpTo, prod_range_succ]
  exact mul_le_of_le_one_right' (R.discount_le_one c p n)

omit [DecidableEq S] in
theorem holdFactor_mem {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (y : S) :
    0 ≤ R.holdFactor c y ∧ R.holdFactor c y ≤ 1 := by
  have h0 : 0 ≤ c y / R.rate y := div_nonneg (hc y) (R.rate_nonneg y)
  exact ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

omit [DecidableEq S] in
theorem measurable_discount (c : S → ℝ) (k : ℕ) : Measurable fun p => R.discount c p k := by
  have hω : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  have he : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.2 k :=
    (measurable_pi_apply k).comp measurable_snd
  have hc : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => c (p.1 k) :=
    (Measurable.of_discrete (f := c)).comp hω
  have hr : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => R.rate (p.1 k) :=
    (Measurable.of_discrete (f := R.rate)).comp hω
  have hh : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => R.holdTime p k := he.div hr
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.max (hc.mul hh)).neg)

omit [DecidableEq S] in
theorem measurable_discountUpTo (c : S → ℝ) (n : ℕ) :
    Measurable fun p => R.discountUpTo c p n :=
  Finset.measurable_prod _ fun k _ => R.measurable_discount c k

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem lintegral_clockLaw_discountUpTo {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (ω : ℕ → S) (n : ℕ) :
    ∫⁻ e, R.discountUpTo c (ω, e) n ∂clockLaw =
      ∏ k ∈ range n, ENNReal.ofReal (R.holdFactor c (ω k)) := by
  set F : ℕ → ℝ → ℝ≥0∞ := fun k t =>
    ENNReal.ofReal (Real.exp (-max 0 (c (ω k) * (t / R.rate (ω k))))) with hF
  have hFm : ∀ k, Measurable (F k) := fun k => by
    simp only [hF]
    fun_prop
  have hind : iIndepFun (fun k (e : ℕ → ℝ) => F k (e k)) clockLaw := by
    rw [clockLaw]
    exact iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) hFm
  have hmeas : ∀ k, Measurable fun e : ℕ → ℝ => F k (e k) := fun k =>
    (hFm k).comp (measurable_pi_apply k)
  have hone : ∀ k, ∫⁻ e, F k (e k) ∂clockLaw = ENNReal.ofReal (R.holdFactor c (ω k)) := by
    intro k
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) k
    rw [clockLaw, ← lintegral_map (hFm k) (measurable_pi_apply k), hmap]
    have heq : F k = fun t => ENNReal.ofReal
        (Real.exp (-max 0 (c (ω k) / R.rate (ω k) * t))) := by
      funext t
      simp only [hF]
      congr 4
      ring
    rw [heq, Rhone.Analysis.ExpLaplace.lintegral_exp_neg_expMeasure_one
      (div_nonneg (hc _) (R.rate_nonneg _))]
    rfl
  change ∫⁻ e, ∏ k ∈ range n, F k (e k) ∂clockLaw = _
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (range n) _ hind hmeas]
  exact Finset.prod_congr rfl fun k _ => hone k

theorem lintegral_discountUpTo {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (x : S) (n : ℕ) :
    ∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x =
      ∫⁻ ω, ∏ k ∈ range n, ENNReal.ofReal (R.holdFactor c (ω k)) ∂R.jumpChain.pathLaw x := by
  rw [jumpHoldLaw, lintegral_prod _ (R.measurable_discountUpTo c n).aemeasurable]
  exact lintegral_congr fun ω => R.lintegral_clockLaw_discountUpTo hc ω n

noncomputable def laplace (c : S → ℝ) (x : S) : ℝ :=
  (∫⁻ p, R.laplaceCost c p ∂R.jumpHoldLaw x).toReal

theorem lintegral_discountUpTo_le_one (c : S → ℝ) (x : S) (n : ℕ) :
    ∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x ≤ 1 := by
  calc ∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x ≤ ∫⁻ _, 1 ∂R.jumpHoldLaw x :=
        lintegral_mono fun p => Finset.prod_le_one fun k _ => R.discount_le_one c p k
    _ = 1 := by simp

theorem tendsto_lintegral_discountUpTo (c : S → ℝ) (x : S) :
    Tendsto (fun n => (∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x).toReal) atTop
      (𝓝 (R.laplace c x)) := by
  have hanti : Antitone fun n => ∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x :=
    fun m n hmn => lintegral_mono fun p => R.discountUpTo_antitone c p hmn
  have hinf : ∫⁻ p, R.laplaceCost c p ∂R.jumpHoldLaw x =
      ⨅ n, ∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x := by
    refine lintegral_iInf (fun n => R.measurable_discountUpTo c n)
      (fun m n hmn p => R.discountUpTo_antitone c p hmn) ?_
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (R.lintegral_discountUpTo_le_one c x 0)
  have ht := tendsto_atTop_iInf hanti
  rw [← hinf] at ht
  refine (ENNReal.tendsto_toReal ?_).comp ht
  rw [hinf]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    ((iInf_le _ 0).trans (R.lintegral_discountUpTo_le_one c x 0))

theorem laplace_eq_holdFactor_mul {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (x : S) :
    R.laplace c x = R.holdFactor c x * ∑ y, R.jumpChain.P x y * R.laplace c y := by
  set v : ℕ → S → ℝ≥0∞ := fun n y =>
    ∫⁻ ω, ∏ k ∈ range n, ENNReal.ofReal (R.holdFactor c (ω k)) ∂R.jumpChain.pathLaw y with hv
  have hvle : ∀ n y, v n y ≤ 1 := fun n y => by
    simp only [hv]
    rw [← R.lintegral_discountUpTo hc y n]
    exact R.lintegral_discountUpTo_le_one c y n
  have hvfin : ∀ n y, v n y ≠ ⊤ := fun n y => ne_top_of_le_ne_top ENNReal.one_ne_top (hvle n y)
  have hrec : ∀ n, (v (n + 1) x).toReal =
      R.holdFactor c x * ∑ y, R.jumpChain.P x y * (v n y).toReal := by
    intro n
    have h := R.jumpChain.lintegral_prod_succ (fun y => ENNReal.ofReal (R.holdFactor c y)) x n
    change v (n + 1) x = ENNReal.ofReal (R.holdFactor c x) *
      ∑ y, ENNReal.ofReal (R.jumpChain.P x y) * v n y at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (R.holdFactor_mem hc x).1,
      ENNReal.toReal_sum fun y _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hvfin n y)]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (R.jumpChain.nonneg x y)]
  have hlim : ∀ y, Tendsto (fun n => (v n y).toReal) atTop (𝓝 (R.laplace c y)) := fun y => by
    have h := R.tendsto_lintegral_discountUpTo c y
    simp only [R.lintegral_discountUpTo hc] at h
    exact h
  have h1 : Tendsto (fun n => (v (n + 1) x).toReal) atTop (𝓝 (R.laplace c x)) :=
    (hlim x).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => R.holdFactor c x * ∑ y, R.jumpChain.P x y * (v n y).toReal)
      atTop (𝓝 (R.holdFactor c x * ∑ y, R.jumpChain.P x y * R.laplace c y)) :=
    tendsto_const_nhds.mul (tendsto_finsetSum _ fun y _ => tendsto_const_nhds.mul (hlim y))
  simp only [hrec] at h1
  exact tendsto_nhds_unique h1 h2

theorem laplace_mem (c : S → ℝ) (x : S) : 0 ≤ R.laplace c x ∧ R.laplace c x ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hle : ∫⁻ p, R.laplaceCost c p ∂R.jumpHoldLaw x ≤ 1 :=
    (lintegral_mono fun p => iInf_le _ 0).trans (by simp [discountUpTo])
  have h := ENNReal.toReal_mono ENNReal.one_ne_top hle
  simpa [laplace] using h

theorem mul_laplace_eq_generator {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) {x : S}
    (hx : R.rate x ≠ 0) : c x * R.laplace c x = ∑ y, R.Q x y * R.laplace c y := by
  have h := R.laplace_eq_holdFactor_mul hc x
  rw [jumpChain_P, R.sum_jumpMatrix_mul hx] at h
  have hr : 0 < R.rate x := lt_of_le_of_ne (R.rate_nonneg x) (Ne.symm hx)
  have hcx := hc x
  rw [holdFactor] at h
  have hden : 1 + c x / R.rate x ≠ 0 := by positivity
  field_simp at h
  linear_combination h

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem isClosedSet_jumpChain {Z : Finset S} (h : ∀ x ∈ Z, ∀ y, y ∉ Z → R.Q x y = 0) :
    R.jumpChain.IsClosedSet Z := by
  intro x hx y hy
  have hxy : x ≠ y := fun e => hy (e ▸ hx)
  rw [jumpChain_P]
  unfold jumpMatrix
  split_ifs with h1
  · rfl
  · rw [h x hx y hy, zero_div]

theorem laplace_eq_one_of_isClosedSet {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) {Z : Finset S}
    (hZ : R.jumpChain.IsClosedSet Z) (hc0 : ∀ y ∈ Z, c y = 0) {x : S} (hx : x ∈ Z) :
    R.laplace c x = 1 := by
  set v : ℕ → S → ℝ≥0∞ := fun n y =>
    ∫⁻ ω, ∏ k ∈ range n, ENNReal.ofReal (R.holdFactor c (ω k)) ∂R.jumpChain.pathLaw y with hv
  have hstep : ∀ n, ∀ y ∈ Z, v n y = 1 := by
    intro n
    induction n with
    | zero => intro y _; simp [hv]
    | succ n ih =>
      intro y hy
      have h := R.jumpChain.lintegral_prod_succ (fun z => ENNReal.ofReal (R.holdFactor c z)) y n
      change v (n + 1) y = ENNReal.ofReal (R.holdFactor c y) *
        ∑ z, ENNReal.ofReal (R.jumpChain.P y z) * v n z at h
      have hh : R.holdFactor c y = 1 := by simp [holdFactor, hc0 y hy]
      have hsum : ∑ z, ENNReal.ofReal (R.jumpChain.P y z) * v n z =
          ∑ z, ENNReal.ofReal (R.jumpChain.P y z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hz : z ∈ Z
        · rw [ih z hz, mul_one]
        · rw [hZ y hy z hz, ENNReal.ofReal_zero, zero_mul]
      rw [h, hh, ENNReal.ofReal_one, one_mul, hsum,
        ← ENNReal.ofReal_sum_of_nonneg fun z _ => R.jumpChain.nonneg y z,
        R.jumpChain.row_sum y, ENNReal.ofReal_one]
  have hlim := R.tendsto_lintegral_discountUpTo c x
  have hone : ∀ n, (∫⁻ p, R.discountUpTo c p n ∂R.jumpHoldLaw x).toReal = 1 := fun n => by
    rw [R.lintegral_discountUpTo hc x n]
    change (v n x).toReal = 1
    rw [hstep n x hx, ENNReal.toReal_one]
  simp only [hone] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem eq_holdFactor_mul_of_generator {c u : S → ℝ} {x : S} (hcx : 0 ≤ c x)
    (h : R.rate x ≠ 0 → c x * u x = ∑ y, R.Q x y * u y) :
    u x = R.holdFactor c x * ∑ y, R.jumpChain.P x y * u y := by
  by_cases hx : R.rate x = 0
  · have hP : ∀ y, R.jumpChain.P x y = if x = y then 1 else 0 := fun y => by
      rw [jumpChain_P]
      simp [jumpMatrix, hx]
    simp [holdFactor, hx, hP]
  · rw [jumpChain_P, R.sum_jumpMatrix_mul hx, ← h hx, holdFactor]
    have hr : 0 < R.rate x := lt_of_le_of_ne (R.rate_nonneg x) (Ne.symm hx)
    have hden : 1 + c x / R.rate x ≠ 0 := by positivity
    field_simp

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem eqOn_of_holdFactor_fixed {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) {W : Finset S}
    (hW : R.jumpChain.IsClosedSet W) (hrate : ∀ x ∈ W, c x ≠ 0 → R.rate x ≠ 0) {u v : S → ℝ}
    (hu : ∀ x ∈ W, u x = R.holdFactor c x * ∑ y, R.jumpChain.P x y * u y)
    (hv : ∀ x ∈ W, v x = R.holdFactor c x * ∑ y, R.jumpChain.P x y * v y)
    (h0 : ∀ x ∈ W, c x = 0 → u x = v x) : ∀ x ∈ W, u x = v x := by
  rcases W.eq_empty_or_nonempty with hWe | hWne
  · simp [hWe]
  obtain ⟨x0, hx0, hmax⟩ := W.exists_max_image (fun x => |u x - v x|) hWne
  suffices hM : |u x0 - v x0| = 0 by
    intro x hx
    have h1 : |u x - v x| ≤ 0 := hM ▸ hmax x hx
    have h2 := abs_nonneg (u x - v x)
    have h3 : |u x - v x| = 0 := le_antisymm h1 h2
    exact sub_eq_zero.1 (abs_eq_zero.1 h3)
  by_cases hc0 : c x0 = 0
  · rw [h0 x0 hx0 hc0, sub_self, abs_zero]
  have hr : 0 < R.rate x0 := lt_of_le_of_ne (R.rate_nonneg x0) (Ne.symm (hrate x0 hx0 hc0))
  have hcpos : 0 < c x0 := lt_of_le_of_ne (hc x0) (Ne.symm hc0)
  have hh0 : 0 ≤ R.holdFactor c x0 := (R.holdFactor_mem hc x0).1
  have hh1 : R.holdFactor c x0 < 1 := by
    rw [holdFactor]
    apply inv_lt_one_of_one_lt₀
    have : 0 < c x0 / R.rate x0 := div_pos hcpos hr
    linarith
  have hdiff : u x0 - v x0 =
      R.holdFactor c x0 * ∑ y, R.jumpChain.P x0 y * (u y - v y) := by
    rw [hu x0 hx0, hv x0 hx0, ← mul_sub, ← Finset.sum_sub_distrib]
    simp only [mul_sub]
  have hbound : |∑ y, R.jumpChain.P x0 y * (u y - v y)| ≤ |u x0 - v x0| := by
    calc |∑ y, R.jumpChain.P x0 y * (u y - v y)|
        ≤ ∑ y, |R.jumpChain.P x0 y * (u y - v y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, R.jumpChain.P x0 y * |u x0 - v x0| := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (R.jumpChain.nonneg x0 y)]
          by_cases hy : y ∈ W
          · exact mul_le_mul_of_nonneg_left (hmax y hy) (R.jumpChain.nonneg x0 y)
          · rw [hW x0 hx0 y hy, zero_mul, zero_mul]
      _ = |u x0 - v x0| := by rw [← Finset.sum_mul, R.jumpChain.row_sum, one_mul]
  have hle : |u x0 - v x0| ≤ R.holdFactor c x0 * |u x0 - v x0| := by
    calc |u x0 - v x0| = R.holdFactor c x0 * |∑ y, R.jumpChain.P x0 y * (u y - v y)| := by
          rw [hdiff, abs_mul, abs_of_nonneg hh0]
      _ ≤ R.holdFactor c x0 * |u x0 - v x0| := mul_le_mul_of_nonneg_left hbound hh0
  have hd0 := abs_nonneg (u x0 - v x0)
  by_contra hne
  have hpos : 0 < |u x0 - v x0| := lt_of_le_of_ne hd0 (Ne.symm hne)
  nlinarith

end RateChain

end Rhone.MarkovChain
