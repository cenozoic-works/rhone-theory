/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.SfsNonIdentifiability

/-!
# Monotone change of variable between coalescent time and real time

Source: myers_fefferman_patterson2008, secs. 3–5. -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory Set Filter Coalescent Rhone.Combinatorics MarkovChain Topology
open scoped NNReal

noncomputable def coalToReal (η : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, η s

noncomputable def coalToRealInv (η : ℝ → ℝ) : ℝ → ℝ := Function.invFun (coalToReal η)

noncomputable def sizeOfCoalTime (η : ℝ → ℝ) (t : ℝ) : ℝ := η (coalToRealInv η t)

section Bounds

variable {η : ℝ → ℝ} {c M : ℝ}

theorem hasDerivAt_coalToReal (hη : Continuous η) (τ : ℝ) :
    HasDerivAt (coalToReal η) (η τ) τ :=
  (hη.integral_hasStrictDerivAt 0 τ).hasDerivAt

theorem continuous_coalToReal (hη : Continuous η) : Continuous (coalToReal η) :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_coalToReal hη τ).continuousAt

theorem coalToReal_zero (η : ℝ → ℝ) : coalToReal η 0 = 0 := intervalIntegral.integral_same

theorem strictMono_coalToReal (hη : Continuous η) (hpos : ∀ τ, 0 < η τ) :
    StrictMono (coalToReal η) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_coalToReal hη) hpos

theorem mul_le_coalToReal (hη : Continuous η) (hlow : ∀ τ, c ≤ η τ) {τ : ℝ} (hτ : 0 ≤ τ) :
    c * τ ≤ coalToReal η τ := by
  have h := intervalIntegral.integral_mono_on hτ (intervalIntegrable_const (μ := volume) (c := c))
    (hη.intervalIntegrable 0 τ) fun x _ => hlow x
  simpa [coalToReal, mul_comm] using h

theorem coalToReal_le_mul (hη : Continuous η) (hup : ∀ τ, η τ ≤ M) {τ : ℝ} (hτ : 0 ≤ τ) :
    coalToReal η τ ≤ M * τ := by
  have h := intervalIntegral.integral_mono_on hτ (hη.intervalIntegrable 0 τ)
    (intervalIntegrable_const (μ := volume) (c := M)) fun x _ => hup x
  simpa [coalToReal, mul_comm] using h

theorem coalToReal_le_mul_of_nonpos (hη : Continuous η) (hlow : ∀ τ, c ≤ η τ) {τ : ℝ}
    (hτ : τ ≤ 0) : coalToReal η τ ≤ c * τ := by
  have h := intervalIntegral.integral_mono_on hτ (intervalIntegrable_const (μ := volume) (c := c))
    (hη.intervalIntegrable τ 0) fun x _ => hlow x
  have e : coalToReal η τ = -∫ s in τ..0, η s := by
    rw [coalToReal, intervalIntegral.integral_symm]
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [e]
  nlinarith

theorem surjective_coalToReal (hη : Continuous η) (hc : 0 < c) (hlow : ∀ τ, c ≤ η τ) :
    Function.Surjective (coalToReal η) := by
  refine (continuous_coalToReal hη).surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hc)
    filter_upwards [eventually_ge_atTop 0] with τ hτ
    exact mul_le_coalToReal hη hlow hτ
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hc)
    filter_upwards [eventually_le_atBot 0] with τ hτ
    exact coalToReal_le_mul_of_nonpos hη hlow hτ

variable (hη : Continuous η) (hc : 0 < c) (hlow : ∀ τ, c ≤ η τ)
include hη hc hlow

theorem coalToReal_coalToRealInv (t : ℝ) : coalToReal η (coalToRealInv η t) = t :=
  Function.rightInverse_invFun (surjective_coalToReal hη hc hlow) t

theorem coalToRealInv_coalToReal (τ : ℝ) : coalToRealInv η (coalToReal η τ) = τ :=
  Function.leftInverse_invFun
    (strictMono_coalToReal hη fun x => lt_of_lt_of_le hc (hlow x)).injective τ

theorem coalToRealInv_zero : coalToRealInv η 0 = 0 := by
  have h := coalToRealInv_coalToReal hη hc hlow 0
  rwa [coalToReal_zero] at h

theorem strictMono_coalToRealInv : StrictMono (coalToRealInv η) := by
  intro s t hst
  have hm := strictMono_coalToReal hη fun x => lt_of_lt_of_le hc (hlow x)
  rw [← coalToReal_coalToRealInv hη hc hlow s, ← coalToReal_coalToRealInv hη hc hlow t] at hst
  exact hm.lt_iff_lt.1 hst

theorem continuous_coalToRealInv : Continuous (coalToRealInv η) :=
  (strictMono_coalToRealInv hη hc hlow).monotone.continuous_of_surjective
    fun τ => ⟨coalToReal η τ, coalToRealInv_coalToReal hη hc hlow τ⟩

theorem hasDerivAt_coalToRealInv (t : ℝ) :
    HasDerivAt (coalToRealInv η) (η (coalToRealInv η t))⁻¹ t :=
  HasDerivAt.of_local_left_inverse (continuous_coalToRealInv hη hc hlow).continuousAt
    (hasDerivAt_coalToReal hη _) (lt_of_lt_of_le hc (hlow _)).ne'
    (Eventually.of_forall fun y => coalToReal_coalToRealInv hη hc hlow y)

theorem cumIntensity_sizeOfCoalTime (t : ℝ) :
    cumIntensity (sizeOfCoalTime η) t = coalToRealInv η t := by
  have hcont : Continuous fun s => (η (coalToRealInv η s))⁻¹ :=
    (hη.comp (continuous_coalToRealInv hη hc hlow)).inv₀ fun s =>
      (lt_of_lt_of_le hc (hlow _)).ne'
  rw [cumIntensity]
  change ∫ s in (0 : ℝ)..t, (η (coalToRealInv η s))⁻¹ = coalToRealInv η t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_coalToRealInv hη hc hlow s) (hcont.intervalIntegrable 0 t),
    coalToRealInv_zero hη hc hlow, sub_zero]

theorem continuous_sizeOfCoalTime : Continuous (sizeOfCoalTime η) :=
  hη.comp (continuous_coalToRealInv hη hc hlow)

theorem div_le_coalToRealInv (hup : ∀ τ, η τ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    t / M ≤ coalToRealInv η t := by
  have hM : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hc (hlow 0)) (hup 0)
  have hm := strictMono_coalToReal hη fun x => lt_of_lt_of_le hc (hlow x)
  rw [← hm.le_iff_le, coalToReal_coalToRealInv hη hc hlow]
  calc coalToReal η (t / M) ≤ M * (t / M) := coalToReal_le_mul hη hup (div_nonneg ht hM.le)
    _ = t := by field_simp

theorem isSizeFunction_sizeOfCoalTime (hup : ∀ τ, η τ ≤ M) :
    IsSizeFunction (sizeOfCoalTime η) where
  pos t _ := lt_of_lt_of_le hc (hlow _)
  intervalIntegrable t _ :=
    ((continuous_sizeOfCoalTime hη hc hlow).inv₀ fun s =>
      (lt_of_lt_of_le hc (hlow _)).ne').intervalIntegrable 0 t
  tendsto_atTop := by
    have hM : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hc (hlow 0)) (hup 0)
    rw [show cumIntensity (sizeOfCoalTime η) = coalToRealInv η from
      funext (cumIntensity_sizeOfCoalTime hη hc hlow)]
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const hM)
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact div_le_coalToRealInv hη hc hlow hup ht

theorem integrableOn_exp_neg_mul_coalToRealInv (hup : ∀ τ, η τ ≤ M) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => Real.exp (-(r * coalToRealInv η t))) (Ici 0) := by
  have hM : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hc (hlow 0)) (hup 0)
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-(r / M) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => Real.exp (-(r / M) * t))
      (by simp)).2 (exp_neg_integrableOn_Ioi 0 (div_pos hr hM))
  refine hb.mono' ?_ ?_
  · exact (Real.continuous_exp.comp ((continuous_const.mul
      (continuous_coalToRealInv hη hc hlow)).neg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have h1 := div_le_coalToRealInv hη hc hlow hup (show 0 ≤ t from ht)
    have : r * (t / M) ≤ r * coalToRealInv η t := mul_le_mul_of_nonneg_left h1 hr.le
    have e : -(r / M) * t = -(r * (t / M)) := by ring
    rw [e]
    linarith

/-- Source: myers_fefferman_patterson2008, Section 3. -/
theorem clockLaplace_sizeOfCoalTime (hup : ∀ τ, η τ ≤ M) {r : ℝ} (hr : 0 < r) :
    clockLaplace (sizeOfCoalTime η) r = ∫ τ in Ioi 0, Real.exp (-(r * τ)) * η τ := by
  have hM : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le hc (hlow 0)) (hup 0)
  have hm := strictMono_coalToReal hη fun x => lt_of_lt_of_le hc (hlow x)
  have hcomp : ∀ x, (fun t => Real.exp (-(r * coalToRealInv η t))) (coalToReal η x)
      = Real.exp (-(r * x)) := fun x => by
    simp only [coalToRealInv_coalToReal hη hc hlow]
  have key := integral_comp_mul_deriv_Ioi (a := 0) (f := coalToReal η) (f' := η)
    (g := fun t => Real.exp (-(r * coalToRealInv η t)))
    (continuous_coalToReal hη).continuousOn
    (by
      refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hc)
      filter_upwards [eventually_ge_atTop 0] with τ hτ
      exact mul_le_coalToReal hη hlow hτ)
    (fun x _ => (hasDerivAt_coalToReal hη x).hasDerivWithinAt)
    ((Real.continuous_exp.comp ((continuous_const.mul
      (continuous_coalToRealInv hη hc hlow)).neg)).continuousOn)
    ((integrableOn_exp_neg_mul_coalToRealInv hη hc hlow hup hr).mono_set (by
      rintro _ ⟨x, hx, rfl⟩
      have : coalToReal η 0 ≤ coalToReal η x := hm.monotone hx
      rwa [coalToReal_zero] at this))
    (by
      have hb : IntegrableOn (fun x : ℝ => M * Real.exp (-r * x)) (Ici 0) :=
        ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ => Real.exp (-r * x))
          (by simp)).2 (exp_neg_integrableOn_Ioi 0 hr)).const_mul M
      refine hb.mono' ?_ ?_
      · exact ((Real.continuous_exp.comp ((continuous_const.mul
          (continuous_coalToRealInv hη hc hlow)).neg)).comp
          (continuous_coalToReal hη)).mul hη |>.aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        simp only [Function.comp_apply, hcomp]
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_pos (lt_of_lt_of_le hc (hlow x)), neg_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hup x) (Real.exp_pos _).le)
  simp only [Function.comp_apply, hcomp, coalToReal_zero] at key
  rw [clockLaplace, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [cumIntensity_sizeOfCoalTime hη hc hlow]

end Bounds

/-- Source: myers_fefferman_patterson2008, secs. 3–5. -/
theorem exists_size_ne_one_sfs_eq_constant_all_sizes_of_laplace {G : ℝ → ℝ}
    (hG : Continuous G) {B : ℝ} (hB : ∀ τ, |G τ| ≤ B)
    (hGne : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Ioo s t, G u ≠ 0)
    (hL : ∀ k : ℕ, 2 ≤ k →
      ∫ τ in Ioi 0, Real.exp (-(((coalRate k : ℚ) : ℝ) * τ)) * G τ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ → ℝ, IsSizeFunction ν ∧ Continuous ν ∧ (∀ t, |ν t - 1| ≤ ε) ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Ioo s t, ν u ≠ 1) ∧
      ∀ n i : ℕ, 1 ≤ i → i < n → ∀ θ : ℝ≥0,
        ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν θ = (θ : ℝ) / i := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set m : ℝ := min ε (1 / 2) with hm
  have hm0 : 0 < m := lt_min hε (by norm_num)
  set δ : ℝ := m / (B + 1) with hδ
  have hδ0 : 0 < δ := div_pos hm0 (by linarith)
  have hδB : ∀ τ, |δ * G τ| ≤ m := by
    intro τ
    rw [abs_mul, abs_of_pos hδ0]
    calc δ * |G τ| ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left (by linarith [hB τ]) hδ0.le
      _ = m := by rw [hδ]; field_simp
  set η : ℝ → ℝ := fun τ => 1 + δ * G τ with hηdef
  have hηc : Continuous η := continuous_const.add (continuous_const.mul hG)
  have hlow : ∀ τ, (1 / 2 : ℝ) ≤ η τ := by
    intro τ
    have h1 := (abs_le.1 (hδB τ)).1
    have h2 : m ≤ 1 / 2 := min_le_right _ _
    simp only [hηdef]; linarith
  have hup : ∀ τ, η τ ≤ 3 / 2 := by
    intro τ
    have h1 := (abs_le.1 (hδB τ)).2
    have h2 : m ≤ 1 / 2 := min_le_right _ _
    simp only [hηdef]; linarith
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hν := isSizeFunction_sizeOfCoalTime hηc hc hlow hup
  have hint : IntegrableOn (fun t => Real.exp (-cumIntensity (sizeOfCoalTime η) t)) (Ioi 0) := by
    have h := (integrableOn_exp_neg_mul_coalToRealInv hηc hc hlow hup one_pos).mono_set
      Ioi_subset_Ici_self
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [cumIntensity_sizeOfCoalTime hηc hc hlow]
    simp only [one_mul]
  have hint1 : IntegrableOn (fun t => Real.exp (-cumIntensity (fun _ => (1 : ℝ)) t))
      (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [cumIntensity_one]
    simp only [neg_one_mul]
  have hclock : ∀ j : ℕ, 2 ≤ j → clockLaplace (sizeOfCoalTime η) ((coalRate j : ℚ) : ℝ)
      = clockLaplace (fun _ => (1 : ℝ)) ((coalRate j : ℚ) : ℝ) := by
    intro j hj
    have hr : (0 : ℝ) < ((coalRate j : ℚ) : ℝ) := by
      have hj' : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      simp only [coalRate, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub,
        Rat.cast_one, Rat.cast_ofNat]
      have : (0 : ℝ) < (j : ℝ) * ((j : ℝ) - 1) := by nlinarith
      positivity
    set r : ℝ := ((coalRate j : ℚ) : ℝ) with hrdef
    have hexp : IntegrableOn (fun τ : ℝ => Real.exp (-(r * τ))) (Ioi 0) := by
      refine (exp_neg_integrableOn_Ioi 0 hr).congr_fun (fun τ _ => ?_) measurableSet_Ioi
      simp only [neg_mul]
    have hexpG : IntegrableOn (fun τ : ℝ => Real.exp (-(r * τ)) * (δ * G τ)) (Ioi 0) := by
      refine (hexp.mul_const m).mono' ?_ ?_
      · exact ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
          (continuous_const.mul hG)).aestronglyMeasurable
      · refine Eventually.of_forall fun τ => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hδB τ) (Real.exp_pos _).le
    rw [clockLaplace_sizeOfCoalTime hηc hc hlow hup hr, clockLaplace]
    have hsplit : (fun τ => Real.exp (-(r * τ)) * η τ)
        = fun τ => Real.exp (-(r * τ)) + Real.exp (-(r * τ)) * (δ * G τ) := by
      funext τ; simp only [hηdef]; ring
    rw [hsplit, integral_add hexp hexpG]
    have hz : ∫ τ in Ioi 0, Real.exp (-(r * τ)) * (δ * G τ) = 0 := by
      have e : (fun τ => Real.exp (-(r * τ)) * (δ * G τ))
          = fun τ => δ * (Real.exp (-(r * τ)) * G τ) := by funext τ; ring
      rw [e, integral_const_mul, hL j hj, mul_zero]
    rw [hz, add_zero]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [cumIntensity_one]
  obtain ⟨s, t, hs, hst, hGst⟩ := hGne
  have hm' := strictMono_coalToReal hηc fun x => lt_of_lt_of_le hc (hlow x)
  refine ⟨sizeOfCoalTime η, hν, continuous_sizeOfCoalTime hηc hc hlow, ?_,
    ⟨coalToReal η s, coalToReal η t, ?_, hm' hst, ?_⟩, ?_⟩
  · intro u
    have h1 : sizeOfCoalTime η u - 1 = δ * G (coalToRealInv η u) := by
      simp only [sizeOfCoalTime, hηdef]; ring
    rw [h1]
    exact le_trans (hδB _) (min_le_left _ _)
  · have h0 := hm'.monotone hs
    rwa [coalToReal_zero] at h0
  · intro u hu
    have hmi := strictMono_coalToRealInv hηc hc hlow
    have h1 : s < coalToRealInv η u := by
      have := hmi hu.1
      rwa [coalToRealInv_coalToReal hηc hc hlow] at this
    have h2 : coalToRealInv η u < t := by
      have := hmi hu.2
      rwa [coalToRealInv_coalToReal hηc hc hlow] at this
    have hG0 := hGst _ ⟨h1, h2⟩
    simp only [sizeOfCoalTime, hηdef]
    intro h
    have : δ * G (coalToRealInv η u) = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hδ0.ne' h3
    · exact hG0 h3
  · intro n i hi hin θ
    have hl := lintegral_variableSizeMarkedLaw_sfs_congr_clockLaplace hν isSizeFunction_one
      hint hint1 (n := n) (fun j hj => hclock j (Finset.mem_Icc.1 hj).1) hi hin θ
    rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => markedKingmanSfs_nonneg n i x)
        (measurable_markedKingmanSfs n i).aestronglyMeasurable, hl,
      ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => markedKingmanSfs_nonneg n i x)
        (measurable_markedKingmanSfs n i).aestronglyMeasurable,
      variableSizeMarkedLaw_one_sfs_mean hi hin θ]

end Rhone.Statistics
