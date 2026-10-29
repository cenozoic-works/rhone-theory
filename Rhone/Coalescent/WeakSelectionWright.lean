/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.WeakSelectionEdge
public import Rhone.Diffusion.WrightStationaryDensitySelection
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Weak-selection edge response of the two-allele model as a Wright density moment

Source: ewens2004, eq. (5.72), p. 175, eq. (5.70)–(5.71), p. 174. -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory Set Filter Topology Diffusion
open LinearAlgebra.Recursion Analysis.TruncationRemainder TruncationRemainder
open scoped Interval

noncomputable def selMomentNum (σ θ₁ θ₂ : ℝ) (a b : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b * wrightDensitySel σ θ₁ θ₂ x

noncomputable def selMoment (σ θ₁ θ₂ : ℝ) (a b : ℕ) : ℝ :=
  selMomentNum σ θ₁ θ₂ a b / ∫ x in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ x

theorem selMomentNum_zero_zero (σ θ₁ θ₂ : ℝ) :
    selMomentNum σ θ₁ θ₂ 0 0 = ∫ x in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ x := by
  simp [selMomentNum]

private theorem measurable_wrightDensity (θ₁ θ₂ : ℝ) : Measurable (wrightDensity θ₁ θ₂) := by
  unfold wrightDensity
  exact (measurable_id.pow_const _).mul ((measurable_const.sub measurable_id).pow_const _)

private theorem wrightDensity_nonneg (θ₁ θ₂ : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ wrightDensity θ₁ θ₂ x := by
  unfold wrightDensity
  exact mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg (by linarith) _)

theorem hasDerivAt_selMomentNum {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (σ : ℝ) (a b : ℕ) :
    HasDerivAt (fun s => selMomentNum s θ₁ θ₂ a b) (2 * selMomentNum σ θ₁ θ₂ (a + 1) b) σ := by
  set F : ℝ → ℝ → ℝ := fun s x => x ^ a * (1 - x) ^ b * wrightDensitySel s θ₁ θ₂ x with hF
  set F' : ℝ → ℝ → ℝ :=
    fun s x => 2 * (x ^ (a + 1) * (1 - x) ^ b * wrightDensitySel s θ₁ θ₂ x) with hF'
  set B : ℝ := 2 * Real.exp (2 * (|σ| + 1)) with hB
  have hmeasSel : ∀ s : ℝ, Measurable (wrightDensitySel s θ₁ θ₂) := by
    intro s
    unfold wrightDensitySel
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_wrightDensity θ₁ θ₂)
  have hFmeas : ∀ s : ℝ, Measurable (F s) := by
    intro s
    exact (((measurable_id.pow_const a).mul
      ((measurable_const.sub measurable_id).pow_const b))).mul (hmeasSel s)
  have hF'meas : Measurable (F' σ) :=
    measurable_const.mul ((((measurable_id.pow_const (a + 1)).mul
      ((measurable_const.sub measurable_id).pow_const b))).mul (hmeasSel σ))
  have hFint : IntervalIntegrable (F σ) volume 0 1 :=
    (intervalIntegrable_wrightDensitySel σ h₁ h₂).continuousOn_mul
      (Continuous.continuousOn (by fun_prop))
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (σ - 1) (σ + 1),
      ‖F' s t‖ ≤ B * wrightDensity θ₁ θ₂ t := by
    refine Filter.Eventually.of_forall fun t ht s hs => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have hw := wrightDensity_nonneg θ₁ θ₂ ht0 ht1
    have hp1 : t ^ (a + 1) ≤ 1 := pow_le_one₀ ht0 ht1
    have hp1' : 0 ≤ t ^ (a + 1) := pow_nonneg ht0 _
    have hp2 : (1 - t) ^ b ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hp2' : 0 ≤ (1 - t) ^ b := pow_nonneg (by linarith) _
    have hs' : |s| ≤ |σ| + 1 := by
      rw [abs_le]
      constructor
      · linarith [hs.1, neg_abs_le σ]
      · linarith [hs.2, le_abs_self σ]
    have hst : 2 * s * t ≤ 2 * (|σ| + 1) := by
      have h1 : s * t ≤ |s| * 1 :=
        (mul_le_mul_of_nonneg_right (le_abs_self s) ht0).trans
          (mul_le_mul_of_nonneg_left ht1 (abs_nonneg s))
      linarith
    have hexp : Real.exp (2 * s * t) ≤ Real.exp (2 * (|σ| + 1)) := Real.exp_le_exp.2 hst
    have hexp0 : 0 < Real.exp (2 * s * t) := Real.exp_pos _
    have hnn : 0 ≤ F' s t := by
      simp only [hF', wrightDensitySel]
      positivity
    rw [Real.norm_of_nonneg hnn]
    simp only [hF', hB, wrightDensitySel]
    have hprod : t ^ (a + 1) * (1 - t) ^ b ≤ 1 := by
      calc t ^ (a + 1) * (1 - t) ^ b ≤ 1 * 1 := mul_le_mul hp1 hp2 hp2' zero_le_one
        _ = 1 := one_mul 1
    have hprod' : 0 ≤ t ^ (a + 1) * (1 - t) ^ b := mul_nonneg hp1' hp2'
    have h3 : t ^ (a + 1) * (1 - t) ^ b * (Real.exp (2 * s * t) * wrightDensity θ₁ θ₂ t)
        ≤ 1 * (Real.exp (2 * (|σ| + 1)) * wrightDensity θ₁ θ₂ t) :=
      mul_le_mul hprod (mul_le_mul_of_nonneg_right hexp hw)
        (mul_nonneg hexp0.le hw) zero_le_one
    linarith
  have hBint : IntervalIntegrable (fun t => B * wrightDensity θ₁ θ₂ t) volume 0 1 :=
    (intervalIntegrable_wrightDensity h₁ h₂).const_mul B
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 → ∀ s ∈ Ioo (σ - 1) (σ + 1),
      HasDerivAt (fun s => F s t) (F' s t) s := by
    refine Filter.Eventually.of_forall fun t _ s _ => ?_
    have he : HasDerivAt (fun s : ℝ => Real.exp (2 * s * t))
        (Real.exp (2 * s * t) * (2 * t)) s := by
      have hlin : HasDerivAt (fun s : ℝ => 2 * s * t) (2 * t) s := by
        simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const t
      exact hlin.exp
    have h := ((he.mul_const (wrightDensity θ₁ θ₂ t)).const_mul (t ^ a * (1 - t) ^ b))
    simp only [hF, hF', wrightDensitySel]
    refine h.congr_deriv ?_
    ring
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (x₀ := σ)
    (s := Ioo (σ - 1) (σ + 1)) (bound := fun t => B * wrightDensity θ₁ θ₂ t)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable)
    hFint hF'meas.aestronglyMeasurable hbound hBint hdiff
  have h := key.2
  have hval : ∫ t in (0 : ℝ)..1, F' σ t = 2 * selMomentNum σ θ₁ θ₂ (a + 1) b := by
    simp only [hF', selMomentNum]
    rw [intervalIntegral.integral_const_mul]
  rw [hval] at h
  exact h

theorem hasDerivAt_selMoment {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (σ : ℝ) (a b : ℕ) :
    HasDerivAt (fun s => selMoment s θ₁ θ₂ a b)
      (2 * (selMoment σ θ₁ θ₂ (a + 1) b - selMoment σ θ₁ θ₂ 1 0 * selMoment σ θ₁ θ₂ a b))
      σ := by
  have hN := hasDerivAt_selMomentNum h₁ h₂ σ a b
  have hZ := hasDerivAt_selMomentNum h₁ h₂ σ 0 0
  have hZpos : 0 < selMomentNum σ θ₁ θ₂ 0 0 := by
    rw [selMomentNum_zero_zero]; exact integral_wrightDensitySel_pos σ h₁ h₂
  have hfun : (fun s => selMoment s θ₁ θ₂ a b)
      = fun s => selMomentNum s θ₁ θ₂ a b / selMomentNum s θ₁ θ₂ 0 0 := by
    funext s; rw [selMoment, selMomentNum_zero_zero]
  rw [hfun]
  refine (hN.div hZ hZpos.ne').congr_deriv ?_
  simp only [selMoment, ← selMomentNum_zero_zero, zero_add]
  field_simp

private theorem gamma_add_nat {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Real.Gamma (θ + n) = rising θ n * Real.Gamma θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : θ + (n : ℝ) ≠ 0 := by positivity
    rw [rising_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hne, ih]
    ring

private theorem selMomentNum_zero_eq_beta {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (a b : ℕ) :
    selMomentNum 0 θ₁ θ₂ a b = ProbabilityTheory.beta (θ₁ + a) (θ₂ + b) := by
  have ha : 0 < θ₁ + a := by positivity
  have hb : 0 < θ₂ + b := by positivity
  rw [← integral_wrightDensity ha hb, selMomentNum,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have e1 : x ^ (θ₁ + (a : ℝ) - 1) = x ^ (θ₁ - 1) * x ^ a := by
    rw [show θ₁ + (a : ℝ) - 1 = (θ₁ - 1) + (a : ℝ) by ring, Real.rpow_add hx0,
      Real.rpow_natCast]
  have e2 : (1 - x) ^ (θ₂ + (b : ℝ) - 1) = (1 - x) ^ (θ₂ - 1) * (1 - x) ^ b := by
    rw [show θ₂ + (b : ℝ) - 1 = (θ₂ - 1) + (b : ℝ) by ring, Real.rpow_add hx1,
      Real.rpow_natCast]
  simp only [wrightDensitySel, wrightDensity, e1, e2]
  simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
  ring

/-- Source: ewens2004, eq. (5.70)–(5.71), p. 174. -/
theorem selMoment_zero {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (a b : ℕ) :
    selMoment 0 θ₁ θ₂ a b = rising θ₁ a * rising θ₂ b / rising (θ₁ + θ₂) (a + b) := by
  have h12 : 0 < θ₁ + θ₂ := by positivity
  have hG1 := Real.Gamma_pos_of_pos h₁
  have hG2 := Real.Gamma_pos_of_pos h₂
  have hG12 := Real.Gamma_pos_of_pos h12
  have hr := rising_pos h12 (a + b)
  have hden : ∫ x in (0 : ℝ)..1, wrightDensitySel 0 θ₁ θ₂ x = ProbabilityTheory.beta θ₁ θ₂ := by
    rw [← selMomentNum_zero_zero, selMomentNum_zero_eq_beta h₁ h₂]
    simp
  have hsum : θ₁ + (a : ℝ) + (θ₂ + (b : ℝ)) = (θ₁ + θ₂) + ((a + b : ℕ) : ℝ) := by
    push_cast; ring
  rw [selMoment, selMomentNum_zero_eq_beta h₁ h₂, hden, ProbabilityTheory.beta,
    ProbabilityTheory.beta, hsum, gamma_add_nat h₁, gamma_add_nat h₂, gamma_add_nat h12]
  field_simp

theorem selMoment_zero_eq_qOne {θ : ℝ} (hθ : 0 < θ) {π : Fin 2 → ℝ} (h0 : 0 < π 0)
    (h1 : 0 < π 1) (hsum : π 0 + π 1 = 1) (m : Fin 2 → ℕ) :
    selMoment 0 (θ * π 0) (θ * π 1) (m 0) (m 1) = qOne θ π m := by
  have hθeq : θ * π 0 + θ * π 1 = θ := by rw [← mul_add, hsum, mul_one]
  rw [selMoment_zero (mul_pos hθ h0) (mul_pos hθ h1), hθeq, qOne, Fin.prod_univ_two,
    Fin.sum_univ_two]

theorem hasDerivAt_selMoment_tiltResponse {θ : ℝ} (hθ : 0 < θ) {π : Fin 2 → ℝ}
    (h0 : 0 < π 0) (h1 : 0 < π 1) (hsum : π 0 + π 1 = 1) (m : Fin 2 → ℕ) :
    HasDerivAt (fun s : ℝ => selMoment (s / 2) (θ * π 0) (θ * π 1) (m 0) (m 1))
      (tiltResponse θ π 0 m) 0 := by
  have hA : HasDerivAt (fun s => selMoment s (θ * π 0) (θ * π 1) (m 0) (m 1))
      (2 * (selMoment 0 (θ * π 0) (θ * π 1) (m 0 + 1) (m 1)
        - selMoment 0 (θ * π 0) (θ * π 1) 1 0 * selMoment 0 (θ * π 0) (θ * π 1) (m 0) (m 1)))
      ((0 : ℝ) / 2) := by
    rw [zero_div]
    exact hasDerivAt_selMoment (mul_pos hθ h0) (mul_pos hθ h1) 0 (m 0) (m 1)
  have hhalf : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hcomp := hA.comp (0 : ℝ) hhalf
  refine hcomp.congr_deriv ?_
  have e1 : selMoment 0 (θ * π 0) (θ * π 1) (m 0 + 1) (m 1) = qOne θ π (incf m 0) := by
    have h := selMoment_zero_eq_qOne hθ h0 h1 hsum (incf m 0)
    rw [incf_self, incf_of_ne m (show (1 : Fin 2) ≠ 0 by decide)] at h
    exact h
  have e2 : selMoment 0 (θ * π 0) (θ * π 1) 1 0 = π 0 := by
    have h := selMoment_zero_eq_qOne hθ h0 h1 hsum (incf (fun _ => 0) 0)
    rw [incf_self, incf_of_ne _ (show (1 : Fin 2) ≠ 0 by decide), qOne_eA hθ.ne'] at h
    exact h
  rw [e1, e2, selMoment_zero_eq_qOne hθ h0 h1 hsum m, tiltResponse]
  ring

section Bridge

variable {KB : ℕ} {θA θB ρ : ℝ} {πA : Fin 2 → ℝ} {πB : Fin KB → ℝ}

noncomputable def wrightResponse (θA : ℝ) (πA : Fin 2 → ℝ) (ξ : Config 2 KB) : ℝ :=
  deriv (fun s : ℝ => selMoment (s / 2) (θA * πA 0) (θA * πA 1) (ξ.a 0) (ξ.a 1)) 0

theorem wrightResponse_eq_edgeResponse (hθA : 0 < θA) (h0 : 0 < πA 0) (h1 : 0 < πA 1)
    (hsum : πA 0 + πA 1 = 1) :
    (wrightResponse θA πA : Config 2 KB → ℝ) = edgeResponse θA πA 0 := by
  funext ξ
  exact (hasDerivAt_selMoment_tiltResponse hθA h0 h1 hsum ξ.a).deriv

theorem edge_response_recursion_wright (hθA : 0 < θA) (h0 : 0 < πA 0) (h1 : 0 < πA 1)
    (hsum : πA 0 + πA 1 = 1) {q : Config 2 KB → ℝ} (hq : IsSolution θA θB ρ πA πB q)
    (ξ : Config 2 KB) (hB : ξ.nB = 0) :
    diag θA θB ρ ξ * wrightResponse θA πA ξ
      = rhs θA θB ρ πA πB (wrightResponse θA πA) ξ + sel 0 q ξ := by
  rw [wrightResponse_eq_edgeResponse hθA h0 h1 hsum]
  exact IsSolution.edge_response_recursion hθA hq 0 ξ hB

theorem edge_response_unique_wright (hθA : 0 < θA) (h0 : 0 < πA 0) (h1 : 0 < πA 1)
    (hsum : πA 0 + πA 1 = 1) (u : Config 2 KB → ℝ)
    (hu0 : ∀ ξ : Config 2 KB, ξ.n = 0 → u ξ = 0)
    (hu : ∀ ξ : Config 2 KB, ξ.nB = 0 → 1 ≤ ξ.n →
      diag θA θB ρ ξ * u ξ
        = rhs θA θB ρ πA πB u ξ + sel 0 (edgeNeutral θA πA) ξ)
    (ξ : Config 2 KB) (hB : ξ.nB = 0) :
    HasDerivAt (fun s : ℝ => selMoment (s / 2) (θA * πA 0) (θA * πA 1) (ξ.a 0) (ξ.a 1))
      (u ξ) 0 := by
  rw [edge_response_unique hθA 0 u hu0 hu ξ hB]
  exact hasDerivAt_selMoment_tiltResponse hθA h0 h1 hsum ξ.a

theorem IsHierarchy.edge_hasDerivAt (hθA : 0 < θA) (h0 : 0 < πA 0) (h1 : 0 < πA 1)
    (hsum : πA 0 + πA 1 = 1) {V : Config 2 KB → ℝ} {q : ℕ → Config 2 KB → ℝ}
    (hq : IsHierarchy V (Tplus θA θB ρ πA πB) (Umodel θA θB ρ 0) (vplus θA θB ρ πA πB) q)
    (ξ : Config 2 KB) (hB : ξ.nB = 0) (hn : 1 ≤ ξ.n) :
    q 0 ξ = selMoment 0 (θA * πA 0) (θA * πA 1) (ξ.a 0) (ξ.a 1) ∧
      HasDerivAt (fun s : ℝ => selMoment (s / 2) (θA * πA 0) (θA * πA 1) (ξ.a 0) (ξ.a 1))
        (q 1 ξ) 0 := by
  refine ⟨?_, ?_⟩
  · rw [IsHierarchy.edge_zero hθA hq ξ hB hn, selMoment_zero_eq_qOne hθA h0 h1 hsum]
  · rw [IsHierarchy.edge_one hθA hq ξ hB hn]
    exact hasDerivAt_selMoment_tiltResponse hθA h0 h1 hsum ξ.a

end Bridge

end Rhone.Coalescent
