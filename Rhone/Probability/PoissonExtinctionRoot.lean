/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.PoissonGeneratingFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The extinction root of the Poisson generating function

Source: harris1963, ch. I; haldane1927, pp. 838–839, eq. (1.0). -/

@[expose] public section

namespace Rhone.Probability.PoissonExtinctionRoot

open Real Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal

def IsExtinctionRoot (c η : ℝ) : Prop :=
  0 < η ∧ η < 1 ∧ η = exp (c * (η - 1))

private theorem exp_lt_of_between {c x y z : ℝ} (hc : 0 < c) (hxy : x < y) (hyz : y < z)
    (hx : exp (c * (x - 1)) ≤ x) (hz : exp (c * (z - 1)) ≤ z) :
    exp (c * (y - 1)) < y := by
  have hzx : 0 < z - x := by linarith
  have ha : 0 < (z - y) / (z - x) := div_pos (by linarith) hzx
  have hb : 0 < (y - x) / (z - x) := div_pos (by linarith) hzx
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
    field_simp
    ring
  have hcomb : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp
    ring
  have hne : c * (x - 1) ≠ c * (z - 1) := by
    intro h
    have := mul_left_cancel₀ hc.ne' h
    linarith
  have key := strictConvexOn_exp.2 (mem_univ (c * (x - 1))) (mem_univ (c * (z - 1))) hne ha hb hab
  simp only [smul_eq_mul] at key
  have harg : (z - y) / (z - x) * (c * (x - 1)) + (y - x) / (z - x) * (c * (z - 1))
      = c * (y - 1) := by
    have e : (z - y) / (z - x) * (c * (x - 1)) + (y - x) / (z - x) * (c * (z - 1))
        = c * (((z - y) / (z - x) * x + (y - x) / (z - x) * z)
            - ((z - y) / (z - x) + (y - x) / (z - x))) := by ring
    rw [e, hcomb, hab]
  rw [harg] at key
  calc exp (c * (y - 1))
      < (z - y) / (z - x) * exp (c * (x - 1)) + (y - x) / (z - x) * exp (c * (z - 1)) := key
    _ ≤ (z - y) / (z - x) * x + (y - x) / (z - x) * z :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha.le) (mul_le_mul_of_nonneg_left hz hb.le)
    _ = y := hcomb

/-- Source: harris1963, ch. I. -/
theorem exists_isExtinctionRoot {c : ℝ} (hc : 1 < c) : ∃ η, IsExtinctionRoot c η := by
  have hc0 : 0 < c := by linarith
  set t := (c - 1) / (2 * c) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by positivity)
  have hct : c * t = (c - 1) / 2 := by
    rw [ht]
    field_simp
  have ht2 : t * (c + 1) ≤ c - 1 := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have ht1 : t < 1 := by nlinarith
  have hcont : ContinuousOn (fun x : ℝ => exp (c * (x - 1)) - x) (Icc 0 (1 - t)) :=
    Continuous.continuousOn (by fun_prop)
  have h0 : (0 : ℝ) ≤ exp (c * (0 - 1)) - 0 := by
    have := exp_pos (c * (0 - 1))
    linarith
  have h1 : exp (c * ((1 - t) - 1)) - (1 - t) ≤ 0 := by
    have hpos : 0 < 1 + c * t := by positivity
    have e1 : 1 + c * t ≤ exp (c * t) := by linarith [add_one_le_exp (c * t)]
    have e2 : exp (c * ((1 - t) - 1)) = (exp (c * t))⁻¹ := by
      rw [← exp_neg]
      ring_nf
    have e3 : (exp (c * t))⁻¹ ≤ (1 + c * t)⁻¹ := inv_anti₀ hpos e1
    have e4 : (1 + c * t)⁻¹ ≤ 1 - t := by
      rw [inv_le_iff_one_le_mul₀ hpos, hct]
      nlinarith
    linarith
  obtain ⟨η, hη, hηeq⟩ := intermediate_value_Icc' (by linarith) hcont ⟨h1, h0⟩
  have hroot : η = exp (c * (η - 1)) := by
    have : exp (c * (η - 1)) - η = 0 := hηeq
    linarith
  refine ⟨η, ?_, ?_, hroot⟩
  · rw [hroot]
    exact exp_pos _
  · linarith [hη.2]

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.unique {c η₁ η₂ : ℝ} (hc : 0 < c) (h₁ : IsExtinctionRoot c η₁)
    (h₂ : IsExtinctionRoot c η₂) : η₁ = η₂ := by
  have h1 : exp (c * ((1 : ℝ) - 1)) ≤ 1 := by simp
  rcases lt_trichotomy η₁ η₂ with h | h | h
  · have := exp_lt_of_between hc h h₂.2.1 h₁.2.2.ge h1
    exact absurd h₂.2.2.symm this.ne
  · exact h
  · have := exp_lt_of_between hc h h₁.2.1 h₂.2.2.ge h1
    exact absurd h₁.2.2.symm this.ne

/-- Source: harris1963, ch. I. -/
theorem existsUnique_isExtinctionRoot {c : ℝ} (hc : 1 < c) : ∃! η, IsExtinctionRoot c η := by
  obtain ⟨η, hη⟩ := exists_isExtinctionRoot hc
  exact ⟨η, hη, fun y hy => hy.unique (by linarith) hη⟩

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.eq_or_eq_one {c η x : ℝ} (hc : 0 < c) (h : IsExtinctionRoot c η)
    (hx : x = exp (c * (x - 1))) : x = η ∨ x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · left
    have hx0 : 0 < x := by
      rw [hx]
      exact exp_pos _
    exact IsExtinctionRoot.unique hc ⟨hx0, h1, hx⟩ h
  · exact Or.inr h1
  · exfalso
    have := exp_lt_of_between hc h.2.1 h1 h.2.2.ge hx.ge
    simp at this

noncomputable def extinctionRoot (c : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ x = exp (c * (x - 1))}

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.eq_extinctionRoot {c η : ℝ} (hc : 0 < c) (h : IsExtinctionRoot c η) :
    extinctionRoot c = η := by
  have hleast : IsLeast {x : ℝ | 0 ≤ x ∧ x = exp (c * (x - 1))} η := by
    refine ⟨⟨h.1.le, h.2.2⟩, ?_⟩
    rintro x ⟨-, hx⟩
    rcases h.eq_or_eq_one hc hx with e | e
    · exact e.ge
    · rw [e]
      exact h.2.1.le
  exact hleast.csInf_eq

/-- Source: harris1963, ch. I. -/
theorem isExtinctionRoot_extinctionRoot {c : ℝ} (hc : 1 < c) :
    IsExtinctionRoot c (extinctionRoot c) := by
  obtain ⟨η, hη⟩ := exists_isExtinctionRoot hc
  rw [hη.eq_extinctionRoot (by linarith)]
  exact hη

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.log_eq {c η : ℝ} (h : IsExtinctionRoot c η) :
    log η = c * (η - 1) := by
  have e := h.2.2
  conv_lhs => rw [e]
  exact log_exp _

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.neg_log_eq {c η : ℝ} (h : IsExtinctionRoot c η) :
    -log η = c * (1 - η) := by
  rw [h.log_eq]
  ring

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.mul_lt_one {c η : ℝ} (hc : 0 < c) (h : IsExtinctionRoot c η) :
    c * η < 1 := by
  obtain ⟨h0, h1, he⟩ := h
  have hne : c * (1 - η) ≠ 0 := (mul_pos hc (by linarith)).ne'
  have e1 : c * (1 - η) + 1 < exp (c * (1 - η)) := add_one_lt_exp hne
  have e2 : exp (c * (1 - η)) = η⁻¹ := by
    have : c * (1 - η) = -(c * (η - 1)) := by ring
    rw [this, exp_neg, ← he]
  rw [e2] at e1
  have e3 := mul_lt_mul_of_pos_left e1 h0
  rw [mul_inv_cancel₀ h0.ne'] at e3
  by_contra hge
  rw [not_lt] at hge
  nlinarith [mul_nonneg (sub_nonneg.2 hge) (sub_nonneg.2 h1.le)]

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.tendsto_iterate {c η : ℝ} (hc : 0 < c) (h : IsExtinctionRoot c η) :
    Tendsto (fun n : ℕ => (fun s : ℝ => exp (c * (s - 1)))^[n] 0) atTop (𝓝 η) := by
  set f : ℝ → ℝ := fun s => exp (c * (s - 1)) with hf
  have hmono : Monotone f := by
    intro a b hab
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hc.le)
  have hfη : f η = η := h.2.2.symm
  have hf0 : (0 : ℝ) ≤ f 0 := (exp_pos _).le
  have hseq : Monotone fun n : ℕ => f^[n] 0 := hmono.monotone_iterate_of_le_map hf0
  have hle : ∀ n : ℕ, f^[n] 0 ≤ η := by
    intro n
    induction n with
    | zero => exact h.1.le
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc f (f^[n] 0) ≤ f η := hmono ih
        _ = η := hfη
  have hbdd : BddAbove (Set.range fun n : ℕ => f^[n] 0) :=
    ⟨η, by rintro _ ⟨n, rfl⟩; exact hle n⟩
  have hlim := tendsto_atTop_ciSup hseq hbdd
  set L := ⨆ n : ℕ, f^[n] 0 with hL
  have hcontf : Continuous f := by
    rw [hf]
    fun_prop
  have hfix : f L = L := isFixedPt_of_tendsto_iterate hlim hcontf.continuousAt
  have hLle : L ≤ η := ciSup_le hle
  rcases h.eq_or_eq_one hc hfix.symm with e | e
  · rw [← e]
    exact hlim
  · exfalso
    linarith [h.2.1]

/-- Source: harris1963, ch. I. -/
theorem tendsto_iterate_extinctionRoot {c : ℝ} (hc : 1 < c) :
    Tendsto (fun n : ℕ => (fun s : ℝ => exp (c * (s - 1)))^[n] 0) atTop
      (𝓝 (extinctionRoot c)) :=
  (isExtinctionRoot_extinctionRoot hc).tendsto_iterate (by linarith)

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.rpow_eq {c η : ℝ} (h : IsExtinctionRoot c η) (x : ℝ) :
    η ^ x = exp (c * x * (η - 1)) := by
  rw [rpow_def_of_pos h.1, h.log_eq]
  ring_nf

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.integral_pow_poissonMeasure {c η : ℝ} (h : IsExtinctionRoot c η)
    (x : ℝ) (r : ℝ≥0) (hr : (r : ℝ) = c * x) :
    ∫ k : ℕ, η ^ k ∂poissonMeasure r = η ^ x := by
  rw [Rhone.Probability.poisson_integral_pow, h.rpow_eq x, hr]
  congr 1
  ring

private theorem hasSum_natCast_mul_poisson_mul_pow (μ t : ℝ) :
    HasSum (fun k : ℕ => (k : ℝ) * (exp (-μ) * μ ^ k / (k.factorial : ℝ) * t ^ k))
      (μ * t * exp (μ * (t - 1))) := by
  have h0 : HasSum (fun k : ℕ => exp (-μ) * μ ^ k / (k.factorial : ℝ) * t ^ k)
      (exp (μ * (t - 1))) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (μ * t)
    rw [← Real.exp_eq_exp_ℝ] at h
    have h2 := h.mul_left (exp (-μ))
    have e : exp (-μ) * exp (μ * t) = exp (μ * (t - 1)) := by
      rw [← exp_add]
      ring_nf
    rw [e] at h2
    refine h2.congr_fun fun k => ?_
    rw [mul_pow]
    ring
  have h := h0.mul_left (μ * t)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have h3 : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (exp (-μ) * μ ^ (k + 1) / ((k + 1).factorial : ℝ) * t ^ (k + 1)))
      = fun k : ℕ => μ * t * (exp (-μ) * μ ^ k / (k.factorial : ℝ) * t ^ k) := by
    funext k
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ, Nat.cast_mul]
    field_simp
    ring
  rw [h3]
  exact h

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.hasSum_natCast_mul_pow {c η : ℝ} (h : IsExtinctionRoot c η) (x : ℝ) :
    HasSum (fun k : ℕ =>
        (k : ℝ) * (exp (-(c * x)) * (c * x) ^ k / (k.factorial : ℝ) * η ^ k))
      (c * x * η ^ (x + 1)) := by
  have e : c * x * η ^ (x + 1) = c * x * η * exp (c * x * (η - 1)) := by
    rw [rpow_add_one h.1.ne', h.rpow_eq x]
    ring
  rw [e]
  exact hasSum_natCast_mul_poisson_mul_pow (c * x) η

noncomputable def tiltedKernel (c η x : ℝ) (y : ℕ) : ℝ :=
  η ^ ((y : ℝ) - x) * ((y : ℝ) / x) * (exp (-(c * x)) * (c * x) ^ y / (y.factorial : ℝ))

/-- Source: harris1963, ch. I. -/
theorem IsExtinctionRoot.hasSum_tiltedKernel {c η x : ℝ} (h : IsExtinctionRoot c η)
    (hx : 0 < x) : HasSum (tiltedKernel c η x) (c * η) := by
  have hs := (h.hasSum_natCast_mul_pow x).mul_left (η ^ (-x) / x)
  have hη0 := h.1
  have e : η ^ (-x) / x * (c * x * η ^ (x + 1)) = c * η := by
    rw [rpow_neg hη0.le, rpow_add_one hη0.ne']
    have hpx : 0 < η ^ x := rpow_pos_of_pos hη0 x
    field_simp
  rw [e] at hs
  have hfun : tiltedKernel c η x = fun k : ℕ => η ^ (-x) / x *
      ((k : ℝ) * (exp (-(c * x)) * (c * x) ^ k / (k.factorial : ℝ) * η ^ k)) := by
    funext k
    unfold tiltedKernel
    rw [sub_eq_add_neg, rpow_add hη0, rpow_natCast]
    ring
  rw [hfun]
  exact hs

/--
Source: haldane1927, p. 839, eq. (1.0); felsenstein_teg2019, sec. VII.7, eq. (VII-66)–(VII-69), pp.
316–317. -/
theorem IsExtinctionRoot.one_sub_le {c η : ℝ} (h : IsExtinctionRoot c η) :
    1 - η ≤ 2 * (c - 1) := by
  have h0 := h.1
  have h1 := h.2.1
  have hδ0 : 0 < 1 - η := by linarith
  have habs : |1 - η| < 1 := by
    rw [abs_of_pos hδ0]
    linarith
  have hlog : -log (1 - (1 - η)) = c * (1 - η) := by
    rw [sub_sub_cancel, h.neg_log_eq]
  have hs := hasSum_pow_div_log_of_abs_lt_one habs
  have hlow := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
  rw [hlog, Finset.sum_range_succ, Finset.sum_range_one] at hlow
  norm_num at hlow
  nlinarith

/--
Source: haldane1927, p. 839, eq. (1.0); felsenstein_teg2019, sec. VII.7, eq. (VII-66)–(VII-69), pp.
316–317. -/
theorem IsExtinctionRoot.le_one_sub {c η : ℝ} (hc : 1 < c) (h : IsExtinctionRoot c η) :
    (1 - 4 * (c - 1)) * (2 * (c - 1)) ≤ 1 - η := by
  have h0 := h.1
  have h1 := h.2.1
  have hle := h.one_sub_le
  have hlog' := h.log_eq
  set δ := 1 - η with hδ
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ < 1 := by linarith
  have habs : |δ| < 1 := by
    rw [abs_of_pos hδ0]
    exact hδ1
  have hlog : log (1 - δ) = -(c * δ) := by
    rw [hδ, sub_sub_cancel, hlog']
    ring
  have hup := abs_log_sub_add_sum_range_le habs 2
  rw [hlog, Finset.sum_range_succ, Finset.sum_range_one, abs_of_pos hδ0] at hup
  norm_num at hup
  have hq := (abs_le.1 hup).1
  have hne : (1 - δ) ≠ 0 := by linarith
  have h4 : δ ^ 3 / (1 - δ) * (1 - δ) = δ ^ 3 := div_mul_cancel₀ _ hne
  have h3 : c * δ * (1 - δ) ≤ (δ + δ ^ 2 / 2) * (1 - δ) + δ ^ 3 := by
    have hq' : c * δ ≤ δ + δ ^ 2 / 2 + δ ^ 3 / (1 - δ) := by linarith
    have := mul_le_mul_of_nonneg_right hq' (by linarith : (0 : ℝ) ≤ 1 - δ)
    rw [add_mul, h4] at this
    linarith
  have h5 : (c - 1) * (1 - δ) ≤ δ * (1 - δ) / 2 + δ ^ 2 := by
    by_contra hh
    rw [not_le] at hh
    nlinarith [mul_pos hδ0 (sub_pos.2 hh)]
  by_contra hcon
  rw [not_le] at hcon
  have he : 0 < 2 * (c - 1) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hδ0.le,
    mul_lt_mul_of_pos_right hcon (by linarith : (0 : ℝ) < 1 + 2 * (2 * (c - 1))),
    pow_pos he 3]

/-- Source: haldane1927, p. 839, eq. (1.0). -/
theorem tendsto_one_sub_extinctionRoot_div :
    Tendsto (fun c : ℝ => (1 - extinctionRoot c) / (2 * (c - 1))) (𝓝[>] 1) (𝓝 1) := by
  have hlow : Tendsto (fun c : ℝ => 1 - 4 * (c - 1)) (𝓝[>] 1) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (Continuous.tendsto' (by fun_prop) 1 1 (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc' : (1 : ℝ) < c := hc
    rw [le_div_iff₀ (by linarith)]
    exact (isExtinctionRoot_extinctionRoot hc').le_one_sub hc'
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc' : (1 : ℝ) < c := hc
    rw [div_le_one (by linarith)]
    exact (isExtinctionRoot_extinctionRoot hc').one_sub_le

end Rhone.Probability.PoissonExtinctionRoot
