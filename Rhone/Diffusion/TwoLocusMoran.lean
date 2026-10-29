/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FinChain
public import Rhone.Diffusion.TwoLocusMaximumPrinciple
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A two-locus Moran chain whose generator approximates the two-locus diffusion

Source: ethier_kurtz1986, ch. 10. -/

@[expose] public section

namespace Rhone.Diffusion

open MvPolynomial Finset Rhone.LinearAlgebra MarkovChain

variable {KA KB : ℕ}

theorem abs_le_mul_pow_succ_of_hasDerivAt {f f' : ℝ → ℝ} {C s : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : f 0 = 0)
    (hb : ∀ t ∈ Set.Icc 0 s, |f' t| ≤ C * t ^ m) :
    ∀ t ∈ Set.Icc 0 s, |f t| ≤ C * t ^ (m + 1) := by
  intro t ht
  have hbound : ∀ y ∈ Set.Ico 0 t, ‖f' y‖ ≤ C * t ^ m := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact (hb y ⟨hy.1, hy.2.le.trans ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.1 hy.2.le m) hC)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := 0) (b := t)
    (fun y _ => (hf y).hasDerivWithinAt) hbound t ⟨ht.1, le_rfl⟩
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
  calc |f t| ≤ C * t ^ m * t := hmv
    _ = C * t ^ (m + 1) := by ring

theorem abs_polynomial_taylor_two_le (P : Polynomial ℝ) {M s : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hb : ∀ t ∈ Set.Icc 0 s,
      |(Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval t| ≤ M) :
    |P.eval s - P.eval 0 - s * (Polynomial.derivative P).eval 0 -
        s ^ 2 / 2 * (Polynomial.derivative (Polynomial.derivative P)).eval 0| ≤ M * s ^ 3 := by
  have h2 := abs_le_mul_pow_succ_of_hasDerivAt (m := 0)
    (f := fun t => (Polynomial.derivative (Polynomial.derivative P)).eval t -
      (Polynomial.derivative (Polynomial.derivative P)).eval 0)
    (f' := fun t =>
      (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative P))).eval t) hM
    (fun t => (Polynomial.hasDerivAt _ t).sub_const _) (sub_self _)
    (fun t ht => by simpa using hb t ht)
  have h1 := abs_le_mul_pow_succ_of_hasDerivAt (m := 1)
    (f := fun t => (Polynomial.derivative P).eval t - (Polynomial.derivative P).eval 0 -
      t * (Polynomial.derivative (Polynomial.derivative P)).eval 0)
    (f' := fun t => (Polynomial.derivative (Polynomial.derivative P)).eval t -
      (Polynomial.derivative (Polynomial.derivative P)).eval 0) hM
    (fun t => by
      have := ((Polynomial.hasDerivAt (Polynomial.derivative P) t).sub_const
        ((Polynomial.derivative P).eval 0)).sub
        ((hasDerivAt_id' t).mul_const
          ((Polynomial.derivative (Polynomial.derivative P)).eval 0))
      convert this using 1
      ring)
    (by simp) h2
  have h0 := abs_le_mul_pow_succ_of_hasDerivAt (m := 2)
    (f := fun t => P.eval t - P.eval 0 - t * (Polynomial.derivative P).eval 0 -
      t ^ 2 / 2 * (Polynomial.derivative (Polynomial.derivative P)).eval 0)
    (f' := fun t => (Polynomial.derivative P).eval t - (Polynomial.derivative P).eval 0 -
      t * (Polynomial.derivative (Polynomial.derivative P)).eval 0) hM
    (fun t => by
      have := (((Polynomial.hasDerivAt P t).sub_const (P.eval 0)).sub
        ((hasDerivAt_id' t).mul_const ((Polynomial.derivative P).eval 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const
          ((Polynomial.derivative (Polynomial.derivative P)).eval 0))
      convert this using 1
      norm_num)
    (by simp) h1
  exact h0 s ⟨hs, le_rfl⟩

theorem exists_nonneg_bound_of_forall {α ι : Type*} [Finite ι] {S : Set α} (F : ι → α → ℝ)
    (h : ∀ i, ∃ C, ∀ y ∈ S, |F i y| ≤ C) : ∃ C, 0 ≤ C ∧ ∀ i, ∀ y ∈ S, |F i y| ≤ C := by
  have := Fintype.ofFinite ι
  choose C hC using h
  refine ⟨∑ i, |C i|, sum_nonneg fun i _ => abs_nonneg _, fun i y hy => ?_⟩
  exact (hC i y hy).trans ((le_abs_self _).trans
    (single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (mem_univ i)))

theorem exists_bound_eval_of_isCompact {G : Type*} {S : Set (G → ℝ)} (hS : IsCompact S)
    (p : MvPolynomial G ℝ) : ∃ C, ∀ y ∈ S, |eval y p| ≤ C := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (MvPolynomial.continuous_eval p).continuousOn
  refine ⟨C, fun y hy => ?_⟩
  have := hC y hy
  rwa [Real.norm_eq_abs] at this

theorem exists_bound_eval_line (w : Fin KA × Fin KB → ℝ) (q : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ C, ∀ p ∈ gameteSimplex KA KB ×ˢ Set.Icc (0 : ℝ) 1, |eval (p.1 + p.2 • w) q| ≤ C := by
  have hc : Continuous fun p : (Fin KA × Fin KB → ℝ) × ℝ => eval (p.1 + p.2 • w) q :=
    (MvPolynomial.continuous_eval q).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))
  obtain ⟨C, hC⟩ :=
    (isCompact_gameteSimplex.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp => ?_⟩
  have := hC p hp
  rwa [Real.norm_eq_abs] at this

theorem abs_moranStep_sub_le {G : Type*} [Fintype G] {x b d : G → ℝ} {D2 φ : G → G → ℝ}
    {s F0 Q2 M Mb M2 : ℝ} (hx0 : ∀ g, 0 ≤ x g) (hx1 : ∑ g, x g = 1) (hb : ∑ h, b h = 0)
    (hs : 0 < s) (hr : ∀ h, 0 ≤ x h + s * b h)
    (hQ2 : ∑ g, x g * ∑ h, x h * D2 g h = 2 * Q2)
    (hφ : ∀ g h, |φ g h - (F0 + s * (d h - d g) + s ^ 2 / 2 * D2 g h)| ≤ M * s ^ 3)
    (hbM : ∀ h, |b h| ≤ Mb) (hD2M : ∀ g h, |D2 g h| ≤ M2) :
    |(s ^ 2)⁻¹ * (∑ g, x g * ∑ h, (x h + s * b h) * φ g h - F0) - (∑ h, b h * d h + Q2)| ≤
      s * (M + Fintype.card G * Mb * M2) := by
  obtain ⟨R, hRφ, hR⟩ : ∃ R : G → G → ℝ,
      (∀ g h, φ g h = F0 + s * (d h - d g) + s ^ 2 / 2 * D2 g h + R g h) ∧
        ∀ g h, |R g h| ≤ M * s ^ 3 :=
    ⟨fun g h => φ g h - (F0 + s * (d h - d g) + s ^ 2 / 2 * D2 g h), fun g h => by ring, hφ⟩
  obtain ⟨r, hr_def⟩ : ∃ r : G → ℝ, ∀ h, r h = x h + s * b h := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ h, 0 ≤ r h := fun h => by rw [hr_def]; exact hr h
  simp only [← hr_def]
  have hr1 : ∑ h, r h = 1 := by
    simp only [hr_def, sum_add_distrib, ← mul_sum, hb, hx1, mul_zero, add_zero]
  have hin : ∀ g, ∑ h, r h * φ g h = F0 + s * (∑ h, r h * d h - d g) +
      s ^ 2 / 2 * ∑ h, r h * D2 g h + ∑ h, r h * R g h := by
    intro g
    have e : ∀ h, r h * φ g h = F0 * r h + s * (r h * d h) - s * d g * r h +
        s ^ 2 / 2 * (r h * D2 g h) + r h * R g h := by
      intro h
      rw [hRφ]
      ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hr1]
    ring
  have hS1 : ∑ h, r h * d h - ∑ g, x g * d g = s * ∑ h, b h * d h := by
    simp only [hr_def, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    ring
  have hT : ∑ g, x g * ∑ h, r h * D2 g h = 2 * Q2 + s * ∑ g, x g * ∑ h, b h * D2 g h := by
    rw [← hQ2, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    simp only [hr_def, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    ring
  have hA : ∑ g, x g * ∑ h, r h * φ g h - F0 = s ^ 2 * (∑ h, b h * d h + Q2) +
      s ^ 3 / 2 * (∑ g, x g * ∑ h, b h * D2 g h) + ∑ g, x g * ∑ h, r h * R g h := by
    simp only [hin]
    have e : ∀ g, x g * (F0 + s * (∑ h, r h * d h - d g) + s ^ 2 / 2 * ∑ h, r h * D2 g h +
        ∑ h, r h * R g h) = F0 * x g + s * (∑ h, r h * d h) * x g - s * (x g * d g) +
        s ^ 2 / 2 * (x g * ∑ h, r h * D2 g h) + x g * ∑ h, r h * R g h := fun g => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hx1]
    linear_combination s * hS1 + s ^ 2 / 2 * hT
  have hs2 : (s ^ 2)⁻¹ * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hs3 : (s ^ 2)⁻¹ * s ^ 3 = s := by
    rw [show s ^ 3 = s ^ 2 * s by ring, ← mul_assoc, hs2, one_mul]
  have hfin : (s ^ 2)⁻¹ * (∑ g, x g * ∑ h, r h * φ g h - F0) - (∑ h, b h * d h + Q2) =
      s / 2 * (∑ g, x g * ∑ h, b h * D2 g h) + (s ^ 2)⁻¹ * ∑ g, x g * ∑ h, r h * R g h := by
    rw [hA]
    linear_combination (∑ h, b h * d h + Q2) * hs2 +
      (∑ g, x g * ∑ h, b h * D2 g h) / 2 * hs3
  have hV : |∑ g, x g * ∑ h, b h * D2 g h| ≤ Fintype.card G * Mb * M2 := by
    have hin2 : ∀ g, |∑ h, b h * D2 g h| ≤ Fintype.card G * Mb * M2 := by
      intro g
      calc |∑ h, b h * D2 g h| ≤ ∑ h, |b h * D2 g h| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _h : G, Mb * M2 := sum_le_sum fun h _ => by
            rw [abs_mul]
            exact mul_le_mul (hbM h) (hD2M g h) (abs_nonneg _) ((abs_nonneg _).trans (hbM h))
        _ = Fintype.card G * Mb * M2 := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
    calc |∑ g, x g * ∑ h, b h * D2 g h| ≤ ∑ g, |x g * ∑ h, b h * D2 g h| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ g, x g * (Fintype.card G * Mb * M2) := sum_le_sum fun g _ => by
          rw [abs_mul, abs_of_nonneg (hx0 g)]
          exact mul_le_mul_of_nonneg_left (hin2 g) (hx0 g)
      _ = Fintype.card G * Mb * M2 := by rw [← sum_mul, hx1, one_mul]
  have hW : |∑ g, x g * ∑ h, r h * R g h| ≤ M * s ^ 3 := by
    calc |∑ g, x g * ∑ h, r h * R g h| ≤ ∑ g, |x g * ∑ h, r h * R g h| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ g, x g * (M * s ^ 3) := sum_le_sum fun g _ => by
          rw [abs_mul, abs_of_nonneg (hx0 g)]
          refine mul_le_mul_of_nonneg_left ?_ (hx0 g)
          calc |∑ h, r h * R g h| ≤ ∑ h, |r h * R g h| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ h, r h * (M * s ^ 3) := sum_le_sum fun h _ => by
                rw [abs_mul, abs_of_nonneg (hr0 h)]
                exact mul_le_mul_of_nonneg_left (hR g h) (hr0 h)
            _ = M * s ^ 3 := by rw [← sum_mul, hr1, one_mul]
      _ = M * s ^ 3 := by rw [← sum_mul, hx1, one_mul]
  rw [hfin]
  have h1 : |s / 2 * ∑ g, x g * ∑ h, b h * D2 g h| ≤ s / 2 * (Fintype.card G * Mb * M2) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have h2 : |(s ^ 2)⁻¹ * ∑ g, x g * ∑ h, r h * R g h| ≤ M * s := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (s ^ 2)⁻¹ * |∑ g, x g * ∑ h, r h * R g h| ≤ (s ^ 2)⁻¹ * (M * s ^ 3) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = M * s := by rw [show (s ^ 2)⁻¹ * (M * s ^ 3) = M * ((s ^ 2)⁻¹ * s ^ 3) by ring, hs3]
  have hC0 : 0 ≤ (Fintype.card G : ℝ) * Mb * M2 := (abs_nonneg _).trans hV
  have := abs_add_le (s / 2 * ∑ g, x g * ∑ h, b h * D2 g h)
    ((s ^ 2)⁻¹ * ∑ g, x g * ∑ h, r h * R g h)
  nlinarith [mul_nonneg hs.le hC0]

theorem eval_dirDeriv_single_sub (x : Fin KA × Fin KB → ℝ)
    (p : MvPolynomial (Fin KA × Fin KB) ℝ) (g h : Fin KA × Fin KB) :
    eval x (dirDeriv (Pi.single h 1 - Pi.single g 1) p) =
      eval x (pderiv h p) - eval x (pderiv g p) := by
  simp [dirDeriv, sub_mul, Pi.single_apply, sum_sub_distrib]

theorem eval_pderiv_dirDeriv_single_sub (x : Fin KA × Fin KB → ℝ)
    (p : MvPolynomial (Fin KA × Fin KB) ℝ) (a g h : Fin KA × Fin KB) :
    eval x (pderiv a (dirDeriv (Pi.single h 1 - Pi.single g 1) p)) =
      eval x (pderiv a (pderiv h p)) - eval x (pderiv a (pderiv g p)) := by
  simp [dirDeriv, sub_mul, Pi.single_apply, sum_sub_distrib]

theorem sum_mul_sum_mul_eval_dirDeriv_dirDeriv {x : Fin KA × Fin KB → ℝ} (hx1 : ∑ g, x g = 1)
    (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∑ g, x g * ∑ h, x h * eval x (dirDeriv (Pi.single h 1 - Pi.single g 1)
        (dirDeriv (Pi.single h 1 - Pi.single g 1) f)) =
      2 * (∑ g, x g * eval x (pderiv g (pderiv g f)) -
        ∑ g, x g * ∑ h, x h * eval x (pderiv g (pderiv h f))) := by
  obtain ⟨E, hE⟩ : ∃ E : Fin KA × Fin KB → Fin KA × Fin KB → ℝ,
      ∀ a c, E a c = eval x (pderiv a (pderiv c f)) := ⟨_, fun _ _ => rfl⟩
  have hD : ∀ g h, eval x (dirDeriv (Pi.single h 1 - Pi.single g 1)
      (dirDeriv (Pi.single h 1 - Pi.single g 1) f)) = E h h - E h g - (E g h - E g g) := by
    intro g h
    rw [eval_dirDeriv_single_sub, eval_pderiv_dirDeriv_single_sub,
      eval_pderiv_dirDeriv_single_sub, hE, hE, hE, hE]
  simp only [hD, ← hE]
  have h1 : ∑ g, x g * ∑ h, x h * E h h = ∑ h, x h * E h h := by rw [← sum_mul, hx1, one_mul]
  have h2 : ∑ g, x g * ∑ h, x h * E h g = ∑ g, x g * ∑ h, x h * E g h := by
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun g _ => sum_congr rfl fun h _ => by ring
  have h3 : ∑ g, x g * ∑ h, x h * E g g = ∑ g, x g * E g g := by
    refine sum_congr rfl fun g _ => ?_
    rw [← sum_mul, hx1, one_mul]
  have hsplit : ∑ g, x g * ∑ h, x h * (E h h - E h g - (E g h - E g g)) =
      ∑ g, x g * ∑ h, x h * E h h - ∑ g, x g * ∑ h, x h * E h g -
        (∑ g, x g * ∑ h, x h * E g h - ∑ g, x g * ∑ h, x h * E g g) := by
    simp only [mul_sub, sum_sub_distrib]
  rw [hsplit, h1, h2, h3]
  ring

theorem eval_twoLocusGenerator_eq_sum (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (i₀ : Fin KA) (σ : ℝ) (x : Fin KA × Fin KB → ℝ) (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    eval x (twoLocusGenerator θA θB ρ πA πB i₀ σ f) =
      ∑ h, eval x (twoLocusDrift θA θB ρ πA πB i₀ σ h) * eval x (pderiv h f) +
        (∑ g, x g * eval x (pderiv g (pderiv g f)) -
          ∑ g, x g * ∑ h, x h * eval x (pderiv g (pderiv h f))) := by
  rw [twoLocusGenerator_eq_simplexDiffusionOp, simplexDiffusionOp, map_add, add_comm]
  congr 1
  · simp only [map_sum, map_mul]
  · simp only [map_sum, map_mul, map_sub, eval_X, eval_C]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun g _ => ?_
    simp [mul_sub, sub_mul, mul_sum, mul_assoc, sum_sub_distrib]

theorem abs_eval_line_taylor_le {x : Fin KA × Fin KB → ℝ} (hx : x ∈ gameteSimplex KA KB)
    {f : MvPolynomial (Fin KA × Fin KB) ℝ} {g h : Fin KA × Fin KB} {M : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ p ∈ gameteSimplex KA KB ×ˢ Set.Icc (0 : ℝ) 1,
      |eval (p.1 + p.2 • (Pi.single h 1 - Pi.single g 1))
        (dirDeriv (Pi.single h 1 - Pi.single g 1) (dirDeriv (Pi.single h 1 - Pi.single g 1)
          (dirDeriv (Pi.single h 1 - Pi.single g 1) f)))| ≤ M)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |eval (x + s • (Pi.single h 1 - Pi.single g 1)) f -
      (eval x f + s * (eval x (pderiv h f) - eval x (pderiv g f)) +
        s ^ 2 / 2 * eval x (dirDeriv (Pi.single h 1 - Pi.single g 1)
          (dirDeriv (Pi.single h 1 - Pi.single g 1) f)))| ≤ M * s ^ 3 := by
  have ht := abs_polynomial_taylor_two_le (linePoly x (Pi.single h 1 - Pi.single g 1) f) hM
    hs0 (fun t ht => ?_)
  · rw [linePoly_eval, linePoly_eval_zero, derivative_linePoly_eval_zero,
      derivative_derivative_linePoly_eval_zero, eval_dirDeriv_single_sub] at ht
    convert ht using 2
    ring
  · rw [derivative_linePoly, derivative_linePoly, derivative_linePoly, linePoly_eval]
    exact hMb (x, t) ⟨hx, ⟨ht.1, ht.2.trans hs1⟩⟩

noncomputable def moranFreq (N : ℕ) (ω : Fin N → Fin KA × Fin KB) : Fin KA × Fin KB → ℝ :=
  fun g => ((univ.filter fun k => ω k = g).card : ℝ) / N

theorem moranFreq_eq_sum (N : ℕ) (ω : Fin N → Fin KA × Fin KB) (g : Fin KA × Fin KB) :
    moranFreq N ω g = (N : ℝ)⁻¹ * ∑ k, if ω k = g then (1 : ℝ) else 0 := by
  simp only [moranFreq]
  rw [natCast_card_filter, div_eq_inv_mul]

theorem moranFreq_mem_gameteSimplex {N : ℕ} (hN : 0 < N) (ω : Fin N → Fin KA × Fin KB) :
    moranFreq N ω ∈ gameteSimplex KA KB := by
  refine ⟨fun g => by simp only [moranFreq]; positivity, ?_⟩
  simp only [moranFreq_eq_sum, ← mul_sum]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne')

theorem moranFreq_update {N : ℕ} (ω : Fin N → Fin KA × Fin KB) (k : Fin N)
    (h : Fin KA × Fin KB) :
    moranFreq N (Function.update ω k h) =
      moranFreq N ω + (N : ℝ)⁻¹ • (Pi.single h 1 - Pi.single (ω k) 1) := by
  funext g
  have hpt : ∀ l, (if Function.update ω k h l = g then (1 : ℝ) else 0) =
      (if ω l = g then 1 else 0) +
        if l = k then ((Pi.single h 1 : Fin KA × Fin KB → ℝ) g -
          (Pi.single (ω k) 1 : Fin KA × Fin KB → ℝ) g) else 0 := by
    intro l
    by_cases hl : l = k
    · subst hl
      simp only [Function.update_self, Pi.single_apply, ite_true]
      by_cases h1 : h = g
      · subst h1
        by_cases h2 : ω l = h
        · rw [h2]
          simp
        · simp [h2, Ne.symm h2]
      · by_cases h2 : ω l = g
        · rw [h2]
          simp [h1, Ne.symm h1]
        · simp [h1, Ne.symm h1, h2, Ne.symm h2]
    · simp [hl]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, moranFreq_eq_sum]
  rw [sum_congr rfl fun l _ => hpt l, sum_add_distrib, sum_ite_eq']
  simp only [mem_univ, ite_true]
  ring

theorem sum_inv_mul_comp_eq_sum_moranFreq {N : ℕ} (ω : Fin N → Fin KA × Fin KB)
    (Φ : Fin KA × Fin KB → ℝ) :
    ∑ k, (N : ℝ)⁻¹ * Φ (ω k) = ∑ g, moranFreq N ω g * Φ g := by
  have e : ∀ g, moranFreq N ω g * Φ g = ∑ k, if ω k = g then (N : ℝ)⁻¹ * Φ g else 0 := by
    intro g
    rw [moranFreq_eq_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [sum_congr rfl fun g _ => e g, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_ite_eq]
  simp

noncomputable def moranKernel (N : ℕ) (r : (Fin N → Fin KA × Fin KB) → Fin KA × Fin KB → ℝ) :
    Matrix (Fin N → Fin KA × Fin KB) (Fin N → Fin KA × Fin KB) ℝ :=
  fun ω ω' => ∑ k, ∑ h, (N : ℝ)⁻¹ * r ω h * if Function.update ω k h = ω' then 1 else 0

theorem sum_moranKernel_mul (N : ℕ) (r : (Fin N → Fin KA × Fin KB) → Fin KA × Fin KB → ℝ)
    (F : (Fin N → Fin KA × Fin KB) → ℝ) (ω : Fin N → Fin KA × Fin KB) :
    ∑ ω', moranKernel N r ω ω' * F ω' =
      ∑ k, ∑ h, (N : ℝ)⁻¹ * r ω h * F (Function.update ω k h) := by
  simp only [moranKernel, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp

noncomputable def moranRate (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (i₀ : Fin KA)
    (σ : ℝ) (N : ℕ) (x : Fin KA × Fin KB → ℝ) (h : Fin KA × Fin KB) : ℝ :=
  x h + (N : ℝ)⁻¹ * eval x (twoLocusDrift θA θB ρ πA πB i₀ σ h)

theorem sum_moranRate (θA θB ρ : ℝ) {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ) (N : ℕ)
    {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) :
    ∑ h, moranRate θA θB ρ πA πB i₀ σ N x h = 1 := by
  simp only [moranRate, sum_add_distrib, ← mul_sum,
    sum_eval_twoLocusDrift θA θB ρ hπA hπB i₀ σ hx, mul_zero, add_zero, hx]

theorem neg_mul_le_eval_twoLocusDrift {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (i₀ : Fin KA) (σ : ℝ) {x : Fin KA × Fin KB → ℝ} (hx : x ∈ gameteSimplex KA KB)
    (h : Fin KA × Fin KB) :
    -(θA + θB + ρ + |σ|) * x h ≤ eval x (twoLocusDrift θA θB ρ πA πB i₀ σ h) := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases h with ⟨i, j⟩
  have hP : 0 ≤ eval x (margA (KB := KB) i) := by
    simp only [margA, map_sum, eval_X]
    exact sum_nonneg fun _ _ => hx0 _
  have hR : 0 ≤ eval x (margB (KA := KA) j) := by
    simp only [margB, map_sum, eval_X]
    exact sum_nonneg fun _ _ => hx0 _
  have hP0 : 0 ≤ eval x (margA (KB := KB) i₀) := by
    simp only [margA, map_sum, eval_X]
    exact sum_nonneg fun _ _ => hx0 _
  have hP1 : eval x (margA (KB := KB) i₀) ≤ 1 := by
    rw [← hx1]
    simp only [margA, map_sum, eval_X]
    rw [Fintype.sum_prod_type]
    exact single_le_sum (f := fun i => ∑ j, x (i, j)) (fun i _ => sum_nonneg fun j _ => hx0 _)
      (mem_univ i₀)
  have hc : |(if i = i₀ then (1 : ℝ) else 0) - eval x (margA (KB := KB) i₀)| ≤ 1 := by
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  have hσ : -|σ| ≤ σ * ((if i = i₀ then (1 : ℝ) else 0) - eval x (margA (KB := KB) i₀)) :=
    (abs_le.1 ((abs_mul σ _).trans_le (mul_le_of_le_one_right (abs_nonneg σ) hc))).1
  have hsel := mul_le_mul_of_nonneg_left hσ (hx0 (i, j))
  simp only [twoLocusDrift, map_add, map_mul, eval_neutralDrift, eval_C, eval_X, map_sub]
  nlinarith [mul_nonneg hθA (mul_nonneg (hπA0 i) hR), mul_nonneg hθB (mul_nonneg (hπB0 j) hP),
    mul_nonneg hρ (mul_nonneg hP hR)]

theorem moranRate_nonneg {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (i₀ : Fin KA) (σ : ℝ) {N : ℕ} (hN : θA + θB + ρ + |σ| ≤ N) (hN0 : 0 < N)
    {x : Fin KA × Fin KB → ℝ} (hx : x ∈ gameteSimplex KA KB) (h : Fin KA × Fin KB) :
    0 ≤ moranRate θA θB ρ πA πB i₀ σ N x h := by
  have hb := neg_mul_le_eval_twoLocusDrift hθA hθB hρ hπA0 hπB0 i₀ σ hx h
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN0
  have hxh := hx.1 h
  have h1 := mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hNpos.le)
  have h2 : (N : ℝ)⁻¹ * (θA + θB + ρ + |σ|) ≤ 1 :=
    calc (N : ℝ)⁻¹ * (θA + θB + ρ + |σ|) ≤ (N : ℝ)⁻¹ * N :=
          mul_le_mul_of_nonneg_left hN (inv_nonneg.2 hNpos.le)
      _ = 1 := inv_mul_cancel₀ hNpos.ne'
  have h3 := mul_le_of_le_one_left hxh h2
  unfold moranRate
  nlinarith

noncomputable def moranOffset (θA θB ρ σ : ℝ) : ℕ := ⌈θA + θB + ρ + |σ|⌉₊ + 1

theorem moranOffset_pos (θA θB ρ σ : ℝ) (n : ℕ) : 0 < n + moranOffset θA θB ρ σ := by
  unfold moranOffset
  omega

theorem le_moranOffset (θA θB ρ σ : ℝ) (n : ℕ) :
    θA + θB + ρ + |σ| ≤ ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) := by
  have := Nat.le_ceil (θA + θB + ρ + |σ|)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [moranOffset, Nat.cast_add, Nat.cast_one]
  linarith

noncomputable def moranChain {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ) (n : ℕ) :
    FinChain (Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB) where
  P := moranKernel (n + moranOffset θA θB ρ σ)
    (fun ω => moranRate θA θB ρ πA πB i₀ σ (n + moranOffset θA θB ρ σ) (moranFreq _ ω))
  nonneg ω ω' := by
    simp only [moranKernel]
    refine sum_nonneg fun k _ => sum_nonneg fun h _ => mul_nonneg (mul_nonneg ?_ ?_) ?_
    · positivity
    · exact moranRate_nonneg hθA hθB hρ hπA0 hπB0 i₀ σ (le_moranOffset θA θB ρ σ n)
        (moranOffset_pos θA θB ρ σ n)
        (moranFreq_mem_gameteSimplex (moranOffset_pos θA θB ρ σ n) ω) h
    · split_ifs <;> norm_num
  row_sum ω := by
    have := sum_moranKernel_mul _
      (fun ω => moranRate θA θB ρ πA πB i₀ σ (n + moranOffset θA θB ρ σ) (moranFreq _ ω))
      (fun _ => 1) ω
    simp only [mul_one] at this
    rw [this]
    simp only [← mul_sum, sum_moranRate θA θB ρ hπA hπB i₀ σ _
      (moranFreq_mem_gameteSimplex (moranOffset_pos θA θB ρ σ n) ω).2, mul_one, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (moranOffset_pos θA θB ρ σ n).ne')

theorem moranChain_P {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ) (n : ℕ) :
    (moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).P =
      moranKernel (n + moranOffset θA θB ρ σ)
        (fun ω => moranRate θA θB ρ πA πB i₀ σ (n + moranOffset θA θB ρ σ) (moranFreq _ ω)) :=
  rfl

section Chain

variable {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
  {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
  (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ)

theorem moranChain_expect (n : ℕ) (F : (Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB) → ℝ)
    (ω : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB) :
    (moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect F ω =
      ∑ k, ∑ h, ((n + moranOffset θA θB ρ σ : ℕ) : ℝ)⁻¹ *
        moranRate θA θB ρ πA πB i₀ σ (n + moranOffset θA θB ρ σ) (moranFreq _ ω) h *
          F (Function.update ω k h) := by
  rw [FinChain.expect_apply, moranChain_P]
  exact sum_moranKernel_mul _ _ F ω

theorem moranChain_step (n : ℕ) {ω ω' : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB}
    (h : (moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).P ω ω' ≠ 0) (g : Fin KA × Fin KB) :
    |moranFreq _ ω' g - moranFreq _ ω g| ≤ 1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) := by
  obtain ⟨k, h', rfl⟩ : ∃ k h', Function.update ω k h' = ω' := by
    by_contra hne
    simp only [not_exists] at hne
    apply h
    rw [moranChain_P]
    simp only [moranKernel]
    exact sum_eq_zero fun k _ => sum_eq_zero fun h' _ => by simp [hne k h']
  rw [moranFreq_update]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left,
    abs_mul, one_div]
  have hd : |(Pi.single h' 1 : Fin KA × Fin KB → ℝ) g -
      (Pi.single (ω k) 1 : Fin KA × Fin KB → ℝ) g| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) hd

include hθA hθB hρ hπA0 hπB0 hπA hπB in
theorem exists_moran_generator_le_aux (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ c : ℝ, ∀ (N : ℕ), 0 < N → θA + θB + ρ + |σ| ≤ N → ∀ ω : Fin N → Fin KA × Fin KB,
      |(N : ℝ) ^ 2 * ((∑ k, ∑ h, (N : ℝ)⁻¹ * moranRate θA θB ρ πA πB i₀ σ N (moranFreq N ω) h *
          eval (moranFreq N (Function.update ω k h)) f) - eval (moranFreq N ω) f) -
        eval (moranFreq N ω) (twoLocusGenerator θA θB ρ πA πB i₀ σ f)| ≤ c / N := by
  obtain ⟨M3, hM3, hM3b⟩ := exists_nonneg_bound_of_forall
    (S := gameteSimplex KA KB ×ˢ Set.Icc (0 : ℝ) 1)
    (fun (q : (Fin KA × Fin KB) × (Fin KA × Fin KB)) (p : (Fin KA × Fin KB → ℝ) × ℝ) =>
      eval (p.1 + p.2 • (Pi.single q.2 1 - Pi.single q.1 1))
        (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1)
          (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) f))))
    (fun q => exists_bound_eval_line (Pi.single q.2 1 - Pi.single q.1 1)
      (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1)
          (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) f))))
  obtain ⟨M2, hM2, hM2b⟩ := exists_nonneg_bound_of_forall (S := gameteSimplex KA KB)
    (fun (q : (Fin KA × Fin KB) × (Fin KA × Fin KB)) (y : Fin KA × Fin KB → ℝ) =>
      eval y (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1)
        (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) f)))
    (fun q => exists_bound_eval_of_isCompact isCompact_gameteSimplex
      (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1)
        (dirDeriv (Pi.single q.2 1 - Pi.single q.1 1) f)))
  obtain ⟨Mb, hMb, hMbb⟩ := exists_nonneg_bound_of_forall (S := gameteSimplex KA KB)
    (fun (h : Fin KA × Fin KB) (y : Fin KA × Fin KB → ℝ) =>
      eval y (twoLocusDrift θA θB ρ πA πB i₀ σ h))
    (fun h => exists_bound_eval_of_isCompact isCompact_gameteSimplex
      (twoLocusDrift θA θB ρ πA πB i₀ σ h))
  refine ⟨M3 + Fintype.card (Fin KA × Fin KB) * Mb * M2, fun N hN0 hKN ω => ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN0
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN0
  have hs0 : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 hNpos
  have hs1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hE : (∑ k, ∑ h, (N : ℝ)⁻¹ * moranRate θA θB ρ πA πB i₀ σ N (moranFreq N ω) h *
      eval (moranFreq N (Function.update ω k h)) f) =
      ∑ g, moranFreq N ω g * ∑ h, moranRate θA θB ρ πA πB i₀ σ N (moranFreq N ω) h *
        eval (moranFreq N ω + (N : ℝ)⁻¹ • (Pi.single h 1 - Pi.single g 1)) f := by
    refine Eq.trans ?_ (sum_inv_mul_comp_eq_sum_moranFreq ω _)
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [moranFreq_update, mul_assoc]
  have hx := moranFreq_mem_gameteSimplex hN0 ω
  have hr := fun h => moranRate_nonneg hθA hθB hρ hπA0 hπB0 i₀ σ hKN hN0 hx h
  rw [hE, eval_twoLocusGenerator_eq_sum]
  generalize moranFreq N ω = x at hx hr ⊢
  simp only [moranRate] at hr ⊢
  have hφ : ∀ g h, |eval (x + (N : ℝ)⁻¹ • (Pi.single h 1 - Pi.single g 1)) f -
      (eval x f + (N : ℝ)⁻¹ * (eval x (pderiv h f) - eval x (pderiv g f)) +
        (N : ℝ)⁻¹ ^ 2 / 2 * eval x (dirDeriv (Pi.single h 1 - Pi.single g 1)
          (dirDeriv (Pi.single h 1 - Pi.single g 1) f)))| ≤ M3 * (N : ℝ)⁻¹ ^ 3 :=
    fun g h => abs_eval_line_taylor_le hx hM3 (fun p hp => hM3b (g, h) p hp) hs0.le hs1
  have key := abs_moranStep_sub_le (x := x)
    (b := fun h => eval x (twoLocusDrift θA θB ρ πA πB i₀ σ h))
    (d := fun h => eval x (pderiv h f))
    (D2 := fun g h => eval x (dirDeriv (Pi.single h 1 - Pi.single g 1)
      (dirDeriv (Pi.single h 1 - Pi.single g 1) f)))
    (φ := fun g h => eval (x + (N : ℝ)⁻¹ • (Pi.single h 1 - Pi.single g 1)) f)
    (s := (N : ℝ)⁻¹) (F0 := eval x f)
    (Q2 := ∑ g, x g * eval x (pderiv g (pderiv g f)) -
      ∑ g, x g * ∑ h, x h * eval x (pderiv g (pderiv h f)))
    (M := M3) (Mb := Mb) (M2 := M2) hx.1 hx.2
    (sum_eval_twoLocusDrift θA θB ρ hπA hπB i₀ σ hx.2) hs0 hr
    (sum_mul_sum_mul_eval_dirDeriv_dirDeriv hx.2 f) hφ (fun h => hMbb h x hx)
    (fun g h => hM2b (g, h) x hx)
  rw [inv_pow, inv_inv] at key
  rw [div_eq_inv_mul]
  exact key

theorem exists_moranChain_generator_le (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ c : ℝ, ∀ (n : ℕ) (ω : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB),
      |((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 *
          ((moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect
              (fun ω' => eval (moranFreq _ ω') f) ω - eval (moranFreq _ ω) f) -
        eval (moranFreq _ ω) (twoLocusGenerator θA θB ρ πA πB i₀ σ f)| ≤
        c / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) := by
  obtain ⟨c, hc⟩ := exists_moran_generator_le_aux hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ f
  refine ⟨c, fun n ω => ?_⟩
  rw [moranChain_expect]
  exact hc _ (moranOffset_pos θA θB ρ σ n) (le_moranOffset θA θB ρ σ n) ω

theorem exists_moranChain_drift_le :
    ∃ c : ℝ, ∀ (n : ℕ) (ω : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB)
      (g : Fin KA × Fin KB),
      |(moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect
          (fun ω' => moranFreq _ ω' g) ω - moranFreq _ ω g| ≤
        c / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 := by
  have hgen : ∀ g : Fin KA × Fin KB, ∃ c : ℝ, ∀ (n : ℕ)
      (ω : Fin (n + moranOffset θA θB ρ σ) → Fin KA × Fin KB),
      |((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 *
          ((moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect
              (fun ω' => moranFreq _ ω' g) ω - moranFreq _ ω g)| ≤ c := by
    intro g
    obtain ⟨c1, hc1⟩ := exists_moranChain_generator_le hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ (X g)
    obtain ⟨C, hC⟩ := exists_bound_eval_of_isCompact isCompact_gameteSimplex
      (twoLocusGenerator θA θB ρ πA πB i₀ σ (X g))
    refine ⟨C + |c1|, fun n ω => ?_⟩
    have h1 := hc1 n ω
    have h2 := hC _ (moranFreq_mem_gameteSimplex (moranOffset_pos θA θB ρ σ n) ω)
    simp only [eval_X] at h1
    have hN1 : (1 : ℝ) ≤ ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) :=
      Nat.one_le_cast.2 (moranOffset_pos θA θB ρ σ n)
    have h3 : c1 / ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ≤ |c1| :=
      (div_le_div_of_nonneg_right (le_abs_self c1) (by positivity)).trans
        (div_le_self (abs_nonneg _) hN1)
    set A := ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 *
          ((moranChain hθA hθB hρ hπA0 hπB0 hπA hπB i₀ σ n).expect
              (fun ω' => moranFreq _ ω' g) ω - moranFreq _ ω g)
    set L := eval (moranFreq _ ω) (twoLocusGenerator θA θB ρ πA πB i₀ σ (X g))
    have h4 := abs_add_le (A - L) L
    rw [sub_add_cancel] at h4
    linarith
  choose c hc using hgen
  refine ⟨∑ g, |c g|, fun n ω g => ?_⟩
  have h1 := hc g n ω
  have hNpos : (0 : ℝ) < ((n + moranOffset θA θB ρ σ : ℕ) : ℝ) ^ 2 := by
    have := moranOffset_pos θA θB ρ σ n
    positivity
  rw [abs_mul, abs_of_pos hNpos] at h1
  rw [le_div_iff₀ hNpos, mul_comm]
  exact h1.trans ((le_abs_self _).trans
    (single_le_sum (f := fun g => |c g|) (fun g _ => abs_nonneg _) (mem_univ g)))

end Chain

end Rhone.Diffusion
