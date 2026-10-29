/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FullPanLaw
public import Rhone.Statistics.Identifiability.ZeroClockDynamics

/-! # Uniqueness for the unrestricted pre-merger ODE and recombination-gauge sufficiency -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def panPreEnergy (d r u : ℝ) : ℝ :=
  d ^ 2 + (d + r / 2) ^ 2 + (d + r + u) ^ 2

theorem panPreEnergy_derivative (rate recomb D R U : ℝ → ℝ)
    (he : PanPreEquations rate recomb D R U) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => panPreEnergy (D s) (R s) (U s))
      (-rate t * (4 * (D t - (D t + R t / 2)) ^ 2 + (D t - (D t + R t + U t)) ^ 2 +
        2 * ((D t + R t / 2) - (D t + R t + U t)) ^ 2 + (D t) ^ 2 +
        4 * (D t + R t / 2) ^ 2 + (D t + R t + U t) ^ 2) -
        recomb t * (4 * (D t) ^ 2 + 2 * (D t + R t / 2) ^ 2)) t := by
  rcases he t ht with ⟨hd, hr, hu⟩
  convert! ((hd.pow 2).add ((hd.add (hr.div_const 2)).pow 2)).add
    (((hd.add hr).add hu).pow 2) using 1
  simp only [Pi.add_apply]
  ring

theorem panPreEquations_unique (rate recomb D₁ R₁ U₁ D₂ R₂ U₂ : ℝ → ℝ)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (he₁ : PanPreEquations rate recomb D₁ R₁ U₁)
    (he₂ : PanPreEquations rate recomb D₂ R₂ U₂)
    (hzero : D₁ 0 = D₂ 0 ∧ R₁ 0 = R₂ 0 ∧ U₁ 0 = U₂ 0) :
    EqOn D₁ D₂ (Ici 0) ∧ EqOn R₁ R₂ (Ici 0) ∧ EqOn U₁ U₂ (Ici 0) := by
  let d := fun t => D₁ t - D₂ t
  let r := fun t => R₁ t - R₂ t
  let u := fun t => U₁ t - U₂ t
  have he : PanPreEquations rate recomb d r u := by
    intro t ht
    rcases he₁ t ht with ⟨hd₁, hr₁, hu₁⟩
    rcases he₂ t ht with ⟨hd₂, hr₂, hu₂⟩
    refine ⟨?_, ?_, ?_⟩
    · convert! hd₁.sub hd₂ using 1
      dsimp [d, r]
      ring
    · convert! hr₁.sub hr₂ using 1
      dsimp [d, r, u]
      ring
    · convert! hu₁.sub hu₂ using 1
      dsimp [r, u]
      ring
  let e := fun t => panPreEnergy (d t) (r t) (u t)
  let edot := fun t =>
    -rate t * (4 * (d t - (d t + r t / 2)) ^ 2 + (d t - (d t + r t + u t)) ^ 2 +
      2 * ((d t + r t / 2) - (d t + r t + u t)) ^ 2 + (d t) ^ 2 +
      4 * (d t + r t / 2) ^ 2 + (d t + r t + u t) ^ 2) -
      recomb t * (4 * (d t) ^ 2 + 2 * (d t + r t / 2) ^ 2)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt e (edot t) t :=
    fun t ht => panPreEnergy_derivative rate recomb d r u he t ht
  have hsign : ∀ t, 0 ≤ t → edot t ≤ 0 := by
    intro t ht
    dsimp [edot]
    have hrt := hr t ht
    have hρt := hρ t ht
    have ha : 0 ≤ rate t * (4 * (d t - (d t + r t / 2)) ^ 2 + (d t - (d t + r t + u t)) ^ 2 +
      2 * ((d t + r t / 2) - (d t + r t + u t)) ^ 2 + (d t) ^ 2 +
      4 * (d t + r t / 2) ^ 2 + (d t + r t + u t) ^ 2) := by positivity
    have hb : 0 ≤ recomb t * (4 * (d t) ^ 2 + 2 * (d t + r t / 2) ^ 2) := by positivity
    nlinarith
  have ha : AntitoneOn e (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hsign t (interior_subset ht))
  have hz : e 0 = 0 := by simp [e, panPreEnergy, d, r, u, hzero.1, hzero.2.1, hzero.2.2]
  have hall : ∀ t, 0 ≤ t → d t = 0 ∧ r t = 0 ∧ u t = 0 := by
    intro t ht
    have hh := ha self_mem_Ici ht ht
    rw [hz] at hh
    change (d t) ^ 2 + (d t + r t / 2) ^ 2 + (d t + r t + u t) ^ 2 ≤ 0 at hh
    have hd : d t = 0 := by nlinarith [sq_nonneg (d t + r t / 2), sq_nonneg (d t + r t + u t)]
    have hrt : r t = 0 := by rw [hd] at hh; nlinarith [sq_nonneg (0 + r t + u t)]
    have hu : u t = 0 := by rw [hd, hrt] at hh; nlinarith
    exact ⟨hd, hrt, hu⟩
  exact ⟨fun t ht => sub_eq_zero.mp (hall t ht).1,
    fun t ht => sub_eq_zero.mp (hall t ht).2.1,
    fun t ht => sub_eq_zero.mp (hall t ht).2.2⟩

noncomputable def panGaugeD (z d : ℝ) : ℝ := z ^ 2 * d
noncomputable def panGaugeR (z d r : ℝ) : ℝ := z * r + 2 * z * (1 - z) * d
noncomputable def panGaugeU (z d r u : ℝ) : ℝ := u + (1 - z) * r + (1 - z) ^ 2 * d

theorem panGauge_derivatives (rate ρ₁ ρ₂ z D R U : ℝ → ℝ) (t : ℝ)
    (hz : HasDerivAt z (-(ρ₂ t - ρ₁ t) * z t) t)
    (hd : HasDerivAt D (-(rate t + 2 * ρ₁ t) * D t + rate t * R t) t)
    (hr : HasDerivAt R (2 * ρ₁ t * D t - (3 * rate t + ρ₁ t) * R t + 4 * rate t * U t) t)
    (hu : HasDerivAt U (ρ₁ t * R t - 6 * rate t * U t) t)
    (hc : rate t = 0 ∨ z t = 1) :
    HasDerivAt (fun s => panGaugeD (z s) (D s))
      (-(rate t + 2 * ρ₂ t) * panGaugeD (z t) (D t) +
        rate t * panGaugeR (z t) (D t) (R t)) t ∧
    HasDerivAt (fun s => panGaugeR (z s) (D s) (R s))
      (2 * ρ₂ t * panGaugeD (z t) (D t) -
        (3 * rate t + ρ₂ t) * panGaugeR (z t) (D t) (R t) +
        4 * rate t * panGaugeU (z t) (D t) (R t) (U t)) t ∧
    HasDerivAt (fun s => panGaugeU (z s) (D s) (R s) (U s))
      (ρ₂ t * panGaugeR (z t) (D t) (R t) -
        6 * rate t * panGaugeU (z t) (D t) (R t) (U t)) t := by
  refine ⟨?_, ?_, ?_⟩
  · convert! (hz.pow 2).mul hd using 1
    simp only [panGaugeD, panGaugeR, Pi.pow_apply]
    rcases hc with hc | hc <;> rw [hc] <;> ring
  · convert! (hz.mul hr).add (((hz.const_mul 2).mul (hz.const_sub 1)).mul hd) using 1
    simp only [panGaugeD, panGaugeR, panGaugeU, Pi.mul_apply]
    rcases hc with hc | hc <;> rw [hc] <;> ring
  · convert! (hu.add ((hz.const_sub 1).mul hr)).add
      (((hz.const_sub 1).pow 2).mul hd) using 1
    simp only [panGaugeR, panGaugeU, Pi.pow_apply]
    rcases hc with hc | hc <;> rw [hc] <;> ring

theorem panPreModel_gauge_states (rate h : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hzero : h 0 = 0)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt h (Q.recomb t - P.recomb t) t)
    (hsupport : ∀ t, 0 ≤ t → 0 < rate t → h t = 0) :
    EqOn Q.D (fun t => panGaugeD (Real.exp (-h t)) (P.D t)) (Ici 0) ∧
    EqOn Q.R (fun t => panGaugeR (Real.exp (-h t)) (P.D t) (P.R t)) (Ici 0) ∧
    EqOn Q.U (fun t => panGaugeU (Real.exp (-h t)) (P.D t) (P.R t) (P.U t)) (Ici 0) := by
  let z := fun t => Real.exp (-h t)
  have hcompat : ∀ t, 0 ≤ t → rate t = 0 ∨ z t = 1 := by
    intro t ht
    by_cases hh : rate t = 0
    · exact Or.inl hh
    · right
      have hp : 0 < rate t := lt_of_le_of_ne (hr t ht) (Ne.symm hh)
      simp [z, hsupport t ht hp]
  have he : PanPreEquations rate Q.recomb
      (fun t => panGaugeD (z t) (P.D t))
      (fun t => panGaugeR (z t) (P.D t) (P.R t))
      (fun t => panGaugeU (z t) (P.D t) (P.R t) (P.U t)) := by
    intro t ht
    exact panGauge_derivatives rate P.recomb Q.recomb z P.D P.R P.U t
      (exponential_clock_derivative h _ t (hderiv t ht))
      (P.equations t ht).1 (P.equations t ht).2.1 (P.equations t ht).2.2
      (hcompat t ht)
  apply panPreEquations_unique rate Q.recomb Q.D Q.R Q.U _ _ _ hr
    Q.recomb_nonneg Q.equations he
  simp [z, hzero, panGaugeD, panGaugeR, panGaugeU, P.initial, Q.initial]

theorem panPreModel_gauge_law (rate H h : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hzero : h 0 = 0)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt h (Q.recomb t - P.recomb t) t)
    (hsupport : ∀ t, 0 ≤ t → 0 < rate t → h t = 0) :
    P.law H = Q.law H := by
  obtain ⟨hd, hR, hu⟩ := panPreModel_gauge_states rate h P Q hr hzero hderiv hsupport
  apply clockJointLaw_congr_fluxes
  · intro t ht
    change rate t * P.D t = rate t * Q.D t
    have ht0 : 0 ≤ t := ht.le
    by_cases hz : rate t = 0
    · simp [hz]
    · have hp : 0 < rate t := lt_of_le_of_ne (hr t ht.le) (Ne.symm hz)
      rw [hd ht0]
      simp [hsupport t ht.le hp, panGaugeD]
  · intro t ht
    change rate t * (P.R t + P.U t) = rate t * (Q.R t + Q.U t)
    have ht0 : 0 ≤ t := ht.le
    by_cases hz : rate t = 0
    · simp [hz]
    · have hp : 0 < rate t := lt_of_le_of_ne (hr t ht.le) (Ne.symm hz)
      rw [hR ht0, hu ht0]
      simp [hsupport t ht.le hp, panGaugeR, panGaugeU]

end Rhone.Statistics.Identifiability
