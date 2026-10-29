/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.DiploidSelection
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Habitat soft selection and protected polymorphism

Source: novak2011, eq. 3b. -/
@[expose] public section
namespace Rhone.Dynamics
open Finset Filter Topology Set
variable {D : Type*} [Fintype D]
/-- Source: novak2011, eq. 3b. -/
noncomputable def leveneStep (w a b c : D → ℝ) (p : ℝ) : ℝ :=
  ∑ d, w d * selStep (a d) (b d) (c d) p
/-- Source: novak2011, eq. 3b. -/
theorem levene_zero (w a b c : D → ℝ) (_hw : ∀ d, 0 ≤ w d)
    (_hsum : ∑ d, w d = 1) (_ha : ∀ d, 0 < a d) (_hb : ∀ d, 0 < b d)
    (_hc : ∀ d, 0 < c d) : leveneStep w a b c 0 = 0 := by
  simp [leveneStep, selStep]
/-- Source: novak2011, eq. 3b. -/
theorem levene_one (w a b c : D → ℝ) (_hw : ∀ d, 0 ≤ w d)
    (hsum : ∑ d, w d = 1) (ha : ∀ d, 0 < a d) (_hb : ∀ d, 0 < b d)
    (_hc : ∀ d, 0 < c d) : leveneStep w a b c 1 = 1 := by
  have hsel : ∀ d, selStep (a d) (b d) (c d) 1 = 1 := by
    intro d
    simp [selStep, meanFit, ne_of_gt (ha d)]
  simp only [leveneStep, hsel, mul_one, hsum]
/-- Source: novak2011, eq. 3b. -/
theorem levene_mem_Icc (w a b c : D → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsum : ∑ d, w d = 1) (ha : ∀ d, 0 < a d) (hb : ∀ d, 0 < b d)
    (hc : ∀ d, 0 < c d) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    leveneStep w a b c p ∈ Set.Icc 0 1 := by
  have hsel : ∀ d, selStep (a d) (b d) (c d) p ∈ Set.Icc 0 1 := by
    intro d
    have hM := meanFit_pos (ha d) (hb d) (hc d) hp.1 hp.2
    have hpc : 0 ≤ p*(1-p)*b d := mul_nonneg (mul_nonneg hp.1 (by linarith [hp.2])) (hb d).le
    have hcc : 0 ≤ (1-p)^2*c d := mul_nonneg (sq_nonneg _) (hc d).le
    constructor
    · exact div_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (ha d).le) hpc) hM.le
    · apply (div_le_one hM).mpr
      unfold meanFit
      nlinarith
  constructor
  · exact sum_nonneg fun d _ => mul_nonneg (hw d) (hsel d).1
  · calc
      leveneStep w a b c p ≤ ∑d,w d := sum_le_sum fun d _ =>
        mul_le_of_le_one_right (hw d) (hsel d).2
      _ = 1 := hsum
private theorem sel_derivative (a b c p : ℝ) (hM : meanFit a b c p ≠ 0) :
    HasDerivAt (selStep a b c)
      (((2*p*a+(1-2*p)*b)*meanFit a b c p-
        (p^2*a+p*(1-p)*b)*(2*p*a+2*(1-2*p)*b-2*(1-p)*c)) /
          (meanFit a b c p)^2) p := by
  have hi := hasDerivAt_id p
  have hj : HasDerivAt (fun x : ℝ => 1-x) (-1) p := hi.const_sub 1
  have hn := ((hi.pow 2).mul_const a).add ((hi.mul hj).mul_const b)
  have hd := (((hi.pow 2).mul_const a).add
    (((hi.mul hj).const_mul 2).mul_const b)).add ((hj.pow 2).mul_const c)
  have hn' : HasDerivAt (fun q : ℝ => q^2*a+q*(1-q)*b)
      (2*p*a+(1-2*p)*b) p := by
    convert hn using 1
    · funext q
      rfl
    · simp only [id_eq, show (2:ℕ)-1=1 by decide, pow_one, Nat.cast_ofNat, mul_one, one_mul]
      ring
  have hd' : HasDerivAt (meanFit a b c)
      (2*p*a+2*(1-2*p)*b-2*(1-p)*c) p := by
    convert hd using 1
    · funext q
      simp only [meanFit, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    · simp only [id_eq]
      simp only [show (2:ℕ)-1=1 by decide, pow_one, Nat.cast_ofNat, mul_one, one_mul]
      ring
  exact hn'.div hd' hM

/--
Source: novak2011, eq. (3b), Lemma 2.3; burger2013_migration_selection, sec. 4.1, eq. (4.29), sec.
5.3. -/
theorem levene_deriv_zero (w a b c : D → ℝ) (_hw : ∀ d, 0 ≤ w d)
    (_hsum : ∑ d, w d = 1) (_ha : ∀ d, 0 < a d) (_hb : ∀ d, 0 < b d)
    (hc : ∀ d, 0 < c d) : HasDerivAt (leveneStep w a b c)
    (∑ d, w d * b d / c d) 0 := by
  have hd : ∀d, HasDerivAt (selStep (a d) (b d) (c d)) (b d/c d) 0 := by
    intro d
    have hM : meanFit (a d) (b d) (c d) 0 ≠ 0 := by
      simpa [meanFit] using (ne_of_gt (hc d))
    convert sel_derivative (a d) (b d) (c d) 0 hM using 1
    simp only [meanFit, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero,
      sub_zero, one_pow, mul_one, zero_add, add_zero]
    field_simp
  convert HasDerivAt.fun_sum (fun d (_ : d ∈ (univ : Finset D)) => (hd d).const_mul (w d)) using 1
  · rfl
  · apply sum_congr rfl
    intro d hd
    ring

/--
Source: novak2011, eq. (3b), Lemma 2.3; burger2013_migration_selection, sec. 4.1, eq. (4.29), sec.
5.3. -/
theorem levene_deriv_one (w a b c : D → ℝ) (_hw : ∀ d, 0 ≤ w d)
    (_hsum : ∑ d, w d = 1) (ha : ∀ d, 0 < a d) (_hb : ∀ d, 0 < b d)
    (_hc : ∀ d, 0 < c d) : HasDerivAt (leveneStep w a b c)
    (∑ d, w d * b d / a d) 1 := by
  have hd : ∀d, HasDerivAt (selStep (a d) (b d) (c d)) (b d/a d) 1 := by
    intro d
    have hM : meanFit (a d) (b d) (c d) 1 ≠ 0 := by
      simpa [meanFit] using (ne_of_gt (ha d))
    convert sel_derivative (a d) (b d) (c d) 1 hM using 1
    simp only [meanFit, one_pow, one_mul, sub_self, mul_zero, zero_mul,
      zero_pow (by decide : 2 ≠ 0), add_zero]
    field_simp
    ring
  convert HasDerivAt.fun_sum (fun d (_ : d ∈ (univ : Finset D)) => (hd d).const_mul (w d)) using 1
  · rfl
  · apply sum_congr rfl
    intro d hd
    ring

/-- Source: burger2013_migration_selection, sec. 4.1, eq. (4.29), sec. 5.3. -/
theorem levene_protected_fixed (w a b c : D → ℝ) (hw : ∀ d, 0 ≤ w d)
    (hsum : ∑ d, w d = 1) (ha : ∀ d, 0 < a d) (hb : ∀ d, 0 < b d)
    (hc : ∀ d, 0 < c d)
    (h0 : 1 < ∑ d, w d * b d / c d)
    (h1 : 1 < ∑ d, w d * b d / a d) :
    ∃ p ∈ Set.Ioo 0 1, leveneStep w a b c p = p := by
  let g : ℝ → ℝ := fun p=>leveneStep w a b c p-p
  have hg0 : g 0=0 := by simp [g, levene_zero w a b c hw hsum ha hb hc]
  have hg1 : g 1=0 := by simp [g, levene_one w a b c hw hsum ha hb hc]
  have hd0 := (levene_deriv_zero w a b c hw hsum ha hb hc).sub (hasDerivAt_id 0)
  have hd1 := (levene_deriv_one w a b c hw hsum ha hb hc).sub (hasDerivAt_id 1)
  have hr := hd0.tendsto_slope_zero_right.eventually
    (Ioi_mem_nhds (show 0 < (∑d,w d*b d/c d)-1 by linarith))
  have hl := hd1.tendsto_slope_zero_left.eventually
    (Ioi_mem_nhds (show 0 < (∑d,w d*b d/a d)-1 by linarith))
  have hsmall : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < 1/3 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1/3))
  have hlarge : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Iio 0), -1/3 < u :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : -(1:ℝ)/3<0))
  obtain ⟨u, hus, hu0, hu1⟩ := (hr.and (eventually_mem_nhdsWithin.and hsmall)).exists
  obtain ⟨v, hvs, hv0, hv1⟩ := (hl.and (eventually_mem_nhdsWithin.and hlarge)).exists
  have hu : 0 < u := hu0
  have hv : v < 0 := hv0
  have hgu : 0 < g u := by
    change 0 < u⁻¹*(g (0+u)-g 0) at hus
    rw [zero_add, hg0, sub_zero] at hus
    exact pos_of_mul_pos_right hus (inv_nonneg.mpr hu.le)
  have hgv : g (1+v) < 0 := by
    change 0 < v⁻¹*(g (1+v)-g 1) at hvs
    rw [hg1, sub_zero] at hvs
    have : v⁻¹ < 0 := inv_lt_zero.mpr hv
    nlinarith
  have hcG : ContinuousOn g (Set.Icc u (1+v)) := by
    intro p hp
    have hpI : p∈Set.Icc 0 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
    have hdc := HasDerivAt.fun_sum (fun d (_ : d∈(univ:Finset D)) =>
      (sel_derivative (a d) (b d) (c d) p
        (ne_of_gt (meanFit_pos (ha d) (hb d) (hc d) hpI.1 hpI.2))).const_mul (w d))
    exact (hdc.continuousAt.sub continuousAt_id).continuousWithinAt
  obtain ⟨p, hp, hgp⟩ := intermediate_value_Icc' (show u≤1+v by linarith) hcG
    (show (0:ℝ)∈Set.Icc (g (1+v)) (g u) from ⟨hgv.le,hgu.le⟩)
  refine ⟨p, ⟨by linarith [hp.1],by linarith [hp.2]⟩, ?_⟩
  change leveneStep w a b c p-p=0 at hgp
  linarith

end Rhone.Dynamics
