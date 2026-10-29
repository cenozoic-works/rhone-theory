/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.SegregatingExposure
public import Rhone.Coalescent.KingmanClockMoments

/-!
# The Laplace transform of the total tree length of the Kingman coalescent

Source: watterson1975, p. 258, eq. (1.3a); kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics
open scoped NNReal ENNReal

theorem integral_expMeasure_one (g : ℝ → ℝ) :
    ∫ t, g t ∂expMeasure 1 = ∫ t in Set.Ioi 0, Real.exp (-t) * g t := by
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hlt : ∀ᵐ t : ℝ, gammaPDF 1 1 t < ⊤ := ae_of_all _ fun t => by
    rw [gammaPDF_eq]
    exact ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hm hlt,
    ← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  change (gammaPDF 1 1 t).toReal • g t = _
  rw [gammaPDF_eq]
  by_cases ht : 0 ≤ t
  · have hmem : t ∈ Set.Ici (0 : ℝ) := ht
    simp only [ht, ↓reduceIte]
    rw [Set.indicator_of_mem hmem, ENNReal.toReal_ofReal (by positivity)]
    simp [Real.Gamma_one]
  · have hmem : t ∉ Set.Ici (0 : ℝ) := ht
    simp only [ht, ↓reduceIte]
    rw [Set.indicator_of_notMem hmem]
    simp

theorem integral_pow_mul_exp_expMeasure_one {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    ∫ t, (max 0 t) ^ k * Real.exp (-(a * max 0 t)) ∂expMeasure 1 =
      (k.factorial : ℝ) / (1 + a) ^ (k + 1) := by
  rw [integral_expMeasure_one]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := 1 + a)
    (by positivity) (by positivity)
  rw [add_sub_cancel_right] at h
  have hc : ∫ t in Set.Ioi 0, Real.exp (-t) * ((max 0 t) ^ k * Real.exp (-(a * max 0 t))) =
      ∫ t in Set.Ioi 0, t ^ (k : ℝ) * Real.exp (-((1 + a) * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [max_eq_right ht'.le, Real.rpow_natCast]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [hc, h, Real.Gamma_nat_eq_factorial,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    one_div, inv_pow]
  ring

theorem kingmanFiniteLength_ae_eq_clock_sum (n : ℕ) :
    ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h =
        ∑ k : Fin (n - 1), 2 / ((n : ℝ) - 1 - (k : ℕ)) * max 0 (h.2 k) := by
  have hae : ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k : ℕ, (h.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown_general n)
  filter_upwards [hae] with h hh
  unfold kingmanFiniteReward
  apply Finset.sum_congr rfl
  intro k _
  have hk := k.isLt
  have hc : (h.1 k.val).parts.card = n - k.val := by
    rw [hh]
    omega
  have hnot : h.1 k.val ∉ coalescedPartitions (Fin n) := by
    rw [mem_coalescedPartitions, hc]
    omega
  simp only [hnot, ↓reduceIte]
  rw [RateChain.holdTime, partitionChain_rate, hc]
  have hcast : ((n - k.val : ℕ) : ℝ) = (n : ℝ) - k.val := by
    rw [Nat.cast_sub (by omega)]
  have hlt : ((k.val : ℝ) + 1) < n := by exact_mod_cast (by omega : k.val + 1 < n)
  have hpos : (0 : ℝ) < (n : ℝ) - 1 - k.val := by linarith
  have hpos' : (0 : ℝ) < (n : ℝ) - k.val := by linarith
  have hrate : ((coalRate (n - k.val) : ℚ) : ℝ) =
      ((n : ℝ) - k.val) * ((n : ℝ) - 1 - k.val) / 2 := by
    unfold coalRate
    push_cast [hcast]
    ring
  rw [hrate, hcast]
  clear hrate
  have hr : (0 : ℝ) < ((n : ℝ) - k.val) * ((n : ℝ) - 1 - k.val) / 2 := by positivity
  rcases le_total 0 (h.2 k.val) with he | he
  · rw [max_eq_right he, max_eq_right (div_nonneg he hr.le)]
    field_simp
  · rw [max_eq_left he, max_eq_left (div_nonpos_of_nonpos_of_nonneg he hr.le)]
    ring

theorem partitionTreeLength_toReal_ae (n : ℕ) :
    ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      (partitionTreeLength h).toReal =
        kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h := by
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n
    (fun π => (π.parts.card : ℝ)) (fun π => Nat.cast_nonneg π.parts.card)] with h hh
  have hnn := kingmanFiniteReward_nonneg n (fun π => (π.parts.card : ℝ))
    (fun π => Nat.cast_nonneg π.parts.card) h
  unfold partitionTreeLength
  rw [hh]
  exact ENNReal.toReal_ofReal hnn

theorem integral_jumpHoldLaw_clock (n : ℕ) {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) :
    ∫ p, G p.2 ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = ∫ e, G e ∂clockLaw := by
  have hmap : ((partitionChain (Fin n)).jumpHoldLaw ⊥).map Prod.snd = clockLaw := by
    rw [RateChain.jumpHoldLaw, Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hmap, integral_map measurable_snd.aemeasurable hG.aestronglyMeasurable]

theorem integral_clockLaw_eval (k : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ e, g (e k) ∂clockLaw = ∫ t, g t ∂expMeasure 1 := by
  have hmap : clockLaw.map (fun e : ℕ → ℝ => e k) = expMeasure 1 :=
    Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) k
  rw [← hmap, integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable]

/-- Source: watterson1975, p. 258, eq. (1.3a). -/
theorem laplace_partitionTreeLength (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ p, Real.exp (-(s * (partitionTreeLength p).toReal))
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + 2 * s) := by
  have h1 : ∫ p, Real.exp (-(s * (partitionTreeLength p).toReal))
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      ∫ p, (fun e : ℕ → ℝ => ∏ k : Fin (n - 1),
        Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 (e k)))) p.2
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    apply integral_congr_ae
    filter_upwards [partitionTreeLength_toReal_ae n,
      kingmanFiniteLength_ae_eq_clock_sum n] with p hp1 hp2
    rw [hp1, hp2, ← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h1, integral_jumpHoldLaw_clock n (G := fun e : ℕ → ℝ => ∏ k : Fin (n - 1),
    Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 (e k)))) (by fun_prop)]
  have hind : iIndepFun (fun (k : Fin (n - 1)) (e : ℕ → ℝ) => e k.val) clockLaw :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ => id)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_prod_comp (𝕜 := ℝ)
    (f := fun (k : Fin (n - 1)) (t : ℝ) =>
      Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 t)))
    (fun k => (measurable_pi_apply k.val).aemeasurable)
    (fun k => (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 t))).aestronglyMeasurable)
  simp only [Finset.prod_apply, Function.comp_apply] at hprod
  rw [hprod]
  have hfac : ∀ k : Fin (n - 1),
      ∫ e : ℕ → ℝ, Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 (e k.val)))
        ∂clockLaw = ((n : ℝ) - 1 - (k : ℕ)) / (((n : ℝ) - 1 - (k : ℕ)) + 2 * s) := by
    intro k
    have hlt : ((k.val : ℝ) + 1) < n := by exact_mod_cast (by omega : k.val + 1 < n)
    have hpos : (0 : ℝ) < (n : ℝ) - 1 - k.val := by linarith
    rw [integral_clockLaw_eval k.val (g := fun t : ℝ =>
      Real.exp (-(s * (2 / ((n : ℝ) - 1 - (k : ℕ))) * max 0 t))) (by fun_prop)]
    have h := integral_pow_mul_exp_expMeasure_one
      (a := s * (2 / ((n : ℝ) - 1 - (k : ℕ)))) (by positivity) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
    rw [h]
    field_simp
  rw [Finset.prod_congr rfl (fun k _ => hfac k),
    Fin.prod_univ_eq_prod_range
      (fun k : ℕ => ((n : ℝ) - 1 - k) / (((n : ℝ) - 1 - k) + 2 * s)) (n - 1)]
  apply Finset.prod_nbij' (fun k => n - 1 - k) (fun j => n - 1 - j)
  · intro k hk
    rw [mem_range] at hk
    rw [mem_Icc]
    omega
  · intro j hj
    rw [mem_Icc] at hj
    rw [mem_range]
    omega
  · intro k hk
    rw [mem_range] at hk
    omega
  · intro j hj
    rw [mem_Icc] at hj
    omega
  · intro k hk
    rw [mem_range] at hk
    have hcast : ((n - 1 - k : ℕ) : ℝ) = (n : ℝ) - 1 - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast]

end Rhone.Statistics
