/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.TreeLengthLaplace

/-!
# Laplace transform and distribution function of tree length from partition clocks

Source: watterson1975, p. 258, eq. (1.3a); kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics
open scoped NNReal ENNReal

theorem integral_clockLaw_prod_exp (m : ℕ) {w : Fin m → ℝ} (hw : ∀ k, 0 ≤ w k) :
    ∫ e : ℕ → ℝ, ∏ k : Fin m, Real.exp (-(w k * max 0 (e k))) ∂clockLaw =
      ∏ k : Fin m, 1 / (1 + w k) := by
  have hind : iIndepFun (fun (k : Fin m) (e : ℕ → ℝ) => e k.val) clockLaw :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ => id)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_prod_comp (𝕜 := ℝ)
    (f := fun (k : Fin m) (t : ℝ) => Real.exp (-(w k * max 0 t)))
    (fun k => (measurable_pi_apply k.val).aemeasurable)
    (fun k => (by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-(w k * max 0 t))).aestronglyMeasurable)
  simp only [Finset.prod_apply, Function.comp_apply] at hprod
  rw [hprod]
  apply Finset.prod_congr rfl
  intro k _
  rw [integral_clockLaw_eval k.val (g := fun t : ℝ => Real.exp (-(w k * max 0 t)))
    (by fun_prop)]
  have h := integral_pow_mul_exp_expMeasure_one (a := w k) (hw k) 0
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
  exact h

/-- Source: kingman1982, eq. (1.7), (1.12)–(1.13). -/
theorem partitionTmrca_toReal_ae_eq_clock_sum (n : ℕ) :
    ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      (partitionTmrca h).toReal =
        ∑ k : Fin (n - 1),
          2 / (((n : ℝ) - (k : ℕ)) * ((n : ℝ) - 1 - (k : ℕ))) * max 0 (h.2 k) := by
  have hae : ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k : ℕ, (h.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown_general n)
  filter_upwards [hae, partition_costBefore_eq_finite_clamped_sum n (fun _ => (1 : ℝ))
    (fun _ => zero_le_one)] with h hh hcost
  unfold partitionTmrca RateChain.timeBefore
  rw [hcost, ENNReal.toReal_ofReal (Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg zero_le_one (le_max_left _ _))]
  apply Finset.sum_congr rfl
  intro k _
  have hk := k.isLt
  have hc : (h.1 k.val).parts.card = n - k.val := by
    rw [hh]
    omega
  have hnot : h.1 k.val ∉ coalescedPartitions (Fin n) := by
    rw [mem_coalescedPartitions, hc]
    omega
  simp only [hnot, ↓reduceIte, one_mul]
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
  rw [hrate]
  clear hrate
  have hr : (0 : ℝ) < ((n : ℝ) - k.val) * ((n : ℝ) - 1 - k.val) / 2 := by positivity
  rcases le_total 0 (h.2 k.val) with he | he
  · rw [max_eq_right he, max_eq_right (div_nonneg he hr.le)]
    field_simp
  · rw [max_eq_left he, max_eq_left (div_nonpos_of_nonpos_of_nonneg he hr.le)]
    ring

theorem measureReal_weighted_exp_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X μ) (hlaw : ∀ j, μ.map (X j) = expMeasure 1) (m : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    μ.real {ω | ∑ j ∈ range m, 2 / ((j : ℝ) + 1) * max 0 (X j ω) ≤ x} =
      (1 - Real.exp (-x / 2)) ^ m := by
  induction m generalizing x with
  | zero =>
    simp only [range_zero, sum_empty, hx, Set.ofPred_true, probReal_univ, pow_zero]
  | succ m ih =>
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set c : ℝ := 2 / ((m : ℝ) + 1) with hc
    have hcpos : 0 < c := by positivity
    let Y : ℕ → Ω → ℝ := fun j ω => 2 / ((j : ℝ) + 1) * max 0 (X j ω)
    have hYm : ∀ j, Measurable (Y j) := fun j =>
      ((measurable_const.max measurable_id).const_mul _).comp (hX j)
    have hY : iIndepFun Y μ :=
      hind.comp (fun (j : ℕ) (t : ℝ) => 2 / ((j : ℝ) + 1) * max 0 t)
        (fun j => (measurable_const.max measurable_id).const_mul _)
    let A : Ω → ℝ := ∑ j ∈ range m, Y j
    have hA : Measurable A := by
      have h := Finset.measurable_sum (range m) (fun j _ => hYm j)
      convert h using 1
      ext ω
      simp only [A, Finset.sum_apply]
    have hAnn : ∀ ω, 0 ≤ A ω := fun ω => by
      simp only [A, Y, Finset.sum_apply]
      exact Finset.sum_nonneg fun j _ => by positivity
    have hAY : IndepFun (Y m) A μ :=
      (hY.indepFun_finsetSum_of_notMem hYm (by
        simp only [mem_range, lt_self_iff_false, not_false_eq_true] : m ∉ range m)).symm
    let F : ℝ → ℝ := fun y => if 0 ≤ y then (1 - Real.exp (-y / 2)) ^ m else 0
    have hFm : Measurable F :=
      Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
    have hF0 : ∀ y, 0 ≤ F y := fun y => by
      simp only [F]
      split_ifs with hy
      · exact pow_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) m
      · exact le_rfl
    have hF1 : ∀ y, F y ≤ 1 := fun y => by
      simp only [F]
      split_ifs with hy
      · exact pow_le_one₀ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-y / 2)])
      · exact zero_le_one
    have hF : ∀ y, μ {ω | A ω ≤ y} = ENNReal.ofReal (F y) := fun y => by
      by_cases hy : 0 ≤ y
      · have h := ih hy
        simp only [F, hy, ↓reduceIte]
        rw [← h, ofReal_measureReal]
        simp only [A, Y, Finset.sum_apply]
      · have hempty : {ω | A ω ≤ y} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          linarith [hAnn ω]
        simp only [F, hy, ↓reduceIte, hempty, measure_empty, ENNReal.ofReal_zero]
    have hYlaw : μ.map (Y m) = (expMeasure 1).map (fun t => c * max 0 t) := by
      rw [← hlaw m, Measure.map_map (by fun_prop : Measurable fun t : ℝ => c * max 0 t) (hX m)]
      rfl
    have hset : {ω | ∑ j ∈ range (m + 1), 2 / ((j : ℝ) + 1) * max 0 (X j ω) ≤ x} =
        (fun ω => (Y m ω, A ω)) ⁻¹' {p : ℝ × ℝ | p.2 ≤ x - p.1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, A, Y, Finset.sum_apply,
        Finset.sum_range_succ]
      constructor <;> intro h <;> linarith
    have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ x - p.1} :=
      measurableSet_le measurable_snd (by fun_prop)
    have hint : Integrable (fun t => F (x - c * max 0 t)) (expMeasure 1) := by
      refine (integrable_const (1 : ℝ)).mono' (hFm.comp (by fun_prop)).aestronglyMeasurable
        (ae_of_all _ fun t => ?_)
      rw [Real.norm_of_nonneg (hF0 _)]
      exact hF1 _
    have hmeas : μ {ω | ∑ j ∈ range (m + 1), 2 / ((j : ℝ) + 1) * max 0 (X j ω) ≤ x} =
        ENNReal.ofReal (∫ t, F (x - c * max 0 t) ∂expMeasure 1) := by
      rw [hset, ← Measure.map_apply ((hYm m).prodMk hA) hS,
        (indepFun_iff_map_prod_eq_prod_map_map (hYm m).aemeasurable hA.aemeasurable).mp hAY,
        Measure.prod_apply hS]
      have hv : ∀ v, (μ.map A) (Prod.mk v ⁻¹' {p : ℝ × ℝ | p.2 ≤ x - p.1}) =
          ENNReal.ofReal (F (x - v)) := by
        intro v
        rw [Measure.map_apply hA (measurable_prodMk_left hS)]
        exact hF (x - v)
      simp only [hv]
      rw [hYlaw, lintegral_map (f := fun v => ENNReal.ofReal (F (x - v)))
          (g := fun t => c * max 0 t)
          (hFm.comp (by fun_prop : Measurable fun v : ℝ => x - v)).ennreal_ofReal
          (by fun_prop),
        ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => hF0 _)]
    rw [measureReal_def, hmeas, ENNReal.toReal_ofReal (integral_nonneg fun t => hF0 _),
      integral_expMeasure_one]
    have hb : 0 ≤ x / c := div_nonneg hx hcpos.le
    have hstep1 : ∫ t in Set.Ioi 0, Real.exp (-t) * F (x - c * max 0 t) =
        ∫ t in Set.Ioc 0 (x / c), Real.exp (-t) *
          (1 - Real.exp (-x / 2) * Real.exp (t / ((m : ℝ) + 1))) ^ m := by
      have hcongr : ∫ t in Set.Ioi 0, Real.exp (-t) * F (x - c * max 0 t) =
          ∫ t in Set.Ioi 0, (Set.Ioc 0 (x / c)).indicator (fun t => Real.exp (-t) *
            (1 - Real.exp (-x / 2) * Real.exp (t / ((m : ℝ) + 1))) ^ m) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht' : (0 : ℝ) < t := ht
        simp only [max_eq_right ht'.le]
        by_cases htb : t ≤ x / c
        · have hnn : 0 ≤ x - c * t := by
            have := (le_div_iff₀ hcpos).mp htb
            linarith
          have hmem : t ∈ Set.Ioc 0 (x / c) := ⟨ht', htb⟩
          rw [Set.indicator_of_mem hmem]
          simp only [F, hnn, ↓reduceIte]
          rw [← Real.exp_add]
          have harg : -(x - c * t) / 2 = -x / 2 + t / ((m : ℝ) + 1) := by
            rw [hc]
            field_simp
            ring
          rw [harg]
        · have hneg : ¬ 0 ≤ x - c * t := by
            have := (div_lt_iff₀ hcpos).mp (not_le.mp htb)
            intro h
            linarith
          have hmem : t ∉ Set.Ioc 0 (x / c) := fun h => htb h.2
          rw [Set.indicator_of_notMem hmem]
          simp only [F, hneg, ↓reduceIte, mul_zero]
      rw [hcongr, setIntegral_indicator measurableSet_Ioc]
      congr 2
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      tauto
    rw [hstep1, ← intervalIntegral.integral_of_le hb]
    have hderiv : ∀ t ∈ Set.uIcc 0 (x / c),
        HasDerivAt (fun t : ℝ => -(Real.exp (-t) *
          (1 - Real.exp (-x / 2) * Real.exp (t / ((m : ℝ) + 1))) ^ (m + 1)))
          (Real.exp (-t) * (1 - Real.exp (-x / 2) * Real.exp (t / ((m : ℝ) + 1))) ^ m) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * -1) t :=
        (hasDerivAt_id t).neg.exp
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (t / ((m : ℝ) + 1)))
          (Real.exp (t / ((m : ℝ) + 1)) * (1 / ((m : ℝ) + 1))) t :=
        ((hasDerivAt_id t).div_const ((m : ℝ) + 1)).exp
      have h3 := (h2.const_mul (Real.exp (-x / 2))).const_sub 1
      have h5 := (h1.mul (h3.pow (m + 1))).neg
      convert h5 using 1
      simp only [Pi.pow_apply, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t) *
        (1 - Real.exp (-x / 2) * Real.exp (t / ((m : ℝ) + 1))) ^ m).intervalIntegrable _ _)]
    have hq : Real.exp (-x / 2) * Real.exp (x / c / ((m : ℝ) + 1)) = 1 := by
      rw [← Real.exp_add]
      have h0 : -x / 2 + x / c / ((m : ℝ) + 1) = 0 := by
        rw [hc]
        field_simp
        ring
      rw [h0, Real.exp_zero]
    simp only [hq, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, mul_zero, neg_zero, zero_div, Real.exp_zero, mul_one,
      one_mul, sub_neg_eq_add, zero_add]

def clockReflect (n j : ℕ) : ℕ := if j < n - 1 then n - 2 - j else j

theorem clockReflect_injective (n : ℕ) : Function.Injective (clockReflect n) := by
  intro a b h
  unfold clockReflect at h
  split_ifs at h <;> omega

end Rhone.Statistics

namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Probability
open scoped NNReal ENNReal

theorem laplace_partitionTmrca (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ p, Real.exp (-(s * (partitionTmrca p).toReal))
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      ∏ k ∈ Icc 2 n, (k.choose 2 : ℝ) / ((k.choose 2 : ℝ) + s) := by
  have h1 : ∫ p, Real.exp (-(s * (partitionTmrca p).toReal))
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      ∫ p, (fun e : ℕ → ℝ => ∏ k : Fin (n - 1), Real.exp
        (-(s * (2 / (((n : ℝ) - (k : ℕ)) * ((n : ℝ) - 1 - (k : ℕ)))) * max 0 (e k)))) p.2
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    apply integral_congr_ae
    filter_upwards [partitionTmrca_toReal_ae_eq_clock_sum n] with p hp
    rw [hp, ← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpos : ∀ k : Fin (n - 1), (0 : ℝ) < (n : ℝ) - 1 - (k : ℕ) := fun k => by
    have hlt : ((k.val : ℝ) + 1) < n := by exact_mod_cast (by omega : k.val + 1 < n)
    linarith
  rw [h1, integral_jumpHoldLaw_clock n (G := fun e : ℕ → ℝ => ∏ k : Fin (n - 1), Real.exp
      (-(s * (2 / (((n : ℝ) - (k : ℕ)) * ((n : ℝ) - 1 - (k : ℕ)))) * max 0 (e k))))
      (by fun_prop),
    integral_clockLaw_prod_exp (n - 1)
      (w := fun k => s * (2 / (((n : ℝ) - (k : ℕ)) * ((n : ℝ) - 1 - (k : ℕ)))))
      (fun k => by
        have := hpos k
        have h' : (0 : ℝ) < (n : ℝ) - (k : ℕ) := by linarith
        positivity),
    Fin.prod_univ_eq_prod_range
      (fun k : ℕ => 1 / (1 + s * (2 / (((n : ℝ) - k) * ((n : ℝ) - 1 - k))))) (n - 1)]
  apply Finset.prod_nbij' (fun k => n - k) (fun j => n - j)
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
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      rw [Nat.cast_sub (by omega)]
    have hlt : ((k : ℝ) + 1) < n := by exact_mod_cast (by omega : k + 1 < n)
    have hp1 : (0 : ℝ) < (n : ℝ) - 1 - k := by linarith
    have hp2 : (0 : ℝ) < (n : ℝ) - k := by linarith
    rw [Nat.cast_choose_two, hcast, show (n : ℝ) - k - 1 = (n : ℝ) - 1 - k by ring]
    field_simp

theorem partitionTreeLength_cdf (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
        {p | partitionTreeLength p ≤ ENNReal.ofReal x} =
      (1 - Real.exp (-x / 2)) ^ (n - 1) := by
  have hE : MeasurableSet {e : ℕ → ℝ |
      ∑ k : Fin (n - 1), 2 / ((n : ℝ) - 1 - (k : ℕ)) * max 0 (e k) ≤ x} :=
    measurableSet_le (by fun_prop) measurable_const
  have hae : ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      (partitionTreeLength p ≤ ENNReal.ofReal x) = (p.2 ∈ {e : ℕ → ℝ |
        ∑ k : Fin (n - 1), 2 / ((n : ℝ) - 1 - (k : ℕ)) * max 0 (e k) ≤ x}) := by
    filter_upwards [partition_costBefore_eq_finite_clamped_sum n
      (fun π => (π.parts.card : ℝ)) (fun π => Nat.cast_nonneg π.parts.card),
      kingmanFiniteLength_ae_eq_clock_sum n] with p hp1 hp2
    unfold partitionTreeLength
    rw [hp1, ENNReal.ofReal_le_ofReal_iff hx]
    unfold kingmanFiniteReward at hp2
    rw [hp2]
  have hmap : ((partitionChain (Fin n)).jumpHoldLaw ⊥).map Prod.snd = clockLaw := by
    rw [RateChain.jumpHoldLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have h1 : ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
        {p | partitionTreeLength p ≤ ENNReal.ofReal x} =
      clockLaw.real {e : ℕ → ℝ |
        ∑ k : Fin (n - 1), 2 / ((n : ℝ) - 1 - (k : ℕ)) * max 0 (e k) ≤ x} := by
    rw [← hmap, map_measureReal_apply measurable_snd hE]
    exact measureReal_congr hae
  have hind : iIndepFun (fun (j : ℕ) (e : ℕ → ℝ) => e (clockReflect n j)) clockLaw :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ => id)
      (fun _ => measurable_id)).precomp (clockReflect_injective n)
  have h2 := measureReal_weighted_exp_sum_le (μ := clockLaw)
    (X := fun (j : ℕ) (e : ℕ → ℝ) => e (clockReflect n j))
    (fun j => measurable_pi_apply _) hind
    (fun j => Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) (clockReflect n j))
    (n - 1) hx
  rw [h1, ← h2]
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  have hsum : ∑ k : Fin (n - 1), 2 / ((n : ℝ) - 1 - (k : ℕ)) * max 0 (e k) =
      ∑ j ∈ range (n - 1), 2 / ((j : ℝ) + 1) * max 0 (e (clockReflect n j)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => 2 / ((n : ℝ) - 1 - k) * max 0 (e k)) (n - 1),
      ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    have hidx : n - 1 - 1 - j = n - 2 - j := by omega
    have hcr : clockReflect n j = n - 2 - j := by
      unfold clockReflect
      simp only [hj, ↓reduceIte]
    have hcast : ((n - 2 - j : ℕ) : ℝ) = (n : ℝ) - 2 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_ofNat]
    rw [hidx, hcr, hcast]
    congr 2
    ring
  rw [hsum]

end Rhone.Statistics
