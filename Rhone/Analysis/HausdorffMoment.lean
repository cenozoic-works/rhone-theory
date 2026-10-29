/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Hausdorff moment theorem on the unit interval

Source: hausdorff1921, Thm III, pp. 98–102. -/

@[expose] public section

namespace Rhone.Analysis.HausdorffMoment

open MeasureTheory Polynomial Set Filter Topology
open scoped fwdDiff

noncomputable def momentFunctional (m : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun i => m i • LinearMap.id

theorem momentFunctional_X_pow (m : ℕ → ℝ) (k : ℕ) : momentFunctional m (X ^ k) = m k := by
  rw [momentFunctional, lsum_apply, ← monomial_one_right_eq_X_pow, sum_monomial_index] <;> simp

theorem momentFunctional_natCast_mul (m : ℕ → ℝ) (c : ℕ) (p : ℝ[X]) :
    momentFunctional m ((c : ℝ[X]) * p) = (c : ℝ) * momentFunctional m p := by
  rw [← map_natCast C c, C_mul', map_smul, smul_eq_mul]

theorem momentFunctional_X_pow_mul_one_sub_pow (m : ℕ → ℝ) (r : ℕ) : ∀ k : ℕ,
    momentFunctional m (X ^ k * (1 - X) ^ r) = (-1) ^ r * (Δ_[1]^[r] m) k := by
  induction r with
  | zero => intro k; simp [momentFunctional_X_pow]
  | succ r ih =>
    intro k
    have h : (X : ℝ[X]) ^ k * (1 - X) ^ (r + 1) =
        X ^ k * (1 - X) ^ r - X ^ (k + 1) * (1 - X) ^ r := by ring
    rw [h, map_sub, ih k, ih (k + 1), Function.iterate_succ_apply']
    simp only [fwdDiff]
    ring

theorem momentFunctional_bernstein (m : ℕ → ℝ) (n k : ℕ) :
    momentFunctional m (bernsteinPolynomial ℝ n k) =
      (n.choose k : ℝ) * ((-1) ^ (n - k) * (Δ_[1]^[n - k] m) k) := by
  rw [bernsteinPolynomial, mul_assoc, momentFunctional_natCast_mul,
    momentFunctional_X_pow_mul_one_sub_pow]

theorem momentFunctional_bernstein_nonneg {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (n k : ℕ) :
    0 ≤ momentFunctional m (bernsteinPolynomial ℝ n k) := by
  rw [momentFunctional_bernstein]
  exact mul_nonneg (Nat.cast_nonneg _) (hm _ _)

theorem sum_momentFunctional_bernstein (m : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), momentFunctional m (bernsteinPolynomial ℝ n k) = m 0 := by
  rw [← map_sum, bernsteinPolynomial.sum, ← pow_zero (X : ℝ[X]), momentFunctional_X_pow]

theorem sum_choose_mul_bernstein (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (k.choose j : ℝ[X]) * bernsteinPolynomial ℝ n k =
      (n.choose j : ℝ[X]) * X ^ j := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  rw [show j + d + 1 = j + (d + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun k hk => by
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hk)]; simp), zero_add]
  have hterm : ∀ i ∈ Finset.range (d + 1),
      ((j + i).choose j : ℝ[X]) * bernsteinPolynomial ℝ (j + d) (j + i) =
        ((j + d).choose j : ℝ[X]) * X ^ j *
          (X ^ i * (1 - X) ^ (d - i) * (d.choose i : ℝ[X])) := by
    intro i hi
    have hi : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc := Nat.choose_mul (n := j + d) (k := j + i) (s := j) (by omega)
    rw [show j + d - j = d by omega, show j + i - j = i by omega] at hc
    have hc' : ((j + i).choose j : ℝ[X]) * ((j + d).choose (j + i) : ℝ[X]) =
        ((j + d).choose j : ℝ[X]) * (d.choose i : ℝ[X]) := by
      rw [mul_comm]
      exact_mod_cast hc
    rw [bernsteinPolynomial, show j + d - (j + i) = d - i by omega]
    calc ((j + i).choose j : ℝ[X]) *
          (((j + d).choose (j + i) : ℝ[X]) * X ^ (j + i) * (1 - X) ^ (d - i))
        = (((j + i).choose j : ℝ[X]) * ((j + d).choose (j + i) : ℝ[X])) *
            (X ^ (j + i) * (1 - X) ^ (d - i)) := by ring
      _ = _ := by rw [hc', pow_add]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  simp

theorem abs_choose_div_sub_pow_le (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    ∀ j : ℕ, 2 * j ≤ n →
      |(k.choose j : ℝ) / n.choose j - ((k : ℝ) / n) ^ j| ≤ (j : ℝ) ^ 2 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hx0 : 0 ≤ (k : ℝ) / n := by positivity
  have hx1 : (k : ℝ) / n ≤ 1 := div_le_one_of_le₀ hkn hnpos.le
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hjn
    have ih := ih (by omega)
    have hjn' : (j : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : j + 2 ≤ n)
    have h2j : 2 * (j : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : 2 * j + 2 ≤ n)
    have hnj : (0 : ℝ) < (n : ℝ) - j := by linarith
    have hrec : ∀ a : ℕ, ((a.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) =
        (a.choose j : ℝ) * ((a : ℝ) - j) := by
      intro a
      rcases Nat.lt_or_ge a j with ha | ha
      · rw [Nat.choose_eq_zero_of_lt ha, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · have h := congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq a j)
        push_cast [Nat.cast_sub ha] at h
        linarith
    have hCn : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos (by omega)
    set r : ℝ := (k.choose j : ℝ) / n.choose j with hr
    set x : ℝ := (k : ℝ) / n with hx
    set a : ℝ := ((k : ℝ) - j) / ((n : ℝ) - j) with ha
    have hstep : ((k.choose (j + 1) : ℕ) : ℝ) / ((n.choose (j + 1) : ℕ) : ℝ) = r * a := by
      have hk' := hrec k
      have hn' := hrec n
      have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hk'' : ((k.choose (j + 1) : ℕ) : ℝ) =
          (k.choose j : ℝ) * ((k : ℝ) - j) / ((j : ℝ) + 1) := by
        rw [eq_div_iff hj1.ne']; exact hk'
      have hn'' : ((n.choose (j + 1) : ℕ) : ℝ) =
          (n.choose j : ℝ) * ((n : ℝ) - j) / ((j : ℝ) + 1) := by
        rw [eq_div_iff hj1.ne']; exact hn'
      rw [hk'', hn'', hr, ha]
      field_simp
    have habs_a : |a| ≤ 1 := by
      rw [ha, abs_div, abs_of_pos hnj, div_le_one hnj, abs_le]
      constructor <;> linarith
    have hxj : |x ^ j| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hx0 _)]
      exact pow_le_one₀ hx0 hx1
    have hax : |a - x| ≤ 2 * j / n := by
      have hdiff : a - x = -((j : ℝ) * ((n : ℝ) - k)) / (((n : ℝ) - j) * n) := by
        rw [ha, hx]
        field_simp
        ring
      rw [hdiff, abs_div, abs_neg, abs_of_nonneg (by nlinarith), abs_of_pos (by positivity),
        div_le_div_iff₀ (by positivity) hnpos]
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : (n : ℝ) - k ≤ 2 * ((n : ℝ) - j) := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hj0 hnpos.le)
      nlinarith
    push_cast
    rw [hstep, pow_succ]
    calc |r * a - x ^ j * x| = |(r - x ^ j) * a + x ^ j * (a - x)| := by ring_nf
      _ ≤ |(r - x ^ j) * a| + |x ^ j * (a - x)| := abs_add_le _ _
      _ = |r - x ^ j| * |a| + |x ^ j| * |a - x| := by rw [abs_mul, abs_mul]
      _ ≤ (j : ℝ) ^ 2 / n * 1 + 1 * (2 * j / n) := by
          gcongr
      _ = ((j : ℝ) ^ 2 + 2 * j) / n := by ring
      _ ≤ ((j : ℝ) + 1) ^ 2 / n := by
          apply div_le_div_of_nonneg_right _ hnpos.le
          nlinarith

noncomputable def gridPoint (n k : ℕ) : Icc (0 : ℝ) 1 :=
  projIcc 0 1 zero_le_one ((k : ℝ) / n)

theorem gridPoint_coe {n k : ℕ} (hk : k ≤ n) : (gridPoint n k : ℝ) = (k : ℝ) / n := by
  have hmem : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact div_le_one_of_le₀ (by exact_mod_cast hk) (by positivity)
  simp [gridPoint, projIcc_of_mem _ hmem]

noncomputable def approxFunctional (m : ℕ → ℝ) (n : ℕ) : C(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∑ k ∈ Finset.range (n + 1),
    momentFunctional m (bernsteinPolynomial ℝ n k) * g (gridPoint n k)
  map_add' g h := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c g := by simp [Finset.mul_sum, mul_left_comm]

theorem approxFunctional_apply (m : ℕ → ℝ) (n : ℕ) (g : C(Icc (0 : ℝ) 1, ℝ)) :
    approxFunctional m n g = ∑ k ∈ Finset.range (n + 1),
      momentFunctional m (bernsteinPolynomial ℝ n k) * g (gridPoint n k) := rfl

noncomputable def monomialOn (j : ℕ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x => (x : ℝ) ^ j, by fun_prop⟩

theorem approxFunctional_nonneg {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (n : ℕ)
    {g : C(Icc (0 : ℝ) 1, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ approxFunctional m n g := by
  rw [approxFunctional_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (momentFunctional_bernstein_nonneg hm n k) (hg _)

theorem abs_approxFunctional_sub_le {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (n : ℕ)
    (g h : C(Icc (0 : ℝ) 1, ℝ)) :
    |approxFunctional m n g - approxFunctional m n h| ≤ m 0 * ‖g - h‖ := by
  rw [← map_sub, approxFunctional_apply, ← sum_momentFunctional_bernstein m n, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (momentFunctional_bernstein_nonneg hm n k)]
  gcongr
  · exact momentFunctional_bernstein_nonneg hm n k
  · exact (Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm (g - h) _)

theorem tendsto_approxFunctional_monomialOn {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (j : ℕ) :
    Tendsto (fun n => approxFunctional m n (monomialOn j)) atTop (𝓝 (m j)) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |approxFunctional m n (monomialOn j) - m j| ≤ m 0 * (j : ℝ) ^ 2 / n := by
    filter_upwards [eventually_ge_atTop (2 * j + 1)] with n hn
    have hn0 : 0 < n := by omega
    have hjn : j ≤ n := by omega
    have hCn : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn
    have hmj : m j = ∑ k ∈ Finset.range (n + 1),
        momentFunctional m (bernsteinPolynomial ℝ n k) * ((k.choose j : ℝ) / n.choose j) := by
      have h := congrArg (momentFunctional m) (sum_choose_mul_bernstein n j hjn)
      rw [map_sum, momentFunctional_natCast_mul, momentFunctional_X_pow] at h
      simp only [momentFunctional_natCast_mul] at h
      calc m j = ((n.choose j : ℝ) * m j) / n.choose j := by field_simp
        _ = (∑ k ∈ Finset.range (n + 1),
              (k.choose j : ℝ) * momentFunctional m (bernsteinPolynomial ℝ n k)) /
              n.choose j := by rw [h]
        _ = _ := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
    have hL : approxFunctional m n (monomialOn j) = ∑ k ∈ Finset.range (n + 1),
        momentFunctional m (bernsteinPolynomial ℝ n k) * ((k : ℝ) / n) ^ j := by
      rw [approxFunctional_apply]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [monomialOn, ContinuousMap.coe_mk,
        gridPoint_coe (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
    rw [hL, hmj, ← Finset.sum_sub_distrib, ← sum_momentFunctional_bernstein m n, Finset.sum_mul,
      Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hw := momentFunctional_bernstein_nonneg hm n k
    rw [← mul_sub, abs_mul, abs_of_nonneg hw, mul_div_assoc]
    gcongr
    rw [abs_sub_comm]
    exact abs_choose_div_sub_pow_le n k hn0 hk j (by omega)
  have hlim : Tendsto (fun n : ℕ => m 0 * (j : ℝ) ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (hbound.mono fun n hn => by rwa [Real.norm_eq_abs]) hlim

theorem tendsto_approxFunctional_polynomial {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (p : ℝ[X]) :
    Tendsto (fun n => approxFunctional m n (p.toContinuousMapOn (Icc (0 : ℝ) 1))) atTop
      (𝓝 (momentFunctional m p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : (p + q).toContinuousMapOn (Icc (0 : ℝ) 1) =
        p.toContinuousMapOn (Icc (0 : ℝ) 1) + q.toContinuousMapOn (Icc (0 : ℝ) 1) := by
      ext x; simp
    simp only [h, map_add]
    exact hp.add hq
  | monomial j c =>
    have h : (monomial j c).toContinuousMapOn (Icc (0 : ℝ) 1) = c • monomialOn j := by
      ext x; simp [monomialOn]
    have hφ : momentFunctional m (monomial j c) = c * m j := by
      rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, momentFunctional_X_pow,
        smul_eq_mul]
    simp only [h, map_smul, smul_eq_mul, hφ]
    exact (tendsto_approxFunctional_monomialOn hm j).const_mul c

theorem cauchySeq_approxFunctional {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (g : C(Icc (0 : ℝ) 1, ℝ)) :
    CauchySeq fun n => approxFunctional m n g := by
  have hm0 : 0 ≤ m 0 := by simpa using hm 0 0
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hδ : 0 < ε / (4 * (m 0 + 1)) := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 g _ hδ
  have hT := tendsto_approxFunctional_polynomial hm p
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨N, hN⟩ := hT (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := abs_approxFunctional_sub_le hm n g (p.toContinuousMapOn (Icc (0 : ℝ) 1))
  have h2 := abs_approxFunctional_sub_le hm N g (p.toContinuousMapOn (Icc (0 : ℝ) 1))
  have h3 := hN n hn
  have h4 := hN N le_rfl
  rw [Real.dist_eq] at h3 h4 ⊢
  have hgp : ‖g - p.toContinuousMapOn (Icc (0 : ℝ) 1)‖ < ε / (4 * (m 0 + 1)) := by
    rwa [norm_sub_rev]
  have hmδ : m 0 * ‖g - p.toContinuousMapOn (Icc (0 : ℝ) 1)‖ ≤ ε / 4 := by
    calc m 0 * ‖g - p.toContinuousMapOn (Icc (0 : ℝ) 1)‖
        ≤ (m 0 + 1) * (ε / (4 * (m 0 + 1))) := by
          gcongr
          linarith
      _ = ε / 4 := by field_simp
  have hab := abs_sub_lt_iff.1 h3
  have hcd := abs_sub_lt_iff.1 h4
  have hef := abs_le.1 h1
  have hgh := abs_le.1 h2
  rw [abs_lt]
  constructor <;> linarith [hab.1, hab.2, hcd.1, hcd.2, hef.1, hef.2, hgh.1, hgh.2]

noncomputable def limitFunctional (m : ℕ → ℝ) (g : C(Icc (0 : ℝ) 1, ℝ)) : ℝ :=
  limUnder atTop fun n => approxFunctional m n g

theorem tendsto_limitFunctional {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (g : C(Icc (0 : ℝ) 1, ℝ)) :
    Tendsto (fun n => approxFunctional m n g) atTop (𝓝 (limitFunctional m g)) :=
  (cauchySeq_approxFunctional hm g).tendsto_limUnder

noncomputable def limitPositiveFunctional {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) :
    CompactlySupportedContinuousMap (Icc (0 : ℝ) 1) ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => limitFunctional m ⟨f, f.continuous⟩
      map_add' := fun f g => by
        have h := (tendsto_limitFunctional hm ⟨f, f.continuous⟩).add
          (tendsto_limitFunctional hm ⟨g, g.continuous⟩)
        simp only [← map_add] at h
        exact tendsto_nhds_unique (tendsto_limitFunctional hm _) (by convert h using 2)
      map_smul' := fun c f => by
        have h := (tendsto_limitFunctional hm ⟨f, f.continuous⟩).const_mul c
        simp only [← smul_eq_mul, ← map_smul] at h
        exact tendsto_nhds_unique (tendsto_limitFunctional hm _) (by convert h using 2) }
    (fun f hf => by
      refine ge_of_tendsto' (tendsto_limitFunctional hm ⟨f, f.continuous⟩) fun n => ?_
      exact approxFunctional_nonneg hm n fun x =>
        (CompactlySupportedContinuousMap.le_def.1 hf) x)

theorem limitFunctional_monomialOn {m : ℕ → ℝ}
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) (j : ℕ) :
    limitFunctional m (monomialOn j) = m j :=
  tendsto_nhds_unique (tendsto_limitFunctional hm _) (tendsto_approxFunctional_monomialOn hm j)

/-- Source: hausdorff1921, Thm III, p. 98. -/
theorem exists_moment_measure (m : ℕ → ℝ)
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, m n = ∫ x, x ^ n ∂μ := by
  set μI : Measure (Icc (0 : ℝ) 1) := RealRMK.rieszMeasure (limitPositiveFunctional hm)
  have hemb : MeasurableEmbedding (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  refine ⟨μI.map Subtype.val, inferInstance, ?_, fun n => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext x; simp
    rw [this, measure_empty]
  · rw [hemb.integral_map]
    have h := RealRMK.integral_rieszMeasure (limitPositiveFunctional hm)
      (CompactlySupportedContinuousMap.continuousMapEquiv (monomialOn n))
    have hval : limitPositiveFunctional hm
        (CompactlySupportedContinuousMap.continuousMapEquiv (monomialOn n)) =
          limitFunctional m (monomialOn n) := rfl
    rw [hval, limitFunctional_monomialOn hm n] at h
    rw [← h]
    rfl

theorem eq_of_moments_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0)
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hμr : μ.restrict (Icc (0 : ℝ) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ)
  have hνr : ν.restrict (Icc (0 : ℝ) 1) = ν :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hν)
  have hint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], ρ.restrict (Icc (0 : ℝ) 1) = ρ →
      ∀ p : ℝ[X], Integrable (fun x => p.eval x) ρ := by
    intro ρ _ hρ p
    rw [← hρ]
    exact p.continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hpoly : ∀ p : ℝ[X], ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
    intro p
    have hμi : ∀ i, Integrable (fun x : ℝ => p.coeff i * x ^ i) μ := fun i => by
      have h := hint μ hμr (C (p.coeff i) * X ^ i)
      simp only [eval_mul, eval_C, eval_pow, eval_X] at h
      exact h
    have hνi : ∀ i, Integrable (fun x : ℝ => p.coeff i * x ^ i) ν := fun i => by
      have h := hint ν hνr (C (p.coeff i) * X ^ i)
      simp only [eval_mul, eval_C, eval_pow, eval_X] at h
      exact h
    simp only [eval_eq_sum_range]
    rw [integral_finsetSum _ fun i _ => hμi i, integral_finsetSum _ fun i _ => hνi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul, h i]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  set C : ℝ := μ.real (Icc (0 : ℝ) 1) + ν.real (Icc (0 : ℝ) 1) + 1
  have hC : 0 < C := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn
    (ε / C) (by positivity)
  have hclose : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], ρ.restrict (Icc (0 : ℝ) 1) = ρ →
      |∫ x, f x ∂ρ - ∫ x, p.eval x ∂ρ| ≤ ε / C * ρ.real (Icc (0 : ℝ) 1) := by
    intro ρ _ hρ
    rw [← integral_sub (f.integrable ρ) (hint ρ hρ p)]
    conv_lhs => rw [← hρ]
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ _) fun x hx => ?_
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp x hx).le
  have h1 := hclose μ hμr
  have h2 := hclose ν hνr
  rw [Real.dist_eq]
  have hμnn : 0 ≤ μ.real (Icc (0 : ℝ) 1) := measureReal_nonneg
  have hνnn : 0 ≤ ν.real (Icc (0 : ℝ) 1) := measureReal_nonneg
  calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
      ≤ |∫ x, f x ∂μ - ∫ x, p.eval x ∂μ| + |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| := by
        rw [hpoly p]
        calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
            = |(∫ x, f x ∂μ - ∫ x, p.eval x ∂ν) - (∫ x, f x ∂ν - ∫ x, p.eval x ∂ν)| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
    _ ≤ ε / C * μ.real (Icc (0 : ℝ) 1) + ε / C * ν.real (Icc (0 : ℝ) 1) := add_le_add h1 h2
    _ = ε * ((μ.real (Icc (0 : ℝ) 1) + ν.real (Icc (0 : ℝ) 1)) / C) := by ring
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hC]
        linarith
    _ = ε := mul_one ε

/-- Source: hausdorff1921, Thm III, pp. 98–102. -/
theorem hausdorff_moment_existsUnique (m : ℕ → ℝ)
    (hm : ∀ j n : ℕ, 0 ≤ (-1 : ℝ) ^ j * (Δ_[1]^[j] m) n) :
    ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, m n = ∫ x, x ^ n ∂μ := by
  obtain ⟨μ, hfin, hsupp, hmom⟩ := exists_moment_measure m hm
  refine ⟨μ, ⟨hfin, hsupp, hmom⟩, ?_⟩
  rintro ν ⟨hνfin, hνsupp, hνmom⟩
  exact eq_of_moments_eq hνsupp hsupp fun n => (hνmom n).symm.trans (hmom n)

end Rhone.Analysis.HausdorffMoment
