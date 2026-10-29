/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Closure.EvRat
public import Rhone.Coalescent.Rational.Expansion

/-! # The `1/ρ` expansion of the denominator and order matching, with remainder limits -/

@[expose] public section

namespace Rhone.Coalescent.Closure

open Filter Topology Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config
open Analysis.RecombinationExpansion Probability.RecombinationExpansion

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def rem (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    ℕ → ℝ → Config KA KB → ℝ
  | 0, ρ, ξ => Rational.Del hθA hθB πA πB ρ ξ
  | k + 1, ρ, ξ =>
      ρ * rem hθA hθB πA πB k ρ ξ - limUnder atTop fun r : ℝ => r * rem hθA hθB πA πB k r ξ

noncomputable def qCoeff (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    ℕ → Config KA KB → ℝ
  | 0, _ => 0
  | k + 1, ξ => limUnder atTop fun r : ℝ => r * rem hθA hθB πA πB k r ξ

variable {hθA : 0 < θA} {hθB : 0 < θB}

theorem rem_zero (ρ : ℝ) : rem hθA hθB πA πB 0 ρ = Rational.Del hθA hθB πA πB ρ := rfl

theorem rem_succ (k : ℕ) (ρ : ℝ) (ξ : Config KA KB) :
    rem hθA hθB πA πB (k + 1) ρ ξ
      = ρ * rem hθA hθB πA πB k ρ ξ - qCoeff hθA hθB πA πB (k + 1) ξ := rfl

section Exists

variable (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
  (hsB : ∑ j, πB j = 1)
include hπA hsA hπB hsB

theorem rem_evRat_tendsto (k : ℕ) (ξ : Config KA KB) :
    Analysis.Closure.EvRat (fun ρ => rem hθA hθB πA πB k ρ ξ) ∧
      Tendsto (fun ρ => rem hθA hθB πA πB k ρ ξ) atTop (𝓝 0) := by
  induction k with
  | zero =>
    refine ⟨?_, Rational.tendsto_Del_zero hθA hθB hπA hsA hπB hsB ξ⟩
    obtain ⟨u, d, hd, he⟩ := Rational.exists_ratio_Del (πA := πA) (πB := πB) hθA hθB ξ
    exact ⟨u, d, hd, he⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hlim : Tendsto (fun ρ => ρ * rem hθA hθB πA πB k ρ ξ) atTop
        (𝓝 (qCoeff hθA hθB πA πB (k + 1) ξ)) :=
      tendsto_nhds_limUnder (h1.exists_tendsto_mul h2)
    refine ⟨(h1.mul_id).sub (Analysis.Closure.EvRat.const _), ?_⟩
    have := hlim.sub_const (qCoeff hθA hθB πA πB (k + 1) ξ)
    rw [sub_self] at this
    exact this

theorem rem_evRat (k : ℕ) (ξ : Config KA KB) : Analysis.Closure.EvRat
    (fun ρ => rem hθA hθB πA πB k ρ ξ) :=
  (rem_evRat_tendsto hπA hsA hπB hsB k ξ).1

theorem tendsto_rem (k : ℕ) (ξ : Config KA KB) :
    Tendsto (fun ρ => rem hθA hθB πA πB k ρ ξ) atTop (𝓝 0) :=
  (rem_evRat_tendsto hπA hsA hπB hsB k ξ).2

theorem tendsto_mul_rem (k : ℕ) (ξ : Config KA KB) :
    Tendsto (fun ρ => ρ * rem hθA hθB πA πB k ρ ξ) atTop
      (𝓝 (qCoeff hθA hθB πA πB (k + 1) ξ)) :=
  tendsto_nhds_limUnder
    ((rem_evRat hπA hsA hπB hsB k ξ).exists_tendsto_mul (tendsto_rem hπA hsA hπB hsB k ξ))

theorem qCoeff_one :
    qCoeff hθA hθB πA πB 1 = Rational.qCoeffOne hθA hθB hπA hsA hπB hsB := by
  funext ξ
  exact (Rational.tendsto_qCoeffOne hθA hθB hπA hsA hπB hsB ξ).limUnder_eq

theorem qCoeff_one_eq (ξ : Config KA KB) :
    qCoeff hθA hθB πA πB 1 ξ = twoQ1 θA θB πA πB ξ / 2 := by
  rw [qCoeff_one hπA hsA hπB hsB]
  exact Rational.qCoeffOne_eq_half_twoQ1 hθA hθB hπA hsA hπB hsB ξ

end Exists

noncomputable def Aop (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (k : ℕ) (ρ : ℝ) (ξ : Config KA KB) : ℝ :=
  ρ * L1 (rem hθA hθB πA πB k ρ) ξ + L0 θA θB πA πB (rem hθA hθB πA πB k ρ) ξ

theorem Aop_zero {ρ : ℝ} (hρ : 0 ≤ ρ) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    Aop hθA hθB πA πB 0 ρ ξ = twoQ1 θA θB πA πB ξ := by
  have hL := LDelta hθA hθB
    (Rational.qAt_isSolution (πA := πA) (πB := πB) hθA hθB hρ) ξ hn
  rw [← Rational.Del_eq hθA hθB ρ, Lop_split] at hL
  rw [Aop, rem_zero]
  linarith

theorem Aop_succ (k : ℕ) (ρ : ℝ) (ξ : Config KA KB) :
    Aop hθA hθB πA πB (k + 1) ρ ξ
      = ρ * (Aop hθA hθB πA πB k ρ ξ - L1 (qCoeff hθA hθB πA πB (k + 1)) ξ)
        - L0 θA θB πA πB (qCoeff hθA hθB πA πB (k + 1)) ξ := by
  have hfun : rem hθA hθB πA πB (k + 1) ρ
      = fun η => ρ * rem hθA hθB πA πB k ρ η - qCoeff hθA hθB πA πB (k + 1) η := by
    funext η
    exact rem_succ k ρ η
  have e1 : L1 (rem hθA hθB πA πB (k + 1) ρ) ξ
      = ρ * L1 (rem hθA hθB πA πB k ρ) ξ - L1 (qCoeff hθA hθB πA πB (k + 1)) ξ := by
    rw [hfun, L1_sub (fun η => ρ * rem hθA hθB πA πB k ρ η)
      (qCoeff hθA hθB πA πB (k + 1)) ξ, L1_smul]
  have e2 : L0 θA θB πA πB (rem hθA hθB πA πB (k + 1) ρ) ξ
      = ρ * L0 θA θB πA πB (rem hθA hθB πA πB k ρ) ξ
        - L0 θA θB πA πB (qCoeff hθA hθB πA πB (k + 1)) ξ := by
    rw [hfun, Rational.L0_sub (fun η => ρ * rem hθA hθB πA πB k ρ η)
      (qCoeff hθA hθB πA πB (k + 1)) ξ, Rational.L0_smul]
  rw [Aop, e1, e2, Aop]
  ring

section Limits

variable (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
  (hsB : ∑ j, πB j = 1)
include hπA hsA hπB hsB

theorem tendsto_Aop (k : ℕ) (ξ : Config KA KB) :
    Tendsto (fun ρ => Aop hθA hθB πA πB k ρ ξ) atTop
      (𝓝 (L1 (qCoeff hθA hθB πA πB (k + 1)) ξ)) := by
  have h1 : Tendsto (fun ρ : ℝ => L1 (fun η => ρ * rem hθA hθB πA πB k ρ η) ξ) atTop
      (𝓝 (L1 (qCoeff hθA hθB πA πB (k + 1)) ξ)) :=
    Probability.RecombinationExpansion.tendsto_L1
        (fun ρ : ℝ => fun η => ρ * rem hθA hθB πA πB k ρ η)
      (qCoeff hθA hθB πA πB (k + 1)) (fun η => tendsto_mul_rem hπA hsA hπB hsB k η) ξ
  have h2 : Tendsto (fun ρ : ℝ => L0 θA θB πA πB (rem hθA hθB πA πB k ρ) ξ) atTop (𝓝 0) := by
    have h := Probability.RecombinationExpansion.tendsto_L0 (θA := θA) (θB := θB) (πA := πA)
        (πB := πB)
      (fun ρ : ℝ => rem hθA hθB πA πB k ρ) (fun _ => (0 : ℝ))
      (fun η => tendsto_rem hπA hsA hπB hsB k η) ξ
    rwa [Rational.L0_zero] at h
  have hcomb := h1.add h2
  rw [add_zero] at hcomb
  refine hcomb.congr fun ρ => ?_
  rw [Aop, L1_smul]

theorem Aop_eq_and_L1_qCoeff (k : ℕ) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    (∀ ρ : ℝ, 0 ≤ ρ → Aop hθA hθB πA πB (k + 1) ρ ξ
        = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (k + 1)) ξ) ∧
      L1 (qCoeff hθA hθB πA πB (k + 2)) ξ
        = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (k + 1)) ξ := by
  have step : ∀ m : ℕ, (∀ ρ : ℝ, 0 ≤ ρ → Aop hθA hθB πA πB (m + 1) ρ ξ
      = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (m + 1)) ξ) →
      L1 (qCoeff hθA hθB πA πB (m + 2)) ξ
        = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (m + 1)) ξ := by
    intro m hm
    have hconst : (fun ρ : ℝ => Aop hθA hθB πA πB (m + 1) ρ ξ)
        =ᶠ[atTop] fun _ : ℝ => -L0 θA θB πA πB (qCoeff hθA hθB πA πB (m + 1)) ξ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
      exact hm r hr
    exact tendsto_nhds_unique (tendsto_Aop hπA hsA hπB hsB (m + 1) ξ)
      (tendsto_const_nhds.congr' hconst.symm)
  have main : ∀ m : ℕ, ∀ ρ : ℝ, 0 ≤ ρ → Aop hθA hθB πA πB (m + 1) ρ ξ
      = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (m + 1)) ξ := by
    intro m
    induction m with
    | zero =>
      intro ρ hρ
      have h0 := Aop_zero (hθA := hθA) (hθB := hθB) (πA := πA) (πB := πB) hρ ξ hn
      have h1 : L1 (qCoeff hθA hθB πA πB 1) ξ = twoQ1 θA θB πA πB ξ := by
        rw [qCoeff_one hπA hsA hπB hsB]
        exact Rational.L1_qCoeffOne hθA hθB hπA hsA hπB hsB ξ hn
      rw [Aop_succ, h0, h1]
      ring
    | succ m ih =>
      intro ρ hρ
      rw [Aop_succ, ih ρ hρ, step m ih]
      ring
  exact ⟨main k, step k (main k)⟩

theorem L1_qCoeff_succ (k : ℕ) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    L1 (qCoeff hθA hθB πA πB (k + 2)) ξ
      = -L0 θA θB πA πB (qCoeff hθA hθB πA πB (k + 1)) ξ :=
  (Aop_eq_and_L1_qCoeff hπA hsA hπB hsB k ξ hn).2

theorem L1_qCoeff_one (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    L1 (qCoeff hθA hθB πA πB 1) ξ = twoQ1 θA θB πA πB ξ := by
  rw [qCoeff_one hπA hsA hπB hsB]
  exact Rational.L1_qCoeffOne hθA hθB hπA hsA hπB hsB ξ hn

end Limits

theorem Del_eq_sum_add (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (ξ : Config KA KB) :
    Rational.Del hθA hθB πA πB ρ ξ
      = (∑ j ∈ Finset.range k, qCoeff hθA hθB πA πB (j + 1) ξ / ρ ^ (j + 1))
        + rem hθA hθB πA πB k ρ ξ / ρ ^ k := by
  induction k with
  | zero => simp [rem_zero]
  | succ k ih =>
    have hstep : rem hθA hθB πA πB k ρ ξ
        = (rem hθA hθB πA πB (k + 1) ρ ξ + qCoeff hθA hθB πA πB (k + 1) ξ) / ρ := by
      rw [rem_succ]
      field_simp
      ring
    rw [ih, Finset.sum_range_succ, hstep]
    field_simp
    ring

theorem abs_Del_sub_sum_le (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1)
    (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (k : ℕ) (ξ : Config KA KB) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ρ : ℝ in atTop,
      |Rational.Del hθA hθB πA πB ρ ξ
          - ∑ j ∈ Finset.range k, qCoeff hθA hθB πA πB (j + 1) ξ / ρ ^ (j + 1)|
        ≤ C / ρ ^ (k + 1) := by
  set C := |qCoeff hθA hθB πA πB (k + 1) ξ| + 1 with hC
  refine ⟨C, by positivity, ?_⟩
  have hb := (tendsto_mul_rem hπA hsA hπB hsB k ξ).abs.eventually_le_const
    (by simp [hC] : |qCoeff hθA hθB πA πB (k + 1) ξ| < C)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hb] with ρ hρ hbb
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hpow : (0 : ℝ) < ρ ^ k := pow_pos hρ k
  rw [Del_eq_sum_add k hρ0 ξ, add_sub_cancel_left, abs_div, abs_of_pos hpow]
  rw [div_le_div_iff₀ hpow (by positivity)]
  have hexp : ρ ^ (k + 1) = ρ * ρ ^ k := by ring
  have habs : |rem hθA hθB πA πB k ρ ξ| * ρ = |ρ * rem hθA hθB πA πB k ρ ξ| := by
    rw [abs_mul, abs_of_pos hρ]
    ring
  calc |rem hθA hθB πA πB k ρ ξ| * ρ ^ (k + 1)
      = (|rem hθA hθB πA πB k ρ ξ| * ρ) * ρ ^ k := by rw [hexp]; ring
    _ = |ρ * rem hθA hθB πA πB k ρ ξ| * ρ ^ k := by rw [habs]
    _ ≤ C * ρ ^ k := by
        exact mul_le_mul_of_nonneg_right hbb (le_of_lt hpow)

end Rhone.Coalescent.Closure
