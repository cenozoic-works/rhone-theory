/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.Rational.Limit
public import Rhone.Probability.RecombinationExpansion.Expansion

/-! # The `1/ρ` coefficient of `Δ = q − q̂`, and the `x⁰` line of order matching -/

@[expose] public section

namespace Rhone.Coalescent.Rational

open Filter Topology Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config
open Analysis.RecombinationExpansion Probability.RecombinationExpansion

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def Del (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ρ : ℝ) (ξ : Config KA KB) : ℝ :=
  qAt hθA hθB πA πB ρ ξ - qHat θA θB πA πB ξ

theorem Del_eq (hθA : 0 < θA) (hθB : 0 < θB) (ρ : ℝ) :
    Del hθA hθB πA πB ρ
      = fun η : Config KA KB => qAt hθA hθB πA πB ρ η - qHat θA θB πA πB η := rfl

theorem tendsto_Del_zero (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    Tendsto (fun ρ => Del hθA hθB πA πB ρ ξ) atTop (𝓝 0) := by
  have h := (tendsto_q_qHat hθA hθB hπA hsA hπB hsB ξ).sub_const
    (qHat θA θB πA πB ξ)
  simpa [Del, qHat] using h

theorem exists_ratio_Del (hθA : 0 < θA) (hθB : 0 < θB) (ξ : Config KA KB) :
    ∃ u d : Polynomial ℝ, d ≠ 0 ∧
      (fun ρ => Del hθA hθB πA πB ρ ξ)
        =ᶠ[atTop] fun ρ => Polynomial.eval ρ u / Polynomial.eval ρ d := by
  obtain ⟨p, d, hd, _, hq⟩ := Algebra.Rational.exists_ratio_config (πA := πA) (πB := πB) hθA hθB ξ
  refine ⟨p - Polynomial.C (qHat θA θB πA πB ξ) * d, d, hd, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    Polynomial.eventually_atTop_not_isRoot d hd] with ρ h1 h2
  have hdne : Polynomial.eval ρ d ≠ 0 := fun h => h2 h
  simp only [Del, qAt_eq_q hθA hθB h1, hq ρ h1 hdne, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  field_simp

theorem exists_tendsto_mul_Del (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    ∃ L : ℝ, Tendsto (fun ρ => ρ * Del hθA hθB πA πB ρ ξ) atTop (𝓝 L) := by
  obtain ⟨u, d, hd, heq⟩ := exists_ratio_Del (πA := πA) (πB := πB) hθA hθB ξ
  have hdeg : u.degree < d.degree :=
    (Polynomial.div_tendsto_atTop_zero_iff_degree_lt u d hd).mp
      ((tendsto_Del_zero hθA hθB hπA hsA hπB hsB ξ).congr' heq)
  have hdeg2 : (Polynomial.X * u).degree ≤ d.degree := by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · rw [Polynomial.degree_mul, Polynomial.degree_X, add_comm]
      exact Nat.WithBot.add_one_le_of_lt hdeg
  have heq2 : (fun ρ => ρ * Del hθA hθB πA πB ρ ξ)
      =ᶠ[atTop] fun ρ => Polynomial.eval ρ (Polynomial.X * u) / Polynomial.eval ρ d := by
    filter_upwards [heq] with ρ he
    rw [he]
    simp [mul_div_assoc]
  rcases lt_or_eq_of_le hdeg2 with h | h
  · exact ⟨0, (Polynomial.div_tendsto_atTop_zero_of_degree_lt _ d h).congr' heq2.symm⟩
  · exact ⟨(Polynomial.X * u).leadingCoeff / d.leadingCoeff,
      (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq _ d h).congr' heq2.symm⟩

noncomputable def qCoeffOne (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (ξ : Config KA KB) : ℝ :=
  (exists_tendsto_mul_Del hθA hθB hπA hsA hπB hsB ξ).choose

theorem tendsto_qCoeffOne (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    Tendsto (fun ρ => ρ * Del hθA hθB πA πB ρ ξ) atTop
      (𝓝 (qCoeffOne hθA hθB hπA hsA hπB hsB ξ)) :=
  (exists_tendsto_mul_Del hθA hθB hπA hsA hπB hsB ξ).choose_spec

theorem L0_zero (ξ : Config KA KB) : L0 θA θB πA πB (fun _ => (0 : ℝ)) ξ = 0 := by
  simp [L0, Lop, rhs_zero]

theorem L1_qCoeffOne (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hn : 2 ≤ ξ.n) :
    L1 (qCoeffOne hθA hθB hπA hsA hπB hsB) ξ = twoQ1 θA θB πA πB ξ := by
  have key : ∀ᶠ ρ in atTop,
      L1 (fun η => ρ * Del hθA hθB πA πB ρ η) ξ
        = twoQ1 θA θB πA πB ξ - L0 θA θB πA πB (Del hθA hθB πA πB ρ) ξ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    have hL := LDelta hθA hθB (qAt_isSolution (πA := πA) (πB := πB) hθA hθB
      (le_of_lt hρ)) ξ hn
    rw [← Del_eq hθA hθB ρ, Lop_split] at hL
    rw [L1_smul]
    linarith [hL]
  have h1 := Probability.RecombinationExpansion.tendsto_L1
      (fun ρ : ℝ => fun η => ρ * Del hθA hθB πA πB ρ η)
    (qCoeffOne hθA hθB hπA hsA hπB hsB)
    (fun η => tendsto_qCoeffOne hθA hθB hπA hsA hπB hsB η) ξ
  have h2 : Tendsto (fun ρ : ℝ => twoQ1 θA θB πA πB ξ
        - L0 θA θB πA πB (Del hθA hθB πA πB ρ) ξ) atTop
      (𝓝 (twoQ1 θA θB πA πB ξ - L0 θA θB πA πB (fun _ => (0 : ℝ)) ξ)) :=
    tendsto_const_nhds.sub
        (Probability.RecombinationExpansion.tendsto_L0 (fun ρ : ℝ => Del hθA hθB πA πB ρ)
      (fun _ => (0 : ℝ)) (fun η => tendsto_Del_zero hθA hθB hπA hsA hπB hsB η) ξ)
  rw [L0_zero, sub_zero] at h2
  exact tendsto_nhds_unique (h1.congr' key) h2

theorem qCoeffOne_eq_zero_of_eventually (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (h : ∀ᶠ ρ : ℝ in atTop, qAt hθA hθB πA πB ρ ξ = qHat θA θB πA πB ξ) :
    qCoeffOne hθA hθB hπA hsA hπB hsB ξ = 0 := by
  refine tendsto_nhds_unique (tendsto_qCoeffOne hθA hθB hπA hsA hπB hsB ξ) ?_
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h] with ρ hρ
  simp [Del, hρ]

theorem qCoeffOne_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (h : ∀ ρ : ℝ, 0 ≤ ρ → qAt hθA hθB πA πB ρ ξ = qHat θA θB πA πB ξ) :
    qCoeffOne hθA hθB hπA hsA hπB hsB ξ = 0 := by
  refine qCoeffOne_eq_zero_of_eventually hθA hθB hπA hsA hπB hsB ξ ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ
  exact h ρ hρ

theorem exists_ne_qHat_in_sector (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hn : 2 ≤ ξ.n) (h : twoQ1 θA θB πA πB ξ ≠ 0) :
    ∃ η : Config KA KB, (η = ξ ∨ ∃ i j, η = ξ.split i j) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ qAt hθA hθB πA πB ρ η ≠ qHat θA θB πA πB η := by
  by_contra hc
  push Not at hc
  have hzero : ∀ η : Config KA KB, (η = ξ ∨ ∃ i j, η = ξ.split i j) →
      qCoeffOne hθA hθB hπA hsA hπB hsB η = 0 := by
    intro η hη
    exact qCoeffOne_eq_zero hθA hθB hπA hsA hπB hsB η fun ρ hρ => hc η hη ρ hρ
  refine h ?_
  rw [← L1_qCoeffOne hθA hθB hπA hsA hπB hsB ξ hn, L1, hzero ξ (Or.inl rfl)]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_congr rfl
    fun j (_ : j ∈ Finset.univ) => by
      rw [hzero (ξ.split i j) (Or.inr ⟨i, j, rfl⟩), mul_zero]]
  simp

theorem L0_sub (f g : Config KA KB → ℝ) (ξ : Config KA KB) :
    L0 θA θB πA πB (fun η => f η - g η) ξ
      = L0 θA θB πA πB f ξ - L0 θA θB πA πB g ξ :=
  Lop_sub f g ξ

theorem L0_smul (c : ℝ) (f : Config KA KB → ℝ) (ξ : Config KA KB) :
    L0 θA θB πA πB (fun η => c * f η) ξ = c * L0 θA θB πA πB f ξ :=
  Lop_smul c f ξ

noncomputable def coeffDefect (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (ξ : Config KA KB) : ℝ :=
  qCoeffOne hθA hθB hπA hsA hπB hsB ξ - twoQ1 θA θB πA πB ξ / 2

theorem L1_coeffDefect (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hn : 2 ≤ ξ.n) : L1 (coeffDefect hθA hθB hπA hsA hπB hsB) ξ = 0 := by
  have hfun : (coeffDefect hθA hθB hπA hsA hπB hsB : Config KA KB → ℝ)
      = fun η => qCoeffOne hθA hθB hπA hsA hπB hsB η
        - (2 : ℝ)⁻¹ * twoQ1 θA θB πA πB η := by
    funext η; rw [coeffDefect]; ring
  rw [hfun, L1_sub, L1_smul, L1_qCoeffOne hθA hθB hπA hsA hπB hsB ξ hn, L1_twoQ1]
  ring

theorem coeffDefect_eq_zero_of_min_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (hmin : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) : coeffDefect hθA hθB hπA hsA hπB hsB ξ = 0 := by
  have ht : ξ.t ≤ 1 := by
    rcases hmin with h | h
    · have := ξ.t_le_nA; omega
    · have := ξ.t_le_nB; omega
  have h1 : qCoeffOne hθA hθB hπA hsA hπB hsB ξ = 0 := by
    refine qCoeffOne_eq_zero hθA hθB hπA hsA hπB hsB ξ fun ρ hρ => ?_
    exact Probability.Denominator.eq_qHat_of_min_le_one hθA hθB hρ
      (qAt_isSolution (πA := πA) (πB := πB) hθA hθB hρ) ξ hmin
  rw [coeffDefect, h1, twoQ1_eq_zero_of_t_le_one ξ ht]
  ring

theorem L0_coeffDefect_of_t_zero (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (β : Config KA KB)
    (ht : β.t = 0) (hn : 2 ≤ β.n) :
    L0 θA θB πA πB (coeffDefect hθA hθB hπA hsA hπB hsB) β = 0 := by
  have hq1 : L0 θA θB πA πB (qCoeffOne hθA hθB hπA hsA hπB hsB) β = 0 := by
    have hval : ∀ᶠ ρ : ℝ in atTop,
        L0 θA θB πA πB (fun η => ρ * Del hθA hθB πA πB ρ η) β = 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
      have hL := LDelta hθA hθB (qAt_isSolution (πA := πA) (πB := πB) hθA hθB
        (le_of_lt hρ)) β hn
      rw [← Del_eq hθA hθB ρ, Lop_split, L1_of_t_eq_zero _ ht, mul_zero, add_zero] at hL
      rw [L0_smul, hL, twoQ1_eq_zero_of_t_le_one β (by omega), mul_zero]
    have h1 := Probability.RecombinationExpansion.tendsto_L0 (θA := θA) (θB := θB) (πA := πA)
        (πB := πB)
      (fun ρ : ℝ => fun η => ρ * Del hθA hθB πA πB ρ η)
      (qCoeffOne hθA hθB hπA hsA hπB hsB)
      (fun η => tendsto_qCoeffOne hθA hθB hπA hsA hπB hsB η) β
    refine tendsto_nhds_unique h1 (Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [hval] with ρ hρ
    exact hρ.symm
  have hfun : (coeffDefect hθA hθB hπA hsA hπB hsB : Config KA KB → ℝ)
      = fun η => qCoeffOne hθA hθB hπA hsA hπB hsB η
        - (2 : ℝ)⁻¹ * twoQ1 θA θB πA πB η := by
    funext η; rw [coeffDefect]; ring
  rw [hfun, L0_sub, L0_smul, hq1, L0_twoQ1_eq_zero β ht]
  ring

theorem qCoeffOne_eq_half_twoQ1 (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    qCoeffOne hθA hθB hπA hsA hπB hsB ξ = twoQ1 θA θB πA πB ξ / 2 := by
  have main : ∀ N : ℕ, ∀ ζ : Config KA KB, ζ.nA + ζ.nB = N →
      coeffDefect hθA hθB hπA hsA hπB hsB ζ = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro ζ hN
      by_cases hmin : ζ.nA ≤ 1 ∨ ζ.nB ≤ 1
      · exact coeffDefect_eq_zero_of_min_le_one hθA hθB hπA hsA hπB hsB ζ hmin
      · have hA2' : 2 ≤ ζ.nA := by omega
        have hB2' : 2 ≤ ζ.nB := by omega
        have hsector : ∀ η : Config KA KB, η.mA = ζ.mA → η.mB = ζ.mB →
            L1 (coeffDefect hθA hθB hπA hsA hπB hsB) η = 0 := by
          intro η hηA hηB
          refine L1_coeffDefect hθA hθB hπA hsA hπB hsB η
            (Probability.RecombinationExpansion.two_le_n_of_two_le η ?_ ?_)
          · rw [Probability.RecombinationExpansion.nA_of_mA_eq hηA]; exact hA2'
          · rw [Probability.RecombinationExpansion.nB_of_mB_eq hηB]; exact hB2'
        have hconst : ∀ η : Config KA KB, η.mA = ζ.mA → η.mB = ζ.mB →
            coeffDefect hθA hθB hπA hsA hπB hsB η
              = coeffDefect hθA hθB hπA hsA hπB hsB
                  (Probability.RecombinationExpansion.sectorBase ζ) :=
          fun η hηA hηB => Probability.RecombinationExpansion.eq_at_sectorBase (ζ := ζ) hsector η.t
              η rfl hηA hηB
        set β := Probability.RecombinationExpansion.sectorBase ζ with hβ
        have hβt : β.t = 0 := Probability.RecombinationExpansion.t_sectorBase ζ
        have hβA : β.nA = ζ.nA := Probability.RecombinationExpansion.nA_sectorBase ζ
        have hβB : β.nB = ζ.nB := Probability.RecombinationExpansion.nB_sectorBase ζ
        have hβn : 2 ≤ β.n := Probability.RecombinationExpansion.two_le_n_of_two_le β
            (by omega) (by omega)
        have hL0 := L0_coeffDefect_of_t_zero hθA hθB hπA hsA hπB hsB β hβt hβn
        have hsplitm : ∀ (i : Fin KA) (j : Fin KB), β.a i ≠ 0 → β.b j ≠ 0 →
            coeffDefect hθA hθB hπA hsA hπB hsB (β.mergeAB i j)
              = coeffDefect hθA hθB hπA hsA hπB hsB β + (0 : ℝ) := by
          intro i j ha hb
          rw [add_zero, hconst (β.mergeAB i j)
            (by rw [β.mA_mergeAB j ha, Probability.RecombinationExpansion.mA_sectorBase ζ])
            (by rw [β.mB_mergeAB i hb, Probability.RecombinationExpansion.mB_sectorBase ζ]),
            hconst β (Probability.RecombinationExpansion.mA_sectorBase ζ)
                (Probability.RecombinationExpansion.mB_sectorBase ζ)]
        have hres := residual_t_zero (q2 := coeffDefect hθA hθB hπA hsA hπB hsB)
          (σ := fun _ => (0 : ℝ)) β hβt hL0 hsplitm
        have hdropA : (∑ i, (((β.a i * (β.a i - 1) : ℕ) : ℝ) + θA * πA i * ((β.a i : ℕ) : ℝ))
            * coeffDefect hθA hθB hπA hsA hπB hsB (β.dropA i)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hai : β.a i = 0
          · rw [hai]; simp
          · have hlt : (β.dropA i).nA + (β.dropA i).nB < N := by
              have h1 := β.nA_dropA i hai
              have h2 : (β.dropA i).nB = β.nB := rfl
              omega
            rw [ih _ hlt (β.dropA i) rfl, mul_zero]
        have hdropB : (∑ j, (((β.b j * (β.b j - 1) : ℕ) : ℝ) + θB * πB j * ((β.b j : ℕ) : ℝ))
            * coeffDefect hθA hθB hπA hsA hπB hsB (β.dropB j)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hbj : β.b j = 0
          · rw [hbj]; simp
          · have hlt : (β.dropB j).nA + (β.dropB j).nB < N := by
              have h1 := β.nB_dropB j hbj
              have h2 : (β.dropB j).nA = β.nA := rfl
              omega
            rw [ih _ hlt (β.dropB j) rfl, mul_zero]
        have hmerge : (∑ i : Fin KA, ∑ j : Fin KB,
            ((β.coalAB i j : ℕ) : ℝ) * (0 : ℝ)) = 0 := by simp
        rw [hdropA, hdropB, hmerge] at hres
        have hcoef : 0 < ((β.nA * (β.nA - 1) : ℕ) : ℝ) + θA * ((β.nA : ℕ) : ℝ)
            + ((β.nB * (β.nB - 1) : ℕ) : ℝ) + θB * ((β.nB : ℕ) : ℝ) := by
          have h1 : (0 : ℝ) ≤ ((β.nA * (β.nA - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          have h2 : (0 : ℝ) ≤ ((β.nB * (β.nB - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          have h3 : (0 : ℝ) < θA * ((β.nA : ℕ) : ℝ) :=
            mul_pos hθA (by exact_mod_cast (by omega : 0 < β.nA))
          have h4 : (0 : ℝ) ≤ θB * ((β.nB : ℕ) : ℝ) :=
            mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
        have hβzero : coeffDefect hθA hθB hπA hsA hπB hsB β = 0 := by
          rcases mul_eq_zero.1 (by linarith [hres] : (((β.nA * (β.nA - 1) : ℕ) : ℝ)
            + θA * ((β.nA : ℕ) : ℝ) + ((β.nB * (β.nB - 1) : ℕ) : ℝ)
            + θB * ((β.nB : ℕ) : ℝ)) * coeffDefect hθA hθB hπA hsA hπB hsB β = 0) with h | h
          · exact absurd h (ne_of_gt hcoef)
          · exact h
        rw [hconst ζ rfl rfl]
        exact hβzero
  have hz := main (ξ.nA + ξ.nB) ξ rfl
  rw [coeffDefect] at hz
  linarith

theorem exists_ne_qHat_of_twoQ1_ne_zero (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (h : twoQ1 θA θB πA πB ξ ≠ 0) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ qAt hθA hθB πA πB ρ ξ ≠ qHat θA θB πA πB ξ := by
  by_contra hc
  push Not at hc
  have h0 := qCoeffOne_eq_zero hθA hθB hπA hsA hπB hsB ξ fun ρ hρ => hc ρ hρ
  rw [qCoeffOne_eq_half_twoQ1 hθA hθB hπA hsA hπB hsB ξ] at h0
  exact h (by linarith)

theorem qRho_ne_qHat (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB)
    (h : twoQ1 θA θB πA πB ξ ≠ 0) :
    Algebra.Rational.qRho hθA hθB πA πB ξ ≠ RatFunc.C (qHat θA θB πA πB ξ) := by
  intro hEq
  obtain ⟨p, d, hd, hlink, hq⟩ := Algebra.Rational.exists_ratio_config (πA := πA) (πB := πB) hθA hθB
      ξ
  have hp : p = Polynomial.C (qHat θA θB πA πB ξ) * d := by
    refine IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ) ?_
    rw [hlink, hEq, map_mul, RatFunc.algebraMap_C]
  have hev : ∀ᶠ ρ : ℝ in atTop, qAt hθA hθB πA πB ρ ξ = qHat θA θB πA πB ξ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      Polynomial.eventually_atTop_not_isRoot d hd] with ρ h1 h2
    have hdne : Polynomial.eval ρ d ≠ 0 := fun hz => h2 hz
    rw [qAt_eq_q hθA hθB h1, hq ρ h1 hdne, hp, Polynomial.eval_mul, Polynomial.eval_C,
      mul_div_assoc, div_self hdne, mul_one]
  have h0 := qCoeffOne_eq_zero_of_eventually hθA hθB hπA hsA hπB hsB ξ hev
  rw [qCoeffOne_eq_half_twoQ1 hθA hθB hπA hsA hπB hsB ξ] at h0
  exact h (by linarith)

end Rhone.Coalescent.Rational
