/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Converse.Sign
public import Rhone.Probability.Converse.Source
public import Rhone.Coalescent.Closure.Expansion
public import Rhone.Coalescent.Closure.NonProductWitness

/-! # Vanishing `1/ρ` coefficients of `q` and the `t ≤ 1` product-family converse -/

@[expose] public section

namespace Rhone.Coalescent.Converse

open Filter Topology Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config
open Analysis.RecombinationExpansion Probability.RecombinationExpansion

section Coefficients

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {hθA : 0 < θA} {hθB : 0 < θB}

theorem rem_and_qCoeff_eq_zero (ξ : Config KA KB)
    (h : ∀ᶠ ρ : ℝ in atTop, Rational.Del hθA hθB πA πB ρ ξ = 0) (k : ℕ) :
    (∀ᶠ ρ : ℝ in atTop, Closure.rem hθA hθB πA πB k ρ ξ = 0)
      ∧ Closure.qCoeff hθA hθB πA πB k ξ = 0 := by
  induction k with
  | zero => exact ⟨h, rfl⟩
  | succ k ih =>
    obtain ⟨hrem, _⟩ := ih
    have hq : Closure.qCoeff hθA hθB πA πB (k + 1) ξ = 0 := by
      have ht : Tendsto (fun ρ : ℝ => ρ * Closure.rem hθA hθB πA πB k ρ ξ) atTop (𝓝 0) := by
        refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
        filter_upwards [hrem] with ρ hρ
        rw [hρ, mul_zero]
      exact ht.limUnder_eq
    refine ⟨?_, hq⟩
    filter_upwards [hrem] with ρ hρ
    rw [Closure.rem_succ, hρ, hq, mul_zero, sub_zero]

theorem qCoeff_eq_zero_of_eq_qHat (ξ : Config KA KB) (k : ℕ)
    (h : ∀ ρ : ℝ, 0 ≤ ρ → Rational.qAt hθA hθB πA πB ρ ξ = qHat θA θB πA πB ξ) :
    Closure.qCoeff hθA hθB πA πB k ξ = 0 := by
  refine (rem_and_qCoeff_eq_zero ξ ?_ k).2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ
  change Rational.qAt hθA hθB πA πB ρ ξ - qHat θA θB πA πB ξ = 0
  rw [h ρ hρ, sub_self]

theorem exists_ne_qHat_of_qCoeff_ne_zero (ξ : Config KA KB) (k : ℕ)
    (h : Closure.qCoeff hθA hθB πA πB k ξ ≠ 0) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ Rational.qAt hθA hθB πA πB ρ ξ ≠ qHat θA θB πA πB ξ := by
  by_contra hc
  push Not at hc
  exact h (qCoeff_eq_zero_of_eq_qHat ξ k fun ρ hρ => hc ρ hρ)

theorem qCoeff_eq_zero_of_min_le_one (ξ : Config KA KB) (k : ℕ)
    (hmin : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) : Closure.qCoeff hθA hθB πA πB k ξ = 0 :=
  qCoeff_eq_zero_of_eq_qHat ξ k fun _ρ hρ =>
    Probability.Denominator.eq_qHat_of_min_le_one hθA hθB hρ
      (Rational.qAt_isSolution (πA := πA) (πB := πB) hθA hθB hρ) ξ hmin

variable (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
  (hsB : ∑ j, πB j = 1)
include hπA hsA hπB hsB

theorem L0_qCoeffTwo_of_t_zero (ξ : Config KA KB) (ht : ξ.t = 0) (hn : 2 ≤ ξ.n) :
    L0 θA θB πA πB (Closure.qCoeff hθA hθB πA πB 2) ξ = 0 := by
  have h := Closure.L1_qCoeff_succ (hθA := hθA) (hθB := hθB) hπA hsA hπB hsB 1 ξ hn
  rw [L1_of_t_eq_zero _ ht] at h
  linarith

theorem twoL1_qCoeffTwo (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    2 * L1 (Closure.qCoeff hθA hθB πA πB 2) ξ = -L0 θA θB πA πB (twoQ1 θA θB πA πB) ξ := by
  have h := Closure.L1_qCoeff_succ (hθA := hθA) (hθB := hθB) hπA hsA hπB hsB 0 ξ hn
  have hfun : Closure.qCoeff hθA hθB πA πB 1 = fun η => (2 : ℝ)⁻¹ * twoQ1 θA θB πA πB η := by
    funext η
    rw [Closure.qCoeff_one_eq (hθA := hθA) (hθB := hθB) hπA hsA hπB hsB η]
    ring
  rw [hfun, Rational.L0_smul] at h
  linarith

end Coefficients

section Ray

noncomputable def piOf {K : ℕ} (β : Fin K → ℝ) : Fin K → ℝ := fun k => β k / ∑ l, β l

variable {K : ℕ} {β : Fin K → ℝ}

theorem sum_beta_pos (hβ : ∀ k, 0 < β k) (hK : 0 < K) : 0 < ∑ k, β k := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact Finset.sum_pos (fun k _ => hβ k) Finset.univ_nonempty

theorem piOf_pos (hβ : ∀ k, 0 < β k) (hK : 0 < K) (k : Fin K) : 0 < piOf β k :=
  div_pos (hβ k) (sum_beta_pos hβ hK)

theorem sum_piOf (hβ : ∀ k, 0 < β k) (hK : 0 < K) : ∑ k, piOf β k = 1 := by
  simp only [piOf]
  rw [← Finset.sum_div, div_self (ne_of_gt (sum_beta_pos hβ hK))]

theorem alpha_ray (hβ : ∀ k, 0 < β k) (hK : 0 < K) (ε : ℝ) :
    (fun k => (ε * ∑ l, β l) * piOf β k) = fun k => ε * β k := by
  funext k
  have hs : (∑ l, β l) ≠ 0 := ne_of_gt (sum_beta_pos hβ hK)
  simp only [piOf]
  field_simp

end Ray

section Theorem2Prime

variable {KA KB : ℕ} {βA : Fin KA → ℝ} {βB : Fin KB → ℝ}

noncomputable def qTwoRay (βA : Fin KA → ℝ) (βB : Fin KB → ℝ) (ε : ℝ) (ξ : Config KA KB) :
    ℝ :=
  if h : (0 < ε * ∑ k, βA k) ∧ (0 < ε * ∑ k, βB k) then
    Closure.qCoeff h.1 h.2 (piOf βA) (piOf βB) 2 ξ
  else 0

theorem qTwoRay_eq {ε : ℝ} (h1 : 0 < ε * ∑ k, βA k) (h2 : 0 < ε * ∑ k, βB k) :
    qTwoRay βA βB ε = Closure.qCoeff h1 h2 (piOf βA) (piOf βB) 2 := by
  funext ξ
  rw [qTwoRay, dite_eq_left ⟨h1, h2⟩]

noncomputable def gRay (βA : Fin KA → ℝ) (βB : Fin KB → ℝ) (ε : ℝ) (a : Fin KA → ℕ)
    (b : Fin KB → ℕ) : ℝ :=
  Probability.Converse.gVal (ε * ∑ k, βA k) (ε * ∑ k, βB k) (piOf βA) (piOf βB) (qTwoRay βA βB ε) a
      b

@[simp] theorem cfg0_n (a : Fin KA → ℕ) (b : Fin KB → ℕ) :
    (Probability.Converse.cfg0 a b).n = (∑ i, a i) + ∑ j, b j := by
  simp [Config.n, Config.sumA, Config.sumB, Probability.Converse.cfg0_t]

variable (hβA : ∀ k, 0 < βA k) (hβB : ∀ k, 0 < βB k) (hKA : 2 ≤ KA) (hKB : 2 ≤ KB)
include hβA hβB hKA hKB

theorem rayRec : Probability.Converse.RayRec βA βB (gRay βA βB) := by
  have hKA' : 0 < KA := by omega
  have hKB' : 0 < KB := by omega
  have hθbA : (0 : ℝ) < ∑ k, βA k := sum_beta_pos hβA hKA'
  have hθbB : (0 : ℝ) < ∑ k, βB k := sum_beta_pos hβB hKB'
  have hπA : ∀ i, 0 < piOf βA i := fun i => piOf_pos hβA hKA' i
  have hπB : ∀ j, 0 < piOf βB j := fun j => piOf_pos hβB hKB' j
  have hsA : ∑ i, piOf βA i = 1 := sum_piOf hβA hKA'
  have hsB : ∑ j, piOf βB j = 1 := sum_piOf hβB hKB'
  refine ⟨?_, ?_, ?_⟩
  · intro ε a b hle
    rw [gRay, Probability.Converse.gVal]
    by_cases hε : 0 < ε
    · have h1 : (0 : ℝ) < ε * ∑ k, βA k := mul_pos hε hθbA
      have h2 : (0 : ℝ) < ε * ∑ k, βB k := mul_pos hε hθbB
      rw [qTwoRay_eq h1 h2,
        qCoeff_eq_zero_of_min_le_one (Probability.Converse.cfg0 a b) 2
            (Or.inl (by rw [Probability.Converse.cfg0_nA]; omega)),
        zero_div]
    · rw [qTwoRay, dite_eq_right, zero_div]
      rintro ⟨hc, -⟩
      exact hε (by nlinarith)
  · intro ε a b hle
    rw [gRay, Probability.Converse.gVal]
    by_cases hε : 0 < ε
    · have h1 : (0 : ℝ) < ε * ∑ k, βA k := mul_pos hε hθbA
      have h2 : (0 : ℝ) < ε * ∑ k, βB k := mul_pos hε hθbB
      rw [qTwoRay_eq h1 h2,
        qCoeff_eq_zero_of_min_le_one (Probability.Converse.cfg0 a b) 2
            (Or.inr (by rw [Probability.Converse.cfg0_nB]; omega)),
        zero_div]
    · rw [qTwoRay, dite_eq_right, zero_div]
      rintro ⟨hc, -⟩
      exact hε (by nlinarith)
  · intro ε hε a b ha hb
    have h1 : (0 : ℝ) < ε * ∑ k, βA k := mul_pos hε hθbA
    have h2 : (0 : ℝ) < ε * ∑ k, βB k := mul_pos hε hθbB
    have hfun := qTwoRay_eq (βA := βA) (βB := βB) h1 h2
    have hL0 : L0 (ε * ∑ k, βA k) (ε * ∑ k, βB k) (piOf βA) (piOf βB)
        (qTwoRay βA βB ε) (Probability.Converse.cfg0 a b) = 0 := by
      rw [hfun]
      exact L0_qCoeffTwo_of_t_zero (fun i => (hπA i).le) hsA (fun j => (hπB j).le) hsB
        (Probability.Converse.cfg0 a b) (Probability.Converse.cfg0_t a b) (by rw [cfg0_n]; omega)
    have hsig : ∀ i j, a i ≠ 0 → b j ≠ 0 →
        sigmaOf (qTwoRay βA βB ε) ((Probability.Converse.cfg0 a b).mergeAB i j)
          = 2 * (qOne (ε * ∑ k, βA k) (piOf βA) a * qOne (ε * ∑ k, βB k) (piOf βB) b)
            * Probability.Converse.Gcoef (ε * ∑ k, βA k) (piOf βA) a i
            * Probability.Converse.Gcoef (ε * ∑ k, βB k) (piOf βB) b j := by
      intro i j hai hbj
      refine Probability.Converse.sigma_cfg1_eq h1 hπA h2 hπB a b hai hbj ?_
      rw [hfun]
      refine twoL1_qCoeffTwo (fun i' => (hπA i').le) hsA (fun j' => (hπB j').le) hsB
        (Probability.Converse.cfg1 a b i j) ?_
      have hn := Config.n_mergeAB (ξ := Probability.Converse.cfg0 a b) (i := i) (j := j) hai hbj
      rw [cfg0_n] at hn
      change 2 ≤ ((Probability.Converse.cfg0 a b).mergeAB i j).n
      omega
    have hrec := Probability.Converse.gRec h1 hπA h2 hπB (q2 := qTwoRay βA βB ε) a b hL0 hsig
    rw [Probability.Converse.Phi_eq_PhiA hsA a, Probability.Converse.Phi_eq_PhiA hsB b, alpha_ray
        hβA hKA' ε,
      alpha_ray hβB hKB' ε] at hrec
    exact hrec

theorem lead_gRay (a : Fin KA → ℕ) (b : Fin KB → ℕ) (ha : 2 ≤ ∑ i, a i)
    (hb : 2 ≤ ∑ j, b j) : Probability.Converse.LeadPos
        (Probability.Converse.mu a + Probability.Converse.mu b) (fun ε => gRay βA βB ε a b) :=
  Probability.Converse.ord_sign_g hβA hKA hβB hKB (rayRec hβA hβB hKA hKB) ((∑ i, a i) + ∑ j, b j) a
      b le_rfl ha hb

omit hβA hβB hKA hKB in
theorem Gcoef_ray {K : ℕ} {β : Fin K → ℝ} (hβ : ∀ k, 0 < β k) (hK : 0 < K) (ε : ℝ)
    (m : Fin K → ℕ) (i : Fin K) :
    Probability.Converse.Gcoef (ε * ∑ l, β l) (piOf β) m i = Probability.Converse.GcoefA
        (fun k => ε * β k) m i := by
  rw [Probability.Converse.Gcoef_eq_GcoefA (sum_piOf hβ hK) m i, alpha_ray hβ hK ε]

omit hβA hβB hKA hKB in
theorem exists_c_eq_one {KA KB : ℕ} (ξ : Config KA KB) (ht : ξ.t = 1) :
    ∃ i₀ j₀, ξ.c i₀ j₀ = 1 := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ i : Fin KA, ∀ j : Fin KB, ξ.c i j = 0 := by
    intro i j
    have hle : ξ.c i j ≤ ξ.t := by
      refine le_trans (ξ.le_cRow i j) ?_
      rw [ξ.t_eq_sum_cRow]
      exact Finset.single_le_sum (f := fun i' => ξ.cRow i')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := hcon i j
    omega
  have hzt : ξ.t = 0 := by
    rw [Config.t]
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hz i j
  omega

theorem lead_ratio (ξ : Config KA KB) (hnA : 2 ≤ ξ.nA) (hnB : 2 ≤ ξ.nB) (ht : ξ.t ≤ 1) :
    ∃ hF : ℝ → ℝ, Probability.Converse.LeadPos
        (Probability.Converse.mu ξ.mA + Probability.Converse.mu ξ.mB) hF ∧
      ∀ ε : ℝ, 0 < ε → qTwoRay βA βB ε ξ
        = (qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA
            * qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB) * hF ε := by
  have hKA' : 0 < KA := by omega
  have hKB' : 0 < KB := by omega
  have hθbA : (0 : ℝ) < ∑ k, βA k := sum_beta_pos hβA hKA'
  have hθbB : (0 : ℝ) < ∑ k, βB k := sum_beta_pos hβB hKB'
  have hπA : ∀ i, 0 < piOf βA i := fun i => piOf_pos hβA hKA' i
  have hπB : ∀ j, 0 < piOf βB j := fun j => piOf_pos hβB hKB' j
  have hsA : ∑ i, piOf βA i = 1 := sum_piOf hβA hKA'
  have hsB : ∑ j, piOf βB j = 1 := sum_piOf hβB hKB'
  have hmA : 2 ≤ ∑ i, ξ.mA i := by rw [Config.sum_mA]; omega
  have hmB : 2 ≤ ∑ j, ξ.mB j := by rw [Config.sum_mB]; omega
  have hgpos := lead_gRay hβA hβB hKA hKB ξ.mA ξ.mB hmA hmB
  rcases Nat.lt_or_ge ξ.t 1 with h0 | h1
  · have ht0 : ξ.t = 0 := by omega
    have hxi : ξ = Probability.Converse.cfg0 ξ.mA ξ.mB := (sectorBase_eq_self ht0).symm
    refine ⟨fun ε => gRay βA βB ε ξ.mA ξ.mB, hgpos, fun ε hε => ?_⟩
    have hP : qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA
        * qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB ≠ 0 :=
      mul_ne_zero (Probability.Converse.qOne_ne_zero (mul_pos hε hθbA) hπA _)
        (Probability.Converse.qOne_ne_zero (mul_pos hε hθbB) hπB _)
    conv_lhs => rw [hxi]
    simp only [gRay, Probability.Converse.gVal]
    field_simp
    rw [mul_assoc, mul_div_assoc, div_self hP, mul_one]
  · have ht1 : ξ.t = 1 := by omega
    obtain ⟨i₀, j₀, hc⟩ := exists_c_eq_one ξ ht1
    have hmAi : ξ.mA i₀ ≠ 0 := by
      have hr1 : ξ.c i₀ j₀ ≤ ξ.cRow i₀ := ξ.le_cRow i₀ j₀
      have hr2 : ξ.cRow i₀ ≤ ξ.mA i₀ := Nat.le_add_left _ _
      omega
    have hmBj : ξ.mB j₀ ≠ 0 := by
      have hr1 : ξ.c i₀ j₀ ≤ ξ.cCol j₀ := ξ.le_cCol i₀ j₀
      have hr2 : ξ.cCol j₀ ≤ ξ.mB j₀ := Nat.le_add_left _ _
      omega
    have hxi : ξ = Probability.Converse.cfg1 ξ.mA ξ.mB i₀ j₀ :=
        Probability.Converse.eq_mergeAB_of_t_eq_one ξ ht1 hc
    refine ⟨fun ε => gRay βA βB ε ξ.mA ξ.mB
      + 2 * (Probability.Converse.GcoefA (fun k => ε * βA k) ξ.mA i₀
          * Probability.Converse.GcoefA (fun k => ε * βB k) ξ.mB j₀), ?_, fun ε hε => ?_⟩
    · refine hgpos.add_nonneg ?_
      refine (((Probability.Converse.lead_G hβA hKA hmA hmAi).mul
          (Probability.Converse.lead_G hβB hKB hmB hmBj)).const_mul
        (by norm_num : (0 : ℝ) < 2)).congr' ?_
      filter_upwards with ε
      ring
    · have h1 : (0 : ℝ) < ε * ∑ k, βA k := mul_pos hε hθbA
      have h2 : (0 : ℝ) < ε * ∑ k, βB k := mul_pos hε hθbB
      have hP : qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA
          * qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB ≠ 0 :=
        mul_ne_zero (Probability.Converse.qOne_ne_zero h1 hπA _)
            (Probability.Converse.qOne_ne_zero h2 hπB _)
      have hn2 : 2 ≤ (Probability.Converse.cfg1 ξ.mA ξ.mB i₀ j₀).n := by
        have hnn := congrArg Config.n hxi
        have hb1 : ξ.nA ≤ ξ.n := ξ.nA_le_n
        have hb2 : ξ.nB ≤ ξ.n := ξ.nB_le_n
        omega
      have hsig : sigmaOf (qTwoRay βA βB ε) ξ
          = 2 * (qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA
              * qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB)
            * Probability.Converse.Gcoef (ε * ∑ k, βA k) (piOf βA) ξ.mA i₀
            * Probability.Converse.Gcoef (ε * ∑ k, βB k) (piOf βB) ξ.mB j₀ := by
        conv_lhs => rw [hxi]
        refine Probability.Converse.sigma_cfg1_eq h1 hπA h2 hπB ξ.mA ξ.mB hmAi hmBj ?_
        rw [qTwoRay_eq h1 h2]
        exact twoL1_qCoeffTwo (fun i' => (hπA i').le) hsA (fun j' => (hπB j').le) hsB
          (Probability.Converse.cfg1 ξ.mA ξ.mB i₀ j₀) hn2
      have hsb : sectorBase ξ = Probability.Converse.cfg0 ξ.mA ξ.mB := rfl
      have hsplit : qTwoRay βA βB ε ξ
          = qTwoRay βA βB ε (Probability.Converse.cfg0 ξ.mA ξ.mB) + sigmaOf (qTwoRay βA βB ε) ξ :=
              by
        simp only [sigmaOf, hsb]
        ring
      have hg : qTwoRay βA βB ε (Probability.Converse.cfg0 ξ.mA ξ.mB)
          = (qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA
              * qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB) * gRay βA βB ε ξ.mA ξ.mB := by
        simp only [gRay, Probability.Converse.gVal]
        field_simp
        rw [mul_assoc, mul_div_assoc, div_self hP, mul_one]
      rw [hsplit, hg, hsig, Gcoef_ray hβA hKA' ε, Gcoef_ray hβB hKB' ε]
      ring

theorem qCoeffTwo_sign (ξ : Config KA KB) (hnA : 2 ≤ ξ.nA) (hnB : 2 ≤ ξ.nB) (ht : ξ.t ≤ 1) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      0 < (-1 : ℝ) ^ (Probability.Converse.mu ξ.mA + Probability.Converse.mu ξ.mB) * qTwoRay βA βB ε
          ξ := by
  have hKA' : 0 < KA := by omega
  have hKB' : 0 < KB := by omega
  have hθbA : (0 : ℝ) < ∑ k, βA k := sum_beta_pos hβA hKA'
  have hθbB : (0 : ℝ) < ∑ k, βB k := sum_beta_pos hβB hKB'
  have hπA : ∀ i, 0 < piOf βA i := fun i => piOf_pos hβA hKA' i
  have hπB : ∀ j, 0 < piOf βB j := fun j => piOf_pos hβB hKB' j
  obtain ⟨hF, hFlead, hFeq⟩ := lead_ratio hβA hβB hKA hKB ξ hnA hnB ht
  obtain ⟨ε₀, hε₀, hsign⟩ := hFlead.eventually_sign
  refine ⟨ε₀, hε₀, fun ε hε => ?_⟩
  have hεpos : (0 : ℝ) < ε := hε.1
  have hqA : (0 : ℝ) < qOne (ε * ∑ k, βA k) (piOf βA) ξ.mA :=
    Probability.Converse.qOne_pos (mul_pos hεpos hθbA) hπA _
  have hqB : (0 : ℝ) < qOne (ε * ∑ k, βB k) (piOf βB) ξ.mB :=
    Probability.Converse.qOne_pos (mul_pos hεpos hθbB) hπB _
  rw [hFeq ε hεpos]
  have hs := hsign ε hε
  nlinarith [mul_pos hqA hqB]

theorem qCoeffTwo_ne_zero (ξ : Config KA KB) (hnA : 2 ≤ ξ.nA) (hnB : 2 ≤ ξ.nB)
    (ht : ξ.t ≤ 1) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, qTwoRay βA βB ε ξ ≠ 0 := by
  obtain ⟨ε₀, hε₀, hsign⟩ := qCoeffTwo_sign hβA hβB hKA hKB ξ hnA hnB ht
  refine ⟨ε₀, hε₀, fun ε hε hz => ?_⟩
  have hs := hsign ε hε
  rw [hz, mul_zero] at hs
  exact lt_irrefl 0 hs

end Theorem2Prime

section Bridge

variable {KA KB : ℕ}

theorem exists_admissible_q_ne_qHat_t_le_one (hKA : 2 ≤ KA) (hKB : 2 ≤ KB)
    (ξ : Config KA KB) (hnA : 2 ≤ ξ.nA) (hnB : 2 ≤ ξ.nB) (ht : ξ.t ≤ 1) :
    ∃ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
      (∀ i, 0 < πA i) ∧ (∑ i, πA i = 1) ∧ (∀ j, 0 < πB j) ∧ (∑ j, πB j = 1) ∧
      ∃ (ρ : ℝ) (hρ : 0 ≤ ρ),
        LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ ≠ qHat θA θB πA πB ξ := by
  have hKA' : 0 < KA := by omega
  have hKB' : 0 < KB := by omega
  have hβA : ∀ _k : Fin KA, (0 : ℝ) < 1 := fun _ => one_pos
  have hβB : ∀ _k : Fin KB, (0 : ℝ) < 1 := fun _ => one_pos
  obtain ⟨ε₀, hε₀, hne⟩ :=
    qCoeffTwo_ne_zero (βA := fun _ => (1 : ℝ)) (βB := fun _ => (1 : ℝ)) hβA hβB hKA hKB
      ξ hnA hnB ht
  have hεpos : (0 : ℝ) < ε₀ / 2 := by linarith
  have hεmem : ε₀ / 2 ∈ Set.Ioo (0 : ℝ) ε₀ := ⟨hεpos, by linarith⟩
  have hθbA : (0 : ℝ) < ∑ _k : Fin KA, (1 : ℝ) := sum_beta_pos hβA hKA'
  have hθbB : (0 : ℝ) < ∑ _k : Fin KB, (1 : ℝ) := sum_beta_pos hβB hKB'
  have h1 : (0 : ℝ) < (ε₀ / 2) * ∑ _k : Fin KA, (1 : ℝ) := mul_pos hεpos hθbA
  have h2 : (0 : ℝ) < (ε₀ / 2) * ∑ _k : Fin KB, (1 : ℝ) := mul_pos hεpos hθbB
  have hq : Closure.qCoeff h1 h2 (piOf fun _ => (1 : ℝ)) (piOf fun _ => (1 : ℝ)) 2 ξ ≠ 0 := by
    have hz := hne (ε₀ / 2) hεmem
    rwa [qTwoRay_eq h1 h2] at hz
  obtain ⟨ρ, hρ, hne'⟩ := exists_ne_qHat_of_qCoeff_ne_zero (hθA := h1) (hθB := h2) ξ 2 hq
  refine ⟨_, _, _, _, h1, h2, fun i => piOf_pos hβA hKA' i, sum_piOf hβA hKA',
    fun j => piOf_pos hβB hKB' j, sum_piOf hβB hKB', ρ, hρ, ?_⟩
  rwa [Rational.qAt_eq_q h1 h2 hρ] at hne'

theorem product_family_iff (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) :
    (∀ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (hθA : 0 < θA) (hθB : 0 < θB),
        (∀ i, 0 < πA i) → (∑ i, πA i = 1) → (∀ j, 0 < πB j) → (∑ j, πB j = 1) →
        ∀ (ρ : ℝ) (hρ : 0 ≤ ρ),
          LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ = qHat θA θB πA πB ξ)
      ↔ (ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) := by
  constructor
  · intro hall
    by_contra hmin
    push Not at hmin
    obtain ⟨hnA, hnB⟩ := hmin
    rcases Nat.lt_or_ge ξ.t 2 with ht | ht
    · obtain ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB, ρ, hρ, hne⟩ :=
        exists_admissible_q_ne_qHat_t_le_one hKA hKB ξ (by omega) (by omega) (by omega)
      exact hne (hall θA θB πA πB hθA hθB hπA hsA hπB hsB ρ hρ)
    · obtain ⟨θA, θB, πA, πB, hθA, hθB, hπA, hsA, hπB, hsB, ρ, hρ, hne⟩ :=
        Closure.exists_admissible_q_ne_qHat hKA hKB ξ ht
      exact hne (hall θA θB πA πB hθA hθB hπA hsA hπB hsB ρ hρ)
  · intro hmin θA θB πA πB hθA hθB hπA hsA hπB hsB ρ hρ
    have hqq := Probability.Denominator.eq_qHat_of_min_le_one hθA hθB hρ
      (Rational.qAt_isSolution (πA := πA) (πB := πB) hθA hθB hρ) ξ hmin
    rwa [Rational.qAt_eq_q hθA hθB hρ] at hqq

end Bridge

end Rhone.Coalescent.Converse
