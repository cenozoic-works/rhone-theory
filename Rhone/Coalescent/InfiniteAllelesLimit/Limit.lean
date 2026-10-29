/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.InfiniteAllelesLimit.Window
public import Rhone.Coalescent.Rational.Limit

/-! # Steps 3 and 4: `P(ξ_A, ξ_B) → ESF_lab(ξ_A) · ESF_lab(ξ_B)` as `ρ → ∞` -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset Filter Topology Polynomial TwoLocusGenealogy EsfPair
open Probability.InfiniteAlleles LinearAlgebra.Recursion

variable {n K : ℕ} {θ θA θB x : ℝ} {ζ ζA ζB : Blocks n}

noncomputable def risingTailP (θ : ℝ) (k : ℕ) : Polynomial ℝ :=
  ∏ r ∈ Finset.Ico 1 k, (Polynomial.C θ * Polynomial.X + Polynomial.C ((r : ℕ) : ℝ))

theorem risingTailP_eval (θ x : ℝ) (k : ℕ) :
    (risingTailP θ k).eval x = risingTail (θ * x) k := by
  rw [risingTailP, risingTail, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun r _ => by simp

theorem risingTailP_degree_le (θ : ℝ) (k : ℕ) :
    (risingTailP θ k).degree ≤ ((k - 1 : ℕ) : WithBot ℕ) := by
  rw [risingTailP]
  refine (Polynomial.degree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum
    (fun _ _ => (Polynomial.degree_linear_le : _ ≤ (1 : WithBot ℕ)))).trans ?_
  rw [Finset.sum_const, Nat.card_Ico]
  simp

noncomputable def qOnePolyP (θ : ℝ) (m : Fin K → ℕ) : Polynomial ℝ :=
  Polynomial.C (θ ^ obs m / rising θ (∑ i, m i))
    * ∏ i ∈ Finset.univ.filter fun i => m i ≠ 0, risingTailP θ (m i)

theorem qOnePolyP_eval (θ x : ℝ) (m : Fin K → ℕ) :
    (qOnePolyP θ m).eval x = qOnePoly θ x m := by
  rw [qOnePolyP, qOnePoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Finset.prod_congr rfl fun i _ => risingTailP_eval θ x (m i)]
  ring

noncomputable def qOneP (θ : ℝ) (m : Fin K → ℕ) : Polynomial ℝ :=
  Polynomial.X ^ obs m * qOnePolyP θ m

theorem qOneP_eval (θ x : ℝ) (m : Fin K → ℕ) :
    (qOneP θ m).eval x = qOne θ (fun _ => x) m := by
  rw [qOneP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, qOnePolyP_eval,
    qOne_uniform]

theorem qOneP_coeff (θ : ℝ) (m : Fin K → ℕ) : (qOneP θ m).coeff (obs m) = esfLab θ m := by
  have h := Polynomial.coeff_X_pow_mul (qOnePolyP θ m) (obs m) 0
  rw [zero_add] at h
  rw [qOneP, h, Polynomial.coeff_zero_eq_eval_zero, qOnePolyP_eval, qOnePoly_zero]

theorem obs_add_sum_pred (m : Fin K → ℕ) :
    obs m + ∑ i ∈ Finset.univ.filter fun i => m i ≠ 0, (m i - 1) = ∑ i, m i := by
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin K)),
      i ∉ Finset.univ.filter (fun i => m i ≠ 0) → m i = 0 := by
    intro i _ hi
    by_contra hc
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, hc⟩)
  have hstep : ∑ i ∈ Finset.univ.filter fun i => m i ≠ 0, (1 + (m i - 1))
      = ∑ i ∈ Finset.univ.filter fun i => m i ≠ 0, m i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (Finset.mem_filter.1 hi).2
    omega
  rw [obs, ← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.filter fun i => m i ≠ 0)) hsupp, ← hstep, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, mul_one]

theorem qOneP_degree_le (θ : ℝ) (m : Fin K → ℕ) :
    (qOneP θ m).degree ≤ ((∑ i, m i : ℕ) : WithBot ℕ) := by
  have hprod : (∏ i ∈ Finset.univ.filter fun i => m i ≠ 0, risingTailP θ (m i)).degree
      ≤ ((∑ i ∈ Finset.univ.filter fun i => m i ≠ 0, (m i - 1) : ℕ) : WithBot ℕ) := by
    refine (Polynomial.degree_prod_le _ _).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => risingTailP_degree_le θ (m i)
  have hpoly : (qOnePolyP θ m).degree
      ≤ ((∑ i ∈ Finset.univ.filter fun i => m i ≠ 0, (m i - 1) : ℕ) : WithBot ℕ) := by
    refine (Polynomial.degree_mul_le _ _).trans ?_
    refine le_trans (add_le_add Polynomial.degree_C_le hprod) ?_
    rw [zero_add]
  refine (Polynomial.degree_mul_le _ _).trans ?_
  refine le_trans (add_le_add (Polynomial.degree_X_pow_le (obs m)) hpoly) ?_
  rw [← Nat.cast_add, obs_add_sum_pred m]

theorem qOne_piWin (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (θ x : ℝ) :
    qOne θ (piWin ζ x) (mvec ζ) = qOne θ (fun _ => x) (mvec ζ) := by
  rw [qOne, qOne]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : mvec ζ i = 0
  · rw [hi, rising_zero, rising_zero]
  · have hmem : i ∈ Finset.univ.filter fun i => mvec ζ i ≠ 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
    rw [filter_mvec_ne_zero hζ] at hmem
    rw [piWin_of_mem_cols hmem]

theorem coeff_qOne_piWin (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (θ : ℝ) :
    (∑ k : Fin (n + 1), wgtA ζ k * qOne θ
        (piWin ζ (Probability.InfiniteAllelesLimit.xnode ζ.card n k)) (mvec ζ))
      = esfPart n θ ζ := by
  have hdeg : (qOneP θ (mvec ζ)).degree ≤ (n : WithBot ℕ) := by
    have := qOneP_degree_le θ (mvec ζ)
    rwa [sum_mvec hζ] at this
  have hval : ∀ k : Fin (n + 1),
      wgtA ζ k * qOne θ (piWin ζ (Probability.InfiniteAllelesLimit.xnode ζ.card n k)) (mvec ζ)
        = Probability.InfiniteAllelesLimit.exWeight Finset.univ
            (Probability.InfiniteAllelesLimit.xnode ζ.card n) ζ.card k
            * (qOneP θ (mvec ζ)).eval (Probability.InfiniteAllelesLimit.xnode ζ.card n k) := by
    intro k
    rw [wgtA, qOneP_eval, qOne_piWin hζ]
  rw [Finset.sum_congr rfl fun k _ => hval k,
    Probability.InfiniteAllelesLimit.sum_exWeight_xnode ζ.card ζ.card (qOneP θ (mvec ζ)) hdeg, ←
        obs_mvec hζ, qOneP_coeff,
    esfLab_mvec hζ]

theorem mA_cSample {KA KB : ℕ} (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (i : Fin KA) :
    (cSample σA σB).mA i = countIn σA i (Finset.univ : Finset (Fin n)) := by
  have hset : ∀ j : Fin KB,
      ((Finset.univ.filter fun k : Fin n => σA k = i).filter fun k => σB k = j)
        = Finset.univ.filter fun k : Fin n => σA k = i ∧ σB k = j := by
    intro j
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfib := Finset.card_eq_sum_card_fiberwise (f := σB)
    (s := Finset.univ.filter fun k : Fin n => σA k = i)
    (t := (Finset.univ : Finset (Fin KB))) fun x _ => Finset.mem_univ _
  rw [Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin KB))) =>
    congrArg Finset.card (hset j)] at hfib
  simp only [Config.mA, Config.cRow, cSample, countIn, zero_add]
  exact hfib.symm

theorem mB_cSample {KA KB : ℕ} (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (j : Fin KB) :
    (cSample σA σB).mB j = countIn σB j (Finset.univ : Finset (Fin n)) := by
  have hset : ∀ i : Fin KA,
      ((Finset.univ.filter fun k : Fin n => σB k = j).filter fun k => σA k = i)
        = Finset.univ.filter fun k : Fin n => σA k = i ∧ σB k = j := by
    intro i
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hfib := Finset.card_eq_sum_card_fiberwise (f := σA)
    (s := Finset.univ.filter fun k : Fin n => σB k = j)
    (t := (Finset.univ : Finset (Fin KA))) fun x _ => Finset.mem_univ _
  rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin KA))) =>
    congrArg Finset.card (hset i)] at hfib
  simp only [Config.mB, Config.cCol, cSample, countIn, zero_add]
  exact hfib.symm

theorem mA_wSample (ζA ζB : Blocks n) : (wSample ζA ζB).mA = mvec ζA :=
  funext fun i => mA_cSample _ _ i

theorem mB_wSample (ζA ζB : Blocks n) : (wSample ζA ζB).mB = mvec ζB :=
  funext fun j => mB_cSample _ _ j

noncomputable def qWinAt (hθA : 0 < θA) (hθB : 0 < θB) (ζA ζB : Blocks n) (x y ρ : ℝ) : ℝ :=
  Rational.qAt hθA hθB (piWin ζA x) (piWin ζB y) ρ (wSample ζA ζB)

theorem qWinAt_eq_qWin (hθA : 0 < θA) (hθB : 0 < θB) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ζA ζB : Blocks n) (x y : ℝ) :
    qWinAt hθA hθB ζA ζB x y ρ = qWin hθA hθB hρ ζA ζB x y := by
  rw [qWinAt, qWin, Rational.qAt_eq_q hθA hθB hρ]

theorem tendsto_qWinAt (hθA : 0 < θA) (hθB : 0 < θB)
    (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA)
    (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB) {x y : ℝ}
    (hx : 0 ≤ x) (hxm : (ζA.card : ℝ) * x ≤ 1)
    (hy : 0 ≤ y) (hym : (ζB.card : ℝ) * y ≤ 1) :
    Tendsto (fun ρ : ℝ => qWinAt hθA hθB ζA ζB x y ρ) atTop
      (𝓝 (qOne θA (piWin ζA x) (mvec ζA) * qOne θB (piWin ζB y) (mvec ζB))) := by
  have h := Rational.tendsto_q_qHat hθA hθB (piWin_nonneg hx hxm) (piWin_sum_one hA)
    (piWin_nonneg hy hym) (piWin_sum_one hB) (wSample ζA ζB)
  rwa [mA_wSample, mB_wSample] at h

theorem tendsto_esfKernel_prod (hθA : 0 < θA) (hθB : 0 < θB) (ζA ζB : Blocks n) :
    Tendsto (fun ρ : ℝ => esfKernel θA θB ρ ζA ζB) atTop
      (𝓝 (esfPart n θA ζA * esfPart n θB ζB)) := by
  by_cases hpart : IsPartOf (Finset.univ : Finset (Fin n)) ζA ∧
      IsPartOf (Finset.univ : Finset (Fin n)) ζB
  · obtain ⟨hA, hB⟩ := hpart
    set FA : Fin (n + 1) → ℝ := fun k =>
      qOne θA (piWin ζA (Probability.InfiniteAllelesLimit.xnode ζA.card n k)) (mvec ζA) with hFA
    set FB : Fin (n + 1) → ℝ := fun l =>
      qOne θB (piWin ζB (Probability.InfiniteAllelesLimit.xnode ζB.card n l)) (mvec ζB) with hFB
    have hlim : Tendsto (fun ρ : ℝ => ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        wgtA ζA k * wgtA ζB l * qWinAt hθA hθB ζA ζB
          (Probability.InfiniteAllelesLimit.xnode ζA.card n k)
              (Probability.InfiniteAllelesLimit.xnode ζB.card n l) ρ) atTop
        (𝓝 (∑ k : Fin (n + 1), ∑ l : Fin (n + 1), wgtA ζA k * wgtA ζB l * (FA k * FB l))) := by
      refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
      exact (tendsto_qWinAt hθA hθB hA hB Probability.InfiniteAllelesLimit.xnode_nonneg
          Probability.InfiniteAllelesLimit.mul_xnode_le_one
          Probability.InfiniteAllelesLimit.xnode_nonneg
        Probability.InfiniteAllelesLimit.mul_xnode_le_one).const_mul _
    have hcongr : (fun ρ : ℝ => ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        wgtA ζA k * wgtA ζB l * qWinAt hθA hθB ζA ζB
          (Probability.InfiniteAllelesLimit.xnode ζA.card n k)
              (Probability.InfiniteAllelesLimit.xnode ζB.card n l) ρ)
        =ᶠ[atTop] fun ρ : ℝ => esfKernel θA θB ρ ζA ζB := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with ρ hρ
      rw [esfKernel_eq_sum_q hθA hθB hρ hA hB]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
        rw [qWinAt_eq_qWin hθA hθB hρ]
    have hval : (∑ k : Fin (n + 1), ∑ l : Fin (n + 1), wgtA ζA k * wgtA ζB l * (FA k * FB l))
        = esfPart n θA ζA * esfPart n θB ζB := by
      have hfac : (∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
          wgtA ζA k * wgtA ζB l * (FA k * FB l))
          = (∑ k : Fin (n + 1), wgtA ζA k * FA k) * ∑ l : Fin (n + 1), wgtA ζB l * FB l := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      rw [hfac, hFA, hFB, coeff_qOne_piWin hA, coeff_qOne_piWin hB]
    rw [← hval]
    exact hlim.congr' hcongr
  · have hz : ∀ ρ : ℝ, esfKernel θA θB ρ ζA ζB = 0 :=
      fun ρ => esfKernel_eq_zero_of_not_part hpart
    have hz2 : esfPart n θA ζA * esfPart n θB ζB = 0 := by
      rcases not_and_or.1 hpart with h | h
      · rw [esfPart_eq_zero h θA, zero_mul]
      · rw [esfPart_eq_zero h θB, mul_zero]
    rw [hz2]
    simpa only [hz] using tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℝ))

theorem tendsto_covKernel_zero (hθA : 0 < θA) (hθB : 0 < θB) (ζA ζB : Blocks n) :
    Tendsto (fun ρ : ℝ => covKernel n θA θB ρ ζA ζB) atTop (𝓝 0) := by
  have h := (tendsto_esfKernel_prod hθA hθB ζA ζB).sub
    (tendsto_const_nhds (x := esfPart n θA ζA * esfPart n θB ζB) (f := (atTop : Filter ℝ)))
  rw [sub_self] at h
  exact h.congr fun ρ => rfl

end Rhone.Coalescent.InfiniteAllelesLimit
