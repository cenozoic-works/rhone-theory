/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.TwoLocusGenerator
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Order.Compact

/-!
# The positive maximum principle for diffusion operators on the simplex

Source: ethier_kurtz1986, ch. 4, sec. 2. -/

@[expose] public section

namespace Rhone.Diffusion

open MvPolynomial Finset

theorem polynomial_eval_eq_add_mul_divX (P : Polynomial ℝ) (t : ℝ) :
    P.eval t = P.eval 0 + t * (Polynomial.divX P).eval t := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.coeff_zero_eq_eval_zero]
  ring

theorem polynomial_derivative_eval_zero (P : Polynomial ℝ) :
    (Polynomial.derivative P).eval 0 = (Polynomial.divX P).eval 0 := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  simp [Polynomial.derivative_mul]

theorem polynomial_derivative_derivative_eval_zero (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 =
      2 * (Polynomial.divX (Polynomial.divX P)).eval 0 := by
  have h1 : Polynomial.derivative P =
      Polynomial.derivative (Polynomial.divX P) * Polynomial.X + Polynomial.divX P := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add P]
    simp [Polynomial.derivative_mul]
  rw [h1]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, mul_zero,
    mul_one, zero_add]
  rw [polynomial_derivative_eval_zero (Polynomial.divX P)]
  ring

theorem polynomial_exists_pos_near (R : Polynomial ℝ) (h : 0 < R.eval 0) :
    ∃ δ > 0, ∀ t, |t| < δ → 0 < R.eval t := by
  have hev : ∀ᶠ t in nhds (0 : ℝ), 0 < R.eval t :=
    R.continuous.continuousAt.eventually (lt_mem_nhds h)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨δ, hδ, fun t ht => hball (by simpa [Real.dist_eq] using ht)⟩

theorem polynomial_derivative_eval_zero_nonpos {P : Polynomial ℝ} {ε : ℝ} (hε : 0 < ε)
    (hmax : ∀ t ∈ Set.Icc 0 ε, P.eval t ≤ P.eval 0) : (Polynomial.derivative P).eval 0 ≤ 0 := by
  rw [polynomial_derivative_eval_zero]
  by_contra hpos
  push Not at hpos
  obtain ⟨δ, hδ, hR⟩ := polynomial_exists_pos_near _ hpos
  have ht0 : 0 < min (δ / 2) ε := lt_min (by linarith) hε
  have htδ : |min (δ / 2) ε| < δ := by
    rw [abs_of_pos ht0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have h1 := hmax (min (δ / 2) ε) ⟨ht0.le, min_le_right _ _⟩
  rw [polynomial_eval_eq_add_mul_divX P (min (δ / 2) ε)] at h1
  have := mul_pos ht0 (hR _ htδ)
  linarith

theorem polynomial_derivative_eval_zero_eq_zero {P : Polynomial ℝ} {ε : ℝ} (hε : 0 < ε)
    (hmax : ∀ t ∈ Set.Icc (-ε) ε, P.eval t ≤ P.eval 0) : (Polynomial.derivative P).eval 0 = 0 := by
  refine le_antisymm (polynomial_derivative_eval_zero_nonpos hε fun t ht =>
    hmax t ⟨by linarith [ht.1], ht.2⟩) ?_
  rw [polynomial_derivative_eval_zero]
  by_contra hneg
  push Not at hneg
  obtain ⟨δ, hδ, hR⟩ := polynomial_exists_pos_near (-(Polynomial.divX P))
    (by rw [Polynomial.eval_neg]; linarith)
  have ht0 : 0 < min (δ / 2) ε := lt_min (by linarith) hε
  have htδ : |-min (δ / 2) ε| < δ := by
    rw [abs_neg, abs_of_pos ht0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have h1 := hmax (-min (δ / 2) ε) ⟨by linarith [min_le_right (δ / 2) ε], by linarith⟩
  rw [polynomial_eval_eq_add_mul_divX P (-min (δ / 2) ε)] at h1
  have h2 := hR _ htδ
  rw [Polynomial.eval_neg] at h2
  have := mul_pos ht0 h2
  linarith

theorem polynomial_derivative_derivative_eval_zero_nonpos {P : Polynomial ℝ} {ε : ℝ}
    (hε : 0 < ε) (hmax : ∀ t ∈ Set.Icc (-ε) ε, P.eval t ≤ P.eval 0) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 ≤ 0 := by
  have h0 := polynomial_derivative_eval_zero_eq_zero hε hmax
  rw [polynomial_derivative_eval_zero] at h0
  rw [polynomial_derivative_derivative_eval_zero]
  by_contra hpos
  push Not at hpos
  have hpos' : 0 < (Polynomial.divX (Polynomial.divX P)).eval 0 := by linarith
  obtain ⟨δ, hδ, hR⟩ := polynomial_exists_pos_near _ hpos'
  have ht0 : 0 < min (δ / 2) ε := lt_min (by linarith) hε
  have htδ : |min (δ / 2) ε| < δ := by
    rw [abs_of_pos ht0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have h1 := hmax (min (δ / 2) ε) ⟨by linarith [min_le_right (δ / 2) ε], min_le_right _ _⟩
  have e1 := polynomial_eval_eq_add_mul_divX P (min (δ / 2) ε)
  have e2 := polynomial_eval_eq_add_mul_divX (Polynomial.divX P) (min (δ / 2) ε)
  rw [h0, zero_add] at e2
  have := mul_pos (mul_pos ht0 ht0) (hR _ htδ)
  rw [e2] at e1
  nlinarith

variable {G : Type*}

noncomputable def linePoly (x v : G → ℝ) (f : MvPolynomial G ℝ) : Polynomial ℝ :=
  aeval (fun h => Polynomial.C (x h) + Polynomial.C (v h) * Polynomial.X) f

theorem linePoly_eval (x v : G → ℝ) (f : MvPolynomial G ℝ) (t : ℝ) :
    (linePoly x v f).eval t = eval (x + t • v) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [linePoly]
  | add p q hp hq =>
    simp only [linePoly, map_add, Polynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p k hp =>
    simp only [linePoly, map_mul, Polynomial.eval_mul, aeval_X, eval_X] at hp ⊢
    rw [hp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem linePoly_eval_zero (x v : G → ℝ) (f : MvPolynomial G ℝ) :
    (linePoly x v f).eval 0 = eval x f := by
  rw [linePoly_eval, zero_smul, add_zero]

variable [Fintype G]

noncomputable def dirDeriv (v : G → ℝ) (f : MvPolynomial G ℝ) : MvPolynomial G ℝ :=
  ∑ h, C (v h) * pderiv h f

theorem dirDeriv_add (v : G → ℝ) (p q : MvPolynomial G ℝ) :
    dirDeriv v (p + q) = dirDeriv v p + dirDeriv v q := by
  simp [dirDeriv, mul_add, sum_add_distrib]

theorem dirDeriv_mul_X (v : G → ℝ) (p : MvPolynomial G ℝ) (k : G) :
    dirDeriv v (p * X k) = dirDeriv v p * X k + C (v k) * p := by
  classical
  simp only [dirDeriv, Derivation.leibniz, pderiv_X, smul_eq_mul, mul_add, sum_add_distrib,
    sum_mul, Pi.single_apply]
  rw [add_comm]
  congr 1
  · exact sum_congr rfl fun h _ => by ring
  · simp

theorem dirDeriv_C (v : G → ℝ) (a : ℝ) : dirDeriv v (C a : MvPolynomial G ℝ) = 0 := by
  simp [dirDeriv]

theorem derivative_linePoly (x v : G → ℝ) (f : MvPolynomial G ℝ) :
    Polynomial.derivative (linePoly x v f) = linePoly x v (dirDeriv v f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [linePoly, dirDeriv_C]
  | add p q hp hq =>
    rw [dirDeriv_add]
    simp only [linePoly, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p k hp =>
    rw [dirDeriv_mul_X]
    simp only [linePoly, map_mul, map_add, aeval_X, aeval_C, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X] at hp ⊢
    rw [hp]
    simp only [Polynomial.algebraMap_eq]
    ring

theorem derivative_linePoly_eval_zero (x v : G → ℝ) (f : MvPolynomial G ℝ) :
    (Polynomial.derivative (linePoly x v f)).eval 0 = eval x (dirDeriv v f) := by
  rw [derivative_linePoly, linePoly_eval_zero]

theorem derivative_derivative_linePoly_eval_zero (x v : G → ℝ) (f : MvPolynomial G ℝ) :
    (Polynomial.derivative (Polynomial.derivative (linePoly x v f))).eval 0 =
      eval x (dirDeriv v (dirDeriv v f)) := by
  rw [derivative_linePoly, derivative_linePoly, linePoly_eval_zero]

variable [DecidableEq G]

noncomputable def simplexDiffusionOp (b : G → MvPolynomial G ℝ) (f : MvPolynomial G ℝ) :
    MvPolynomial G ℝ :=
  (∑ g, ∑ h, X g * (C (if g = h then 1 else 0) - X h) * pderiv g (pderiv h f)) +
    ∑ g, b g * pderiv g f

theorem mem_simplex_add_smul {x : G → ℝ} (hx0 : ∀ g, 0 ≤ x g) (hx1 : ∑ g, x g = 1) (g : G)
    {t : ℝ} (ht0 : -x g ≤ t) (ht1 : t ≤ 1) :
    (∀ h, 0 ≤ (x + t • (Pi.single g 1 - x) : G → ℝ) h) ∧
      ∑ h, (x + t • (Pi.single g 1 - x) : G → ℝ) h = 1 := by
  have hxg1 : x g ≤ 1 := hx1 ▸ single_le_sum (fun h _ => hx0 h) (mem_univ g)
  refine ⟨fun h => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
    by_cases hh : h = g
    · subst hh
      simp only [ite_true]
      have := hx0 h
      nlinarith
    · simp only [hh, ite_false]
      have := hx0 h
      nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sum_add_distrib,
      ← mul_sum, sum_sub_distrib, hx1]
    simp

theorem eval_secondOrder_eq_sum {x : G → ℝ} (hx1 : ∑ g, x g = 1) (f : MvPolynomial G ℝ) :
    eval x (∑ g, ∑ h, X g * (C (if g = h then 1 else 0) - X h) * pderiv g (pderiv h f)) =
      ∑ g, x g * eval x (dirDeriv (Pi.single g 1 - x) (dirDeriv (Pi.single g 1 - x) f)) := by
  set E : G → G → ℝ := fun h k => eval x (pderiv h (pderiv k f)) with hE
  have hS : ∀ v : G → ℝ, eval x (dirDeriv v (dirDeriv v f)) = ∑ h, v h * ∑ k, v k * E h k := by
    intro v
    simp only [dirDeriv, map_sum, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero,
      map_mul, eval_C, hE, mul_sum]
  have hlin : ∀ (g : G) (F : G → ℝ), ∑ k, (Pi.single g 1 - x : G → ℝ) k * F k =
      F g - ∑ k, x k * F k := by
    intro g F
    simp [sub_mul, Pi.single_apply]
  set D : ℝ := ∑ h, x h * ∑ k, x k * E h k with hD
  have hQ : ∀ g, eval x (dirDeriv (Pi.single g 1 - x) (dirDeriv (Pi.single g 1 - x) f)) =
      E g g - ∑ k, x k * E g k - ∑ h, x h * E h g + D := by
    intro g
    rw [hS]
    simp only [hlin]
    rw [hD]
    simp only [mul_sub, sum_sub_distrib]
    ring
  have hL : eval x (∑ g, ∑ h, X g * (C (if g = h then 1 else 0) - X h) * pderiv g (pderiv h f)) =
      ∑ g, x g * E g g - D := by
    simp only [map_sum, map_mul, map_sub, eval_X, eval_C]
    rw [hD, ← sum_sub_distrib]
    refine sum_congr rfl fun g _ => ?_
    simp [mul_sub, sub_mul, mul_sum, mul_assoc, hE]
  have hB : ∑ g, x g * ∑ h, x h * E h g = D := by
    rw [hD]
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun h _ => sum_congr rfl fun g _ => by ring
  have hR : ∑ g, x g * (E g g - ∑ k, x k * E g k - ∑ h, x h * E h g + D) =
      ∑ g, x g * E g g - D := by
    have e : ∀ g, x g * (E g g - ∑ k, x k * E g k - ∑ h, x h * E h g + D) =
        x g * E g g - x g * ∑ k, x k * E g k - x g * ∑ h, x h * E h g + x g * D :=
      fun g => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← sum_mul, hx1, one_mul, hB]
    rw [hD]
    ring
  rw [hL]
  simp only [hQ]
  rw [hR]

theorem eval_firstOrder_eq_sum {x : G → ℝ} (b : G → MvPolynomial G ℝ)
    (hb0 : ∑ g, eval x (b g) = 0) (f : MvPolynomial G ℝ) :
    eval x (∑ g, b g * pderiv g f) =
      ∑ g, eval x (b g) * eval x (dirDeriv (Pi.single g 1 - x) f) := by
  have hD : ∀ g, eval x (dirDeriv (Pi.single g 1 - x) f) =
      eval x (pderiv g f) - ∑ h, x h * eval x (pderiv h f) := by
    intro g
    simp [dirDeriv, sub_mul, Pi.single_apply]
  simp only [map_sum, map_mul, hD, mul_sub, sum_sub_distrib, ← sum_mul, hb0, zero_mul, sub_zero]

theorem eval_simplexDiffusionOp_nonpos_of_isMax {b : G → MvPolynomial G ℝ}
    {f : MvPolynomial G ℝ} {x : G → ℝ} (hx0 : ∀ g, 0 ≤ x g) (hx1 : ∑ g, x g = 1)
    (hmax : ∀ y : G → ℝ, (∀ g, 0 ≤ y g) → ∑ g, y g = 1 → eval y f ≤ eval x f)
    (hb0 : ∑ g, eval x (b g) = 0) (hbpos : ∀ g, x g = 0 → 0 ≤ eval x (b g)) :
    eval x (simplexDiffusionOp b f) ≤ 0 := by
  have hline : ∀ g t, -x g ≤ t → t ≤ 1 →
      (linePoly x (Pi.single g 1 - x) f).eval t ≤ (linePoly x (Pi.single g 1 - x) f).eval 0 := by
    intro g t ht0 ht1
    rw [linePoly_eval, linePoly_eval_zero]
    obtain ⟨h0, h1⟩ := mem_simplex_add_smul hx0 hx1 g ht0 ht1
    exact hmax _ h0 h1
  have hxg1 : ∀ g, x g ≤ 1 := fun g => hx1 ▸ single_le_sum (fun h _ => hx0 h) (mem_univ g)
  have h1 : ∀ g, eval x (dirDeriv (Pi.single g 1 - x) f) ≤ 0 := by
    intro g
    rw [← derivative_linePoly_eval_zero]
    exact polynomial_derivative_eval_zero_nonpos one_pos fun t ht =>
      hline g t (by linarith [hx0 g, ht.1]) ht.2
  have h2 : ∀ g, 0 < x g → eval x (dirDeriv (Pi.single g 1 - x) f) = 0 := by
    intro g hg
    rw [← derivative_linePoly_eval_zero]
    exact polynomial_derivative_eval_zero_eq_zero hg fun t ht =>
      hline g t ht.1 (ht.2.trans (hxg1 g))
  have h3 : ∀ g, 0 < x g →
      eval x (dirDeriv (Pi.single g 1 - x) (dirDeriv (Pi.single g 1 - x) f)) ≤ 0 := by
    intro g hg
    rw [← derivative_derivative_linePoly_eval_zero]
    exact polynomial_derivative_derivative_eval_zero_nonpos hg fun t ht =>
      hline g t ht.1 (ht.2.trans (hxg1 g))
  rw [simplexDiffusionOp, map_add, eval_secondOrder_eq_sum hx1, eval_firstOrder_eq_sum b hb0]
  refine add_nonpos (sum_nonpos fun g _ => ?_) (sum_nonpos fun g _ => ?_)
  · rcases (hx0 g).eq_or_lt with hg | hg
    · rw [← hg, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos hg.le (h3 g hg)
  · rcases (hx0 g).eq_or_lt with hg | hg
    · exact mul_nonpos_of_nonneg_of_nonpos (hbpos g hg.symm) (h1 g)
    · rw [h2 g hg, mul_zero]

theorem simplexDiffusionOp_neg (b : G → MvPolynomial G ℝ) (f : MvPolynomial G ℝ) :
    simplexDiffusionOp b (-f) = -simplexDiffusionOp b f := by
  simp only [simplexDiffusionOp, map_neg, mul_neg, sum_neg_distrib]
  abel

variable {KA KB : ℕ}

theorem selDrift_eq_sum (i₀ : Fin KA) (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    selDrift i₀ f =
      ∑ g, X g * (C (if g.1 = i₀ then 1 else 0) - margA i₀) * pderiv g f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [← algebraMap_eq, Derivation.map_algebraMap]
    simp
  | add p q hp hq => simp [map_add, hp, hq, mul_add, sum_add_distrib]
  | mul_X p k hp =>
    rcases k with ⟨i, j⟩
    rw [Derivation.leibniz, selDrift_X, hp]
    simp only [smul_eq_mul, Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add,
      sum_add_distrib, mul_sum]
    congr 1
    · simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
      ring
    · exact sum_congr rfl fun g _ => by ring

noncomputable def twoLocusDrift (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (i₀ : Fin KA) (σ : ℝ) (g : Fin KA × Fin KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  neutralDrift θA θB ρ πA πB g + C σ * (X g * (C (if g.1 = i₀ then 1 else 0) - margA i₀))

theorem twoLocusGenerator_eq_simplexDiffusionOp (θA θB ρ : ℝ) (πA : Fin KA → ℝ)
    (πB : Fin KB → ℝ) (i₀ : Fin KA) (σ : ℝ) (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    twoLocusGenerator θA θB ρ πA πB i₀ σ f =
      simplexDiffusionOp (twoLocusDrift θA θB ρ πA πB i₀ σ) f := by
  rw [twoLocusGenerator, neutralGenerator, simplexDiffusionOp, selDrift_eq_sum, mul_sum,
    add_assoc]
  congr 1
  rw [← sum_add_distrib]
  exact sum_congr rfl fun g _ => by rw [twoLocusDrift]; ring

theorem sum_eval_twoLocusDrift (θA θB ρ : ℝ) {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ)
    {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) :
    ∑ g, eval x (twoLocusDrift θA θB ρ πA πB i₀ σ g) = 0 := by
  have hrow := sum_eval_neutralDrift_row θA θB ρ πA hπB hx
  have hP := sum_eval_margA (KB := KB) hx
  have hsel : ∑ g : Fin KA × Fin KB, x g * ((if g.1 = i₀ then (1 : ℝ) else 0) -
      eval x (margA i₀)) = 0 := by
    have hPi : eval x (margA (KB := KB) i₀) = ∑ j, x (i₀, j) := by simp [margA]
    have h1 : ∑ g : Fin KA × Fin KB, x g * (if g.1 = i₀ then (1 : ℝ) else 0) =
        ∑ j, x (i₀, j) := by
      rw [Fintype.sum_prod_type, sum_comm]
      simp
    rw [sum_congr rfl fun g _ => mul_sub (x g) _ _, sum_sub_distrib, h1, ← sum_mul, hx, one_mul,
      hPi, sub_self]
  simp only [twoLocusDrift, map_add, map_mul, map_sub, eval_C, eval_X, sum_add_distrib,
    ← mul_sum, hsel, mul_zero, add_zero]
  rw [Fintype.sum_prod_type]
  simp only [hrow, ← mul_sum, sum_sub_distrib, hπA, hP, sub_self, mul_zero]

theorem eval_twoLocusDrift_nonneg {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j)
    (i₀ : Fin KA) (σ : ℝ) {x : Fin KA × Fin KB → ℝ} (hx0 : ∀ g, 0 ≤ x g) (g : Fin KA × Fin KB)
    (hg : x g = 0) : 0 ≤ eval x (twoLocusDrift θA θB ρ πA πB i₀ σ g) := by
  rcases g with ⟨i, j⟩
  have hP : 0 ≤ eval x (margA (KB := KB) i) := by
    simp only [margA, map_sum, eval_X]
    exact sum_nonneg fun _ _ => hx0 _
  have hR : 0 ≤ eval x (margB (KA := KA) j) := by
    simp only [margB, map_sum, eval_X]
    exact sum_nonneg fun _ _ => hx0 _
  simp only [twoLocusDrift, map_add, map_mul, eval_neutralDrift, eval_C, eval_X, hg]
  simp only [sub_zero, zero_mul, mul_zero, add_zero]
  have := hπA0 i
  have := hπB0 j
  positivity

theorem isCompact_gameteSimplex : IsCompact (gameteSimplex KA KB) := by
  have hsub : gameteSimplex KA KB ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨fun g => hx.1 g, fun g => ?_⟩
    have h := single_le_sum (fun h _ => hx.1 h) (mem_univ g)
    rw [hx.2] at h
    exact h
  have hclosed : IsClosed (gameteSimplex KA KB) := by
    have : gameteSimplex KA KB = (⋂ g, {x : Fin KA × Fin KB → ℝ | 0 ≤ x g}) ∩
        {x | ∑ g, x g = 1} := by
      ext x
      simp [gameteSimplex]
    rw [this]
    exact (isClosed_iInter fun g => isClosed_le continuous_const (continuous_apply g)).inter
      (isClosed_eq (continuous_finsetSum _ fun g _ => continuous_apply g) continuous_const)
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

theorem prod_mem_gameteSimplex {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i)
    (hπB0 : ∀ j, 0 ≤ πB j) (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) :
    (fun g : Fin KA × Fin KB => πA g.1 * πB g.2) ∈ gameteSimplex KA KB := by
  refine ⟨fun g => mul_nonneg (hπA0 _) (hπB0 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, hπB, mul_one, hπA]

theorem exists_nonneg_eval_twoLocusGenerator {θA θB ρ : ℝ} (hθA : 0 ≤ θA) (hθB : 0 ≤ θB)
    (hρ : 0 ≤ ρ) {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (hπA0 : ∀ i, 0 ≤ πA i)
    (hπB0 : ∀ j, 0 ≤ πB j) (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ)
    (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    ∃ x ∈ gameteSimplex KA KB, 0 ≤ eval x (twoLocusGenerator θA θB ρ πA πB i₀ σ f) := by
  obtain ⟨x, hx, hxmax⟩ := isCompact_gameteSimplex.exists_isMaxOn
    ⟨_, prod_mem_gameteSimplex hπA0 hπB0 hπA hπB⟩
    (MvPolynomial.continuous_eval (-f)).continuousOn
  refine ⟨x, hx, ?_⟩
  have h := eval_simplexDiffusionOp_nonpos_of_isMax (b := twoLocusDrift θA θB ρ πA πB i₀ σ)
    (f := -f) hx.1 hx.2 (fun y hy0 hy1 => hxmax ⟨hy0, hy1⟩)
    (sum_eval_twoLocusDrift θA θB ρ hπA hπB i₀ σ hx.2)
    (eval_twoLocusDrift_nonneg hθA hθB hρ hπA0 hπB0 i₀ σ hx.1)
  rw [simplexDiffusionOp_neg, map_neg, ← twoLocusGenerator_eq_simplexDiffusionOp] at h
  linarith

end Rhone.Diffusion
