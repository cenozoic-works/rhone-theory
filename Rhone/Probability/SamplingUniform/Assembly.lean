/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.SolutionEvaluation
public import Rhone.Probability.SamplingUniform.Generic
public import Rhone.Probability.SamplingUniform.Rare
public import Rhone.Probability.RareAlleleHierarchy.Vertex
public import Rhone.Probability.Denominator.SharpnessTransfer

/-! # Sampling assembly and its first mixed frequency coefficient -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Finset MvPolynomial LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear
open LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy RareAlleleHierarchy

def piOf {R : Type*} [CommRing R] (p : R) : Fin 2 → R := ![p, 1 - p]

@[simp] theorem piOf_zero {R : Type*} [CommRing R] (p : R) : piOf p 0 = p := rfl

theorem piOf_sum {R : Type*} [CommRing R] (p : R) : piOf p 0 + piOf p 1 = 1 := by
  simp [piOf]

def samplingMM (m : ℕ) : Config 2 2 := ⟨![m, 0], ![m, 0], 0⟩

theorem xi_empty_samplingMM (m : ℕ) :
    xi (∅ : Finset (Fin m × Fin m)) (fun _ => (0 : Fin 2))
      (fun _ => (0 : Fin 2)) = samplingMM m := by
  apply Config.ext
  · funext i
    fin_cases i <;> simp [xi, freeA, domA, samplingMM]
  · funext j
    fin_cases j <;> simp [xi, freeB, domB, samplingMM]
  · funext i j
    simp [xi, samplingMM]

section Actual

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ p r : F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ (piOf p) (piOf r) q)

include ha hb hr hq

theorem q_samplingMM_expansion (m : ℕ) :
    q (samplingMM m) = ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
      p ^ (m - S.card) * r ^ (m - T.card) * Phi q (piOf p) (piOf r) S.card T.card 0 := by
  have h := q_xi_eq_sum_Phi ha hb hr hq (piOf_sum p) (piOf_sum r)
    (∅ : Finset (Fin m × Fin m)) ⟨by simp, by simp⟩
    (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))
  simpa only [xi_empty_samplingMM, piOf_zero, eps_zero, prod_const, one_pow, mul_one,
    card_compl, Fintype.card_fin, pairsIn, filter_empty, card_empty] using h

end Actual

section Coefficient

variable {K : Type*} [CommRing K]

noncomputable def assembledSample (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) (m : ℕ) :
    MvPolynomial (Fin 2) K :=
  ∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
    X 0 ^ (m - S.card) * X 1 ^ (m - T.card) * Φ S.card T.card 0

private theorem cf11_X0_pow_mul_zero (d : ℕ) (f : MvPolynomial (Fin 2) K)
    (hd : 1 ≤ d) (hv : d = 1 → Van 0 f) : cf 1 1 (X 0 ^ d * f) = 0 := by
  rcases d with _ | d
  · omega
  rcases d with _ | d
  · simp only [Nat.zero_add, pow_one]
    rw [cf_X0_mul 0 1]
    exact hv rfl (mon 0 1) (by simp)
  · have heq : X 0 ^ (d + 1 + 1) * f = X 0 * (X 0 * (X 0 ^ d * f)) := by ring
    rw [heq, cf_X0_mul 0 1, cf_X0_mul_zero]

private theorem cf11_X1_pow_mul_zero (d : ℕ) (f : MvPolynomial (Fin 2) K)
    (hd : 1 ≤ d) (hv : d = 1 → Van 1 f) : cf 1 1 (X 1 ^ d * f) = 0 := by
  rcases d with _ | d
  · omega
  rcases d with _ | d
  · simp only [Nat.zero_add, pow_one]
    rw [cf_X1_mul 1 0]
    exact hv rfl (mon 1 0) (by simp)
  · have heq : X 1 ^ (d + 1 + 1) * f = X 1 * (X 1 * (X 1 ^ d * f)) := by ring
    rw [heq, cf_X1_mul 1 0, cf_X1_mul_zero]

private theorem card_lt_of_ne_univ {m : ℕ} (S : Finset (Fin m)) (hS : S ≠ univ) :
    S.card < m :=
  lt_of_lt_of_eq ((Finset.card_lt_iff_ne_univ S).2 hS) (Fintype.card_fin m)

theorem assembledSample_first_mixed (Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K)
    (hA : ∀ i j t, 1 ≤ i → Van 0 (Φ i j t))
    (hB : ∀ i j t, 1 ≤ j → Van 1 (Φ i j t)) {m : ℕ} (hm : 2 ≤ m) :
    cf 1 1 (assembledSample Φ m) = cf 1 1 (Φ m m 0) := by
  have hterm (S T : Finset (Fin m)) :
      cf 1 1 (X 0 ^ (m - S.card) * X 1 ^ (m - T.card) * Φ S.card T.card 0) =
        if S = univ ∧ T = univ then cf 1 1 (Φ m m 0) else 0 := by
    by_cases hs : S = univ
    · subst S
      simp only [card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, one_mul, true_and]
      by_cases ht : T = univ
      · simp [ht]
      · rw [ite_eq_right ht]
        have hlt := card_lt_of_ne_univ T ht
        apply cf11_X1_pow_mul_zero _ _ (by omega)
        intro hd
        exact hB m T.card 0 (by omega)
    · rw [ite_eq_right (fun h => hs h.1), mul_assoc]
      have hlt := card_lt_of_ne_univ S hs
      apply cf11_X0_pow_mul_zero _ _ (by omega)
      intro hd
      exact (hA S.card T.card 0 (by omega)).mul_left _
  simp only [assembledSample, cf, coeff_sum]
  change (∑ S : Finset (Fin m), ∑ T : Finset (Fin m),
    cf 1 1 (X 0 ^ (m - S.card) * X 1 ^ (m - T.card) * Φ S.card T.card 0)) = _
  simp_rw [hterm]
  simp [ite_and, cf]

end Coefficient

section Generic

variable {K : Type*} [Field K]

noncomputable def genericSample (a b ρ : K) (m : ℕ) : MvPolynomial (Fin 2) K :=
  assembledSample (genericPhi a b ρ) m

theorem genericSample_first_mixed [CharZero K] (a b ρ : K)
    (hD : ∀ i j, Dfull a b ρ i j ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    cf 1 1 (genericSample a b ρ m) = cf 1 1 (genericPhi a b ρ m m 0) := by
  exact assembledSample_first_mixed (genericPhi a b ρ)
    (genericPhi_vanA a b ρ hD) (genericPhi_vanB a b ρ hD) hm

end Generic

section Evaluation

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ p r : F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ (piOf p) (piOf r) q)

include ha hb hr hq

theorem eval_genericPhi_eq_Phi (i j t : ℕ) :
    MvPolynomial.eval ![p, r] (genericPhi a b ρ i j t) =
      Phi q (piOf p) (piOf r) i j t := by
  have hc := map_clearedPhi_eq_Dfull_mul_Phi ha hb hr hq (piOf_sum p) (piOf_sum r)
    (MvPolynomial.eval ![p, r]) (C a) (C b) (C ρ) kapX gamX kapY gamY
    (by simp) (by simp) (by simp)
    (by simp [kapX, kap, piOf]; ring) (by simp [gamX, gam, piOf]; ring)
    (by simp [kapY, kap, piOf]; ring) (by simp [gamY, gam, piOf]; ring) i j t
  rw [genericPhi, map_mul, eval_C, hc, ← mul_assoc,
    inv_mul_cancel₀ (Denominator.Dfull_pos ha hb hr i j).ne', one_mul]

theorem eval_genericSample_eq_q_samplingMM (m : ℕ) :
    MvPolynomial.eval ![p, r] (genericSample a b ρ m) = q (samplingMM m) := by
  rw [q_samplingMM_expansion ha hb hr hq m]
  simp [genericSample, assembledSample, eval_genericPhi_eq_Phi ha hb hr hq]

end Evaluation

end Rhone.Probability.SamplingUniform
