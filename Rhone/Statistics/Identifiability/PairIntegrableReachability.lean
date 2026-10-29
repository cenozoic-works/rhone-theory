/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairIntegrableFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkedPayoff
public import Rhone.Statistics.Identifiability.IntegrablePositiveWeight

/-! # Positive probability of reaching the apart state under positive migration exposure -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.PairIntegrable

def edgeMark (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 2 * (k + 1 : ℝ)], ![0,0]]

def blockedGenerator (k : ℕ) (c q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-c - 2 * MarkovChain.Identifiability.totalMigration k q, 0], ![2*q, -2*q]]

private lemma blocked_eq_sub (k : ℕ) (c q : ℝ) :
    blockedGenerator k c q = MarkovChain.Identifiability.pairGenerator k c q - q • edgeMark k := by
  ext i j
  change blockedGenerator k c q i j = MarkovChain.Identifiability.pairGenerator k c q i j - q *
      edgeMark k i j
  fin_cases i <;> fin_cases j <;>
    simp [blockedGenerator, MarkovChain.Identifiability.pairGenerator, edgeMark,
        MarkovChain.Identifiability.totalMigration]
  ring

private lemma blocked_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (i j : Fin 2) :
    LocallyIntegrable (fun u => blockedGenerator k (c u) (q u) i j) volume := by
  have he : (fun u => blockedGenerator k (c u) (q u) i j) =
      fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u) i j - q u * edgeMark k i j :=
          by
    funext u
    rw [blocked_eq_sub]
    rfl
  rw [he]
  exact (generator_locallyIntegrable k c q hc hq i j).sub (hq.mul_continuous continuous_const)

private lemma blocked_metzler_ae (k : ℕ) (c q : ℝ → ℝ)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) :
    ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ blockedGenerator k (c u) (q u) i j := by
  filter_upwards [hqn] with u hu hnonneg i j hij
  have hp := hu hnonneg
  fin_cases i <;> fin_cases j <;> simp_all [blockedGenerator]

theorem apart_positive_of_migration_exposure (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {t : ℝ} (ht : 0 ≤ t)
    (hQ : 0 < ∫ u in (0 : ℝ)..t, q u) :
    0 < timeVaryingPairTransition k c q 0 t 0 1 := by
  let A := fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u)
  let B := fun u => blockedGenerator k (c u) (q u)
  let w : Fin 2 → ℝ := Pi.single 1 1
  have hA := generator_locallyIntegrable k c q hc hq
  have hB := blocked_locallyIntegrable k c q hc hq
  have hmark (u : ℝ) : A u - B u = q u • edgeMark k := by
    dsimp [A, B]
    rw [blocked_eq_sub, sub_sub_cancel]
  have hzero : (inhomogeneousTransition B 0 t *ᵥ w) 0 = 0 := by
    apply integrableTransition_mulVec_zero_of_closed B hB (fun i : Fin 2 => i = 0) _ w _ 0 t 0 rfl
    · filter_upwards [] with u i j hi hj
      subst i
      fin_cases j <;> simp_all [B, blockedGenerator]
    · intro i hi
      subst i
      simp [w]
  let K := fun u => markedPayoffKernel A B (edgeMark k) w 0 (u,t)
  have hK : Continuous K :=
    (markedPayoffKernel_continuous A B (edgeMark k) hA hB w 0).comp
      (continuous_id.prodMk continuous_const)
  have hKformula (u : ℝ) : K u = inhomogeneousTransition A 0 u 0 0 * (2 * (k + 1 : ℝ)) *
      inhomogeneousTransition B u t 1 1 := by
    change (∑ j : Fin 2, (∑ l : Fin 2, (∑ m : Fin 2,
      inhomogeneousTransition A 0 u 0 m * edgeMark k m l) *
        inhomogeneousTransition B u t l j) * w j) = _
    simp [edgeMark, w, Fin.sum_univ_two]
  have hKpos (u : ℝ) (hu : u ∈ Icc 0 t) : 0 < K u := by
    rw [hKformula]
    exact mul_pos
      (mul_pos (integrableTransition_diagonal_positive A hA
        (generator_metzler_ae k c q hqn) le_rfl hu.1 0) (by positivity))
      (integrableTransition_diagonal_positive B hB (blocked_metzler_ae k c q hqn) hu.1 hu.2 1)
  have hp := continuous_weighted_exposure_positive q K hq hK ht
    (by filter_upwards [hqn] with u hu hmem; exact hu hmem.1) hKpos hQ
  have he := integrable_marked_payoff A B q (edgeMark k) hA hB hmark w 0 t
  rw [hzero, sub_zero] at he
  have hout : (inhomogeneousTransition A 0 t *ᵥ w) 0 =
      timeVaryingPairTransition k c q 0 t 0 1 := by
    simp [w, Matrix.mulVec, dotProduct, Fin.sum_univ_two, A, timeVaryingPairTransition]
  rw [hout] at he
  rw [he]
  exact hp

end Rhone.Statistics.Identifiability.PairIntegrable
