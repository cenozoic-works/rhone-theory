/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteSiteObservationLaw

/-! # Finite equal-rates mutation semigroup and its two-branch observation kernel -/

@[expose] public section

open Set MeasureTheory Matrix
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.Identifiability.EqualRatesMutation

abbrev State (K : ℕ) := Fin K
abbrev MutationMatrix (K : ℕ) := Matrix (State K) (State K) ℝ

def uniform (K : ℕ) : MutationMatrix K := fun _ _ => 1 / (K : ℝ)

def transition (K : ℕ) (k t : ℝ) : MutationMatrix K :=
  Real.exp (-(k/2)*t) • 1 + (1-Real.exp (-(k/2)*t)) • uniform K

def generator (K : ℕ) (k : ℝ) : MutationMatrix K := (k/2) • (uniform K - 1)

lemma uniform_idempotent {K : ℕ} (hK : 0 < K) : uniform K * uniform K = uniform K := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  ext i j
  simp only [Matrix.mul_apply, uniform, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma uniform_transpose (K : ℕ) : (uniform K)ᵀ = uniform K := rfl

lemma transition_transpose (K : ℕ) (k t : ℝ) :
    (transition K k t)ᵀ = transition K k t := by
  simp only [transition, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, uniform_transpose]

lemma transition_symmetric (K : ℕ) (k t : ℝ) (a b : State K) :
    transition K k t a b = transition K k t b a := by
  exact congrFun (congrFun (transition_transpose K k t).symm a) b

theorem transition_zero (K : ℕ) (k : ℝ) : transition K k 0 = 1 := by
  simp [transition]

theorem transition_add {K : ℕ} (hK : 0 < K) (k s t : ℝ) :
    transition K k (s+t) = transition K k s * transition K k t := by
  simp only [transition, mul_add, Real.exp_add, add_mul, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, uniform_idempotent hK, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma generator_mul_transition {K : ℕ} (hK : 0 < K) (k t : ℝ) :
    generator K k * transition K k t =
      (-(k/2) * Real.exp (-(k/2)*t)) • 1 +
      ((k/2) * Real.exp (-(k/2)*t)) • uniform K := by
  simp only [generator, transition, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    sub_mul, one_mul, mul_one, uniform_idempotent hK, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem transition_hasDerivAt {K : ℕ} (hK : 0 < K) (k t : ℝ) :
    HasDerivAt (transition K k) (generator K k * transition K k t) t := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-(k/2)*s))
      (-(k/2) * Real.exp (-(k/2)*t)) t := by
    convert ((hasDerivAt_id t).const_mul (-(k/2))).exp using 1 <;> simp [mul_comm]
  rw [generator_mul_transition hK]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt
    (fun s => Real.exp (-(k/2)*s) * (1 : MutationMatrix K) i j +
      (1-Real.exp (-(k/2)*s)) * uniform K i j)
    ((-(k/2) * Real.exp (-(k/2)*t)) * (1 : MutationMatrix K) i j +
      ((k/2) * Real.exp (-(k/2)*t)) * uniform K i j) t
  convert! (hd.mul_const ((1 : MutationMatrix K) i j)).add
    (((hasDerivAt_const t (1 : ℝ)).sub hd).mul_const (uniform K i j)) using 1
  ring

theorem transition_hasDerivAt_zero {K : ℕ} (hK : 0 < K) (k : ℝ) :
    HasDerivAt (transition K k) (generator K k) 0 := by
  simpa only [transition_zero, mul_one] using transition_hasDerivAt hK k 0

lemma generator_off_diagonal (K : ℕ) (k : ℝ) {a b : State K} (hab : a ≠ b) :
    generator K k a b = k / (2 * (K : ℝ)) := by
  simp only [generator, Matrix.smul_apply, Matrix.sub_apply, uniform,
    Matrix.one_apply, ite_eq_right hab, sub_zero, smul_eq_mul]
  ring

lemma generator_diagonal (K : ℕ) (k : ℝ) (a : State K) :
    generator K k a a = -(k * ((K : ℝ)-1)) / (2 * (K : ℝ)) := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt))
  simp only [generator, Matrix.smul_apply, Matrix.sub_apply, uniform,
    Matrix.one_apply, smul_eq_mul]
  simp only [↓reduceIte]
  field_simp
  ring

theorem transition_row_sum {K : ℕ} (hK : 0 < K) (k t : ℝ) (a : State K) :
    ∑ b, transition K k t a b = 1 := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, uniform, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma transition_column_sum {K : ℕ} (hK : 0 < K) (k t : ℝ) (a : State K) :
    ∑ b, transition K k t b a = 1 := by
  simp_rw [transition_symmetric K k t _ a]
  exact transition_row_sum hK k t a

theorem transition_nonneg (K : ℕ) {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (a b : State K) : 0 ≤ transition K k t a b := by
  have he : Real.exp (-(k/2)*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, uniform]
  split_ifs <;> positivity

theorem transition_stochastic {K : ℕ} (hK : 0 < K) {k t : ℝ}
    (hk : 0 ≤ k) (ht : 0 ≤ t) :
    (∀ a b, 0 ≤ transition K k t a b) ∧ (∀ a, ∑ b, transition K k t a b = 1) :=
  ⟨transition_nonneg K hk ht, transition_row_sum hK k t⟩

lemma uniform_weights_sum {K : ℕ} (hK : 0 < K) :
    ∑ _root : State K, (1 / (K : ℝ)) = 1 := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  simp [hn]

theorem uniform_stationary {K : ℕ} (hK : 0 < K) (k t : ℝ) (a : State K) :
    ∑ root, (1 / (K : ℝ)) * transition K k t root a = 1 / (K : ℝ) := by
  rw [← Finset.mul_sum, transition_column_sum hK, mul_one]

def ancestralPair (K : ℕ) (k t : ℝ) (a b : State K) : ℝ :=
  (1 / (K : ℝ)) * ∑ root, transition K k t root a * transition K k t root b

lemma ancestralPair_eq_double_transition {K : ℕ} (hK : 0 < K)
    (k t : ℝ) (a b : State K) :
    ancestralPair K k t a b = (1 / (K : ℝ)) * transition K k (t+t) a b := by
  rw [transition_add hK, Matrix.mul_apply]
  unfold ancestralPair
  congr 1
  apply Finset.sum_congr rfl
  intro root _
  rw [transition_symmetric K k t root a]

theorem ancestralPair_eq_siteKernel {K : ℕ} (hK : 2 ≤ K)
    (k t : ℝ) (a b : State K) :
    ancestralPair K k t a b =
      FiniteSiteObservation.siteKernel K (FiniteSiteObservation.difference K k t) (a,b) := by
  have hK0 : 0 < K := by omega
  have h0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK0)
  have h1 : (K : ℝ)-1 ≠ 0 := by
    have h : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  rw [ancestralPair_eq_double_transition hK0]
  have he : -(k/2)*(t+t) = -k*t := by ring
  simp only [transition, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    uniform, Matrix.one_apply, he, FiniteSiteObservation.siteKernel,
    FiniteSiteObservation.difference, FiniteSiteObservation.limit]
  split_ifs <;> field_simp <;> ring

theorem independent_sites_eq_conditionalKernel {K : ℕ} (hK : 2 ≤ K)
    (k : ℝ) (t : ℝ × ℝ) (a : FiniteSiteObservation.Observation K) :
    ancestralPair K k t.1 a.1.1 a.1.2 * ancestralPair K k t.2 a.2.1 a.2.2 =
      FiniteSiteObservation.conditionalKernel K k t a := by
  rw [ancestralPair_eq_siteKernel hK, ancestralPair_eq_siteKernel hK]
  rfl

theorem ancestralPair_stochastic {K : ℕ} (hK : 2 ≤ K) {k t : ℝ}
    (hk : 0 ≤ k) (ht : 0 ≤ t) :
    (∀ a b, 0 ≤ ancestralPair K k t a b) ∧
      (∑ a : FiniteSiteObservation.AllelePair K, ancestralPair K k t a.1 a.2 = 1) := by
  constructor
  · intro a b
    rw [ancestralPair_eq_siteKernel hK]
    exact FiniteSiteObservation.siteKernel_nonneg hK
      (FiniteSiteObservation.difference_bounds hK hk ht) (a,b)
  · simp_rw [ancestralPair_eq_siteKernel hK]
    exact FiniteSiteObservation.siteKernel_sum hK _

def observationLaw (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    Measure (FiniteSiteObservation.Observation K) :=
  Measure.sum fun a => ENNReal.ofReal
    (∫ t, ancestralPair K k t.1 a.1.1 a.1.2 * ancestralPair K k t.2 a.2.1 a.2.2 ∂μ) •
      Measure.dirac a

theorem observationLaw_eq {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    observationLaw K k μ = FiniteSiteObservation.law K k μ := by
  simp only [observationLaw, FiniteSiteObservation.law, FiniteSiteObservation.mass]
  simp_rw [independent_sites_eq_conditionalKernel hK]

theorem observationLaw_probability {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k)
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) :
    IsProbabilityMeasure (observationLaw K k μ) := by
  rw [observationLaw_eq hK]
  exact FiniteSiteObservation.law_probability hK hk hμ

theorem observationLaw_eq_of_momentPair_eq {K : ℕ} {k : ℝ}
    {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k)
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    (hsymμ : μ.map Prod.fst = μ.map Prod.snd)
    (hsymν : ν.map Prod.fst = ν.map Prod.snd)
    (hmom : FiniteSiteObservation.momentPair K k μ =
      FiniteSiteObservation.momentPair K k ν) : observationLaw K k μ = observationLaw K k ν := by
  rw [observationLaw_eq hK, observationLaw_eq hK]
  exact FiniteSiteObservation.law_eq_of_momentPair_eq hK hk hμ hν hsymμ hsymν hmom

end Rhone.Statistics.Identifiability.EqualRatesMutation
