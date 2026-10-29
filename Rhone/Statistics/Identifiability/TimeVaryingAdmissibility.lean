/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingFirstExit
public import Rhone.Statistics.Identifiability.Admissibility

/-! # Invariance of the admissible state set under time-dependent evolution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem peanoBaker_term_no_escape (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (P : ι → Prop) (hQ : ∀ t i j, P i → ¬ P j → Q t i j = 0)
    (x : ι → ℝ) (hx : ∀ j, ¬ P j → x j = 0) (n : ℕ) (t : ℝ)
    (j : ι) (hj : ¬ P j) :
    PeanoBaker.term (fun s => inhomogeneousRowOperator (Q s)) x n t j = 0 := by
  classical
  let A := fun s => inhomogeneousRowOperator (Q s)
  have hA : Continuous A := inhomogeneousRowOperator_continuous Q hQc
  change PeanoBaker.term A x n t j = 0
  induction n generalizing t j with
  | zero => exact hx j hj
  | succ n ih =>
    have hcont : Continuous (fun s => A s (PeanoBaker.term A x n s)) :=
      hA.clm_apply (PeanoBaker.term_continuous A hA x n)
    have hi : IntervalIntegrable (fun s => A s (PeanoBaker.term A x n s)) volume 0 t :=
      hcont.intervalIntegrable 0 t
    rw [PeanoBaker.term_succ]
    change (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)
      (∫ s in (0 : ℝ)..t, A s (PeanoBaker.term A x n s)) = 0
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
    have hz : (∫ _s in (0 : ℝ)..t, (0 : ℝ)) = 0 := by simp
    conv_rhs => rw [← hz]
    apply intervalIntegral.integral_congr
    intro s _
    change (∑ i, PeanoBaker.term A x n s i * Q s i j) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hiP : P i
    · rw [hQ s i j hiP hj, mul_zero]
    · rw [ih s i hiP, zero_mul]

theorem inhomogeneousFundamental_no_escape (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (P : ι → Prop) (hQ : ∀ t i j, P i → ¬ P j → Q t i j = 0)
    (t : ℝ) (i j : ι) (hi : P i) (hj : ¬ P j) :
    inhomogeneousFundamental Q t i j = 0 := by
  classical
  unfold inhomogeneousFundamental PeanoBaker.solution
  have hs := PeanoBaker.term_summable (fun s => inhomogeneousRowOperator (Q s))
    (inhomogeneousRowOperator_continuous Q hQc) ((1 : Matrix ι ι ℝ) i) t
  rw [Pi.tsum_apply hs]
  have hz : (∑' _n : ℕ, (0 : ℝ)) = 0 := tsum_zero
  rw [← hz]
  apply tsum_congr
  intro n
  apply peanoBaker_term_no_escape Q hQc P hQ _ _ n t j hj
  intro a ha
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [hia]

theorem inhomogeneousFundamentalInverse_no_escape (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (P : ι → Prop) (hQ : ∀ t i j, P i → ¬ P j → Q t i j = 0)
    (t : ℝ) (i j : ι) (hi : P i) (hj : ¬ P j) :
    inhomogeneousFundamentalInverse Q t i j = 0 := by
  classical
  apply inhomogeneousFundamental_no_escape (fun t => -(Q t).transpose)
    (fun a b => (hQc b a).neg) (fun a => ¬ P a) _ t j i hj (not_not_intro hi)
  intro u a b ha hb
  change -(Q u b a) = 0
  rw [hQ u b a (not_not.mp hb) ha, neg_zero]

theorem inhomogeneousTransition_no_escape (Q : ℝ → Matrix ι ι ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (P : ι → Prop) (hQ : ∀ t i j, P i → ¬ P j → Q t i j = 0)
    (s t : ℝ) (i j : ι) (hi : P i) (hj : ¬ P j) :
    inhomogeneousTransition Q s t i j = 0 := by
  classical
  rw [inhomogeneousTransition, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : P a
  · rw [inhomogeneousFundamental_no_escape Q hQc P hQ t a j ha hj, mul_zero]
  · rw [inhomogeneousFundamentalInverse_no_escape Q hQc P hQ s i a hi ha, zero_mul]

theorem timeVaryingARGTransition_no_escape (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (s t : ℝ) (i j : MarkovChain.Identifiability.State) (hi : Admissible k i)
        (hj : ¬ Admissible k j) :
    inhomogeneousTransition (timeVaryingARGGenerator k c q r) s t i j = 0 := by
  apply inhomogeneousTransition_no_escape _
    (timeVaryingARGGenerator_continuous k c q r hc hq hr) (Admissible k) _ s t i j hi hj
  intro u a b ha hb
  exact generator_no_escape k (c u) (q u) (r u) a b ha hb

theorem timeVaryingPreRow_no_escape (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (t : ℝ) (j : MarkovChain.Identifiability.State) (hj : ¬ Admissible k j) :
    timeVaryingPreRow k c q r t j = 0 :=
  timeVaryingARGTransition_no_escape k c q r hc hq hr 0 t 0 j (initial_admissible k) hj

theorem timeVaryingPreRow_not_admissible (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (t : ℝ) (j : MarkovChain.Identifiability.State) (hj : ¬ Admissible k j) :
    timeVaryingPreRow k c q r t j = 0 :=
  timeVaryingPreRow_no_escape k c q r hc hq hr t j hj

end Rhone.Statistics.Identifiability
