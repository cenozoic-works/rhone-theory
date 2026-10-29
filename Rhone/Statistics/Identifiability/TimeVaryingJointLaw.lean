/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingARGSymmetry
public import Rhone.Statistics.Identifiability.RegularJointLawNormalization

/-! # A normalized time-dependent two-locus event law -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def timeVaryingBranchFlux (k : ℕ) (c q r : ℝ → ℝ)
    (m₀ m₁ : Fin 5) (s : ℝ) : ℝ :=
  timeVaryingMarkFlux k c q r m₀ s + timeVaryingMarkFlux k c q r m₁ s

noncomputable def timeVaryingBranchDensity (k : ℕ) (c q r : ℝ → ℝ)
    (m₀ m₁ : Fin 5) (p : ℝ × ℝ) : ℝ :=
  timeVaryingMarkFlux k c q r m₀ p.1 * timeVaryingPairExitDensity k c q p.1 0 p.2 +
  timeVaryingMarkFlux k c q r m₁ p.1 * timeVaryingPairExitDensity k c q p.1 1 p.2

noncomputable def timeVaryingDiagonalDensity (k : ℕ) (c q r : ℝ → ℝ) : ℝ → ℝ :=
  timeVaryingMarkFlux k c q r 0

noncomputable def timeVaryingUpperDensity (k : ℕ) (c q r : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  timeVaryingBranchDensity k c q r 1 2

noncomputable def timeVaryingLowerBranchDensity (k : ℕ) (c q r : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  timeVaryingBranchDensity k c q r 3 4

noncomputable def timeVaryingJointLaw (k : ℕ) (c q r : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  diagonalDensityLaw (timeVaryingDiagonalDensity k c q r) +
  triangularDensityLaw (timeVaryingUpperDensity k c q r) +
  (triangularDensityLaw (timeVaryingLowerBranchDensity k c q r)).map Prod.swap

noncomputable def diagonalExit (c : ℝ) : MarkovChain.Identifiability.State → ℝ := fun i => markRates
    c i 0

noncomputable def firstBKernel (c : ℝ) : Matrix MarkovChain.Identifiability.State (Fin 2) ℝ :=
  fun i j => if j = 0 then markRates c i 3 else markRates c i 4

theorem timeVaryingDiagonalDensity_matrix (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) :
    timeVaryingDiagonalDensity k c q r t =
      timeVaryingPreRow k c q r t ⬝ᵥ diagonalExit (c t) := rfl

theorem timeVaryingARGGenerator_row_balance_split (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) (i : MarkovChain.Identifiability.State) :
    (∑ j, timeVaryingARGGenerator k c q r t i j) =
      -diagonalExit (c t) i - (∑ j, firstAKernel (c t) i j) -
        (∑ j, firstBKernel (c t) i j) := by
  rw [timeVaryingARGGenerator_row_balance]
  simp [Fin.sum_univ_succ, diagonalExit, firstBKernel,
    ← markRates_A_same, ← markRates_A_apart]
  ring

theorem timeVaryingUpperDensity_matrix (k : ℕ) (c q r : ℝ → ℝ) (s t : ℝ) :
    timeVaryingUpperDensity k c q r (s,t) =
      ((timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) ᵥ*
        timeVaryingPairTransition k c q s t) ⬝ᵥ MarkovChain.Identifiability.pairDensity (c t) := by
  have h₀ : timeVaryingMarkFlux k c q r 1 s =
      (timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) 0 := by
    simp only [timeVaryingMarkFlux, Matrix.vecMul, dotProduct, markRates_A_same]
  have h₁ : timeVaryingMarkFlux k c q r 2 s =
      (timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) 1 := by
    simp only [timeVaryingMarkFlux, Matrix.vecMul, dotProduct, markRates_A_apart]
  simp only [timeVaryingUpperDensity, timeVaryingBranchDensity, timeVaryingPairExitDensity,
    h₀, h₁]
  simp only [dotProduct, Fin.sum_univ_two, MarkovChain.Identifiability.pairDensity,
      Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, Matrix.vecMul]
  ring

theorem timeVaryingLowerBranchDensity_matrix (k : ℕ) (c q r : ℝ → ℝ) (s t : ℝ) :
    timeVaryingLowerBranchDensity k c q r (s,t) =
      ((timeVaryingPreRow k c q r s ᵥ* firstBKernel (c s)) ᵥ*
        timeVaryingPairTransition k c q s t) ⬝ᵥ MarkovChain.Identifiability.pairDensity (c t) := by
  have h₀ : timeVaryingMarkFlux k c q r 3 s =
      (timeVaryingPreRow k c q r s ᵥ* firstBKernel (c s)) 0 := by
    simp [timeVaryingMarkFlux, Matrix.vecMul, dotProduct, firstBKernel]
  have h₁ : timeVaryingMarkFlux k c q r 4 s =
      (timeVaryingPreRow k c q r s ᵥ* firstBKernel (c s)) 1 := by
    simp [timeVaryingMarkFlux, Matrix.vecMul, dotProduct, firstBKernel]
  simp only [timeVaryingLowerBranchDensity, timeVaryingBranchDensity, timeVaryingPairExitDensity,
    h₀, h₁]
  simp only [dotProduct, Fin.sum_univ_two, MarkovChain.Identifiability.pairDensity,
      Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, Matrix.vecMul]
  ring

theorem timeVaryingBranchFlux_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (m₀ m₁ : Fin 5) :
    Continuous (timeVaryingBranchFlux k c q r m₀ m₁) :=
  (timeVaryingMarkFlux_continuous k c q r hc hq hr m₀).add
    (timeVaryingMarkFlux_continuous k c q r hc hq hr m₁)

theorem timeVaryingBranchDensity_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (m₀ m₁ : Fin 5) :
    Continuous (timeVaryingBranchDensity k c q r m₀ m₁) :=
  (((timeVaryingMarkFlux_continuous k c q r hc hq hr m₀).comp continuous_fst).mul
    (timeVaryingPairExitDensity_continuous k c q hc hq 0)).add
  (((timeVaryingMarkFlux_continuous k c q r hc hq hr m₁).comp continuous_fst).mul
    (timeVaryingPairExitDensity_continuous k c q hc hq 1))

theorem timeVaryingBranchFlux_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {s : ℝ} (hs : 0 ≤ s) (m₀ m₁ : Fin 5) :
    0 ≤ timeVaryingBranchFlux k c q r m₀ m₁ s :=
  add_nonneg (timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs m₀)
    (timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs m₁)

theorem timeVaryingBranchDensity_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (m₀ m₁ : Fin 5) : 0 ≤ timeVaryingBranchDensity k c q r m₀ m₁ (s,t) :=
  add_nonneg (mul_nonneg
    (timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs m₀)
    (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs hst 0))
    (mul_nonneg (timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs m₁)
    (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs hst 1))

theorem timeVaryingJointDensities_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    Continuous (timeVaryingDiagonalDensity k c q r) ∧
    Continuous (timeVaryingUpperDensity k c q r) ∧
    Continuous (timeVaryingLowerBranchDensity k c q r) :=
  ⟨timeVaryingMarkFlux_continuous k c q r hc hq hr 0,
    timeVaryingBranchDensity_continuous k c q r hc hq hr 1 2,
    timeVaryingBranchDensity_continuous k c q r hc hq hr 3 4⟩

theorem timeVaryingJointDensities_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) :
    (∀ t, 0 ≤ t → 0 ≤ timeVaryingDiagonalDensity k c q r t) ∧
    (∀ p ∈ upperWedge, 0 ≤ timeVaryingUpperDensity k c q r p) ∧
    (∀ p ∈ upperWedge, 0 ≤ timeVaryingLowerBranchDensity k c q r p) := by
  refine ⟨fun t ht => timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn ht 0,
    ?_, ?_⟩
  · intro p hp
    exact timeVaryingBranchDensity_nonneg k c q r hc hq hr hcn hqn hrn hp.1.le hp.2.le 1 2
  · intro p hp
    exact timeVaryingBranchDensity_nonneg k c q r hc hq hr hcn hqn hrn hp.1.le hp.2.le 3 4

theorem timeVaryingBranchDensity_lintegral (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {s : ℝ} (hs : 0 ≤ s) (m₀ m₁ : Fin 5)
    (htail : ∀ i, Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (timeVaryingBranchDensity k c q r m₀ m₁ (s,t))) =
      ENNReal.ofReal (timeVaryingBranchFlux k c q r m₀ m₁ s) := by
  have hm (m : Fin 5) := timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs m
  have hf (i : Fin 2) : Measurable (fun t =>
      ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) :=
    ((timeVaryingPairExitDensity_continuous k c q hc hq i).comp
      (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi s,
        ENNReal.ofReal (timeVaryingMarkFlux k c q r m₀ s) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t) +
        ENNReal.ofReal (timeVaryingMarkFlux k c q r m₁ s) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 1 t) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [timeVaryingBranchDensity]
      rw [ENNReal.ofReal_add
        (mul_nonneg (hm m₀) (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs ht.le 0))
        (mul_nonneg (hm m₁) (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs ht.le 1)),
        ENNReal.ofReal_mul (hm m₀), ENNReal.ofReal_mul (hm m₁)]
    _ = _ := by
      rw [lintegral_add_left (f := fun t =>
          ENNReal.ofReal (timeVaryingMarkFlux k c q r m₀ s) *
          ENNReal.ofReal (timeVaryingPairExitDensity k c q s 0 t))
          (measurable_const.mul (hf 0)),
        lintegral_const_mul _ (hf 0), lintegral_const_mul _ (hf 1),
        timeVaryingPairExitDensity_lintegral_one k c q hc hq hcn hqn hs 0 (htail 0),
        timeVaryingPairExitDensity_lintegral_one k c q hc hq hcn hqn hs 1 (htail 1),
        mul_one, mul_one, timeVaryingBranchFlux, ENNReal.ofReal_add (hm m₀) (hm m₁)]

theorem timeVaryingFirstExitDensity_partition (k : ℕ) (c q r : ℝ → ℝ) (s : ℝ) :
    timeVaryingFirstExitDensity k c q r s = timeVaryingDiagonalDensity k c q r s +
      timeVaryingBranchFlux k c q r 1 2 s + timeVaryingBranchFlux k c q r 3 4 s := by
  simp [timeVaryingFirstExitDensity, timeVaryingDiagonalDensity,
    timeVaryingBranchFlux, Fin.sum_univ_succ]
  ring

theorem timeVaryingJointLaw_probability (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpre : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0))
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingJointLaw k c q r) := by
  apply asymmetricDensityLaw_probability
    (timeVaryingDiagonalDensity k c q r)
    (timeVaryingBranchFlux k c q r 1 2) (timeVaryingBranchFlux k c q r 3 4)
    (timeVaryingUpperDensity k c q r) (timeVaryingLowerBranchDensity k c q r)
    (timeVaryingMarkFlux_continuous k c q r hc hq hr 0).measurable
    (timeVaryingBranchFlux_continuous k c q r hc hq hr 1 2).measurable
    (timeVaryingBranchFlux_continuous k c q r hc hq hr 3 4).measurable
    (timeVaryingBranchDensity_continuous k c q r hc hq hr 1 2).measurable
    (timeVaryingBranchDensity_continuous k c q r hc hq hr 3 4).measurable
    (fun s hs => timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn hs.le 0)
    (fun s hs => timeVaryingBranchFlux_nonneg k c q r hc hq hr hcn hqn hrn hs.le 1 2)
    (fun s hs => timeVaryingBranchFlux_nonneg k c q r hc hq hr hcn hqn hrn hs.le 3 4)
    (fun s hs => timeVaryingBranchDensity_lintegral k c q r hc hq hr hcn hqn hrn hs.le 1 2
      (hpair s hs.le))
    (fun s hs => timeVaryingBranchDensity_lintegral k c q r hc hq hr hcn hqn hrn hs.le 3 4
      (hpair s hs.le))
  simpa only [← timeVaryingFirstExitDensity_partition] using
    timeVaryingFirstExitDensity_lintegral_one k c q r hc hq hr hcn hqn hrn hpre

theorem timeVaryingBranchFlux_locusExchange (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    timeVaryingBranchFlux k c q r 3 4 = timeVaryingBranchFlux k c q r 1 2 := by
  funext s
  simp only [timeVaryingBranchFlux,
    timeVaryingMarkFlux_locusExchange_same k c q r hc hq hr,
    timeVaryingMarkFlux_locusExchange_apart k c q r hc hq hr]

theorem timeVaryingLowerBranchDensity_eq_upper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    timeVaryingLowerBranchDensity k c q r = timeVaryingUpperDensity k c q r := by
  funext p
  simp only [timeVaryingLowerBranchDensity, timeVaryingUpperDensity,
    timeVaryingBranchDensity,
    timeVaryingMarkFlux_locusExchange_same k c q r hc hq hr,
    timeVaryingMarkFlux_locusExchange_apart k c q r hc hq hr]

theorem timeVaryingJointLaw_eq_regular (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    timeVaryingJointLaw k c q r = regularJointLaw (timeVaryingDiagonalDensity k c q r)
      (timeVaryingUpperDensity k c q r) := by
  rw [timeVaryingJointLaw, timeVaryingLowerBranchDensity_eq_upper k c q r hc hq hr]
  rfl

theorem timeVaryingFirstExitDensity_symmetric_partition (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (s : ℝ) :
    timeVaryingFirstExitDensity k c q r s = timeVaryingDiagonalDensity k c q r s +
      2 * timeVaryingBranchFlux k c q r 1 2 s := by
  rw [timeVaryingFirstExitDensity_partition,
    timeVaryingBranchFlux_locusExchange k c q r hc hq hr]
  ring

theorem timeVaryingPreSurvival_hasDerivAt_symmetric (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (s : ℝ) :
    HasDerivAt (timeVaryingPreSurvival k c q r)
      (-(timeVaryingDiagonalDensity k c q r s +
        2 * timeVaryingBranchFlux k c q r 1 2 s)) s := by
  rw [← timeVaryingFirstExitDensity_symmetric_partition k c q r hc hq hr]
  exact timeVaryingPreSurvival_hasDerivAt k c q r hc hq hr s

theorem timeVaryingRegularJointLaw_probability (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpre : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0))
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (regularJointLaw (timeVaryingDiagonalDensity k c q r)
      (timeVaryingUpperDensity k c q r)) := by
  rw [← timeVaryingJointLaw_eq_regular k c q r hc hq hr]
  exact timeVaryingJointLaw_probability k c q r hc hq hr hcn hqn hrn hpre hpair

theorem timeVaryingJointLaw_restrict_upper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    (timeVaryingJointLaw k c q r).restrict upperWedge =
      triangularDensityLaw (timeVaryingUpperDensity k c q r) := by
  rw [timeVaryingJointLaw_eq_regular k c q r hc hq hr, regularJointLaw_restrict_upper]

theorem timeVaryingJointLaw_restrict_diagonal (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    (timeVaryingJointLaw k c q r).restrict timeDiagonal =
      diagonalDensityLaw (timeVaryingDiagonalDensity k c q r) := by
  rw [timeVaryingJointLaw_eq_regular k c q r hc hq hr, regularJointLaw_restrict_diagonal]

end Rhone.Statistics.Identifiability
