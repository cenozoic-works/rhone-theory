/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.InhomogeneousMarkovFlow
public import Rhone.Statistics.Identifiability.GeneratorValid

/-! # The time-dependent two-state together/apart pair chain -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

theorem timeVaryingPairGenerator_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) :
    ∀ i j, Continuous (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp
      [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.totalMigration] <;>
      fun_prop

theorem timeVaryingPairGenerator_row_sum (k : ℕ) (c q : ℝ) (i : Fin 2) :
    (∑ j, MarkovChain.Identifiability.pairGenerator k c q i j) = if i = 0 then -c else 0 := by
  fin_cases i <;> simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_two]

theorem timeVaryingPairGenerator_row_bounds (k : ℕ) {c q : ℝ} (hc : 0 ≤ c)
    (i : Fin 2) :
    -c ≤ (∑ j, MarkovChain.Identifiability.pairGenerator k c q i j) ∧
        (∑ j, MarkovChain.Identifiability.pairGenerator k c q i j) ≤ 0 := by
  rw [timeVaryingPairGenerator_row_sum]
  split <;> constructor <;> linarith

theorem exists_timeVaryingPairMass (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) :
    ∃ v : ℝ → Fin 2 → ℝ, v 0 = ![1, 0] ∧ Continuous v ∧
      (∀ t j, HasDerivAt (fun s => v s j)
        (∑ i, v t i * MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      AntitoneOn (fun t => ∑ i, v t i) (Ici 0) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) ≤ 1) := by
  obtain ⟨v, hvzero, hvc, he, hn, ha, hm⟩ :=
    exists_inhomogeneous_subgenerator_solution
      (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t))
      (timeVaryingPairGenerator_continuous k c q hc hq)
      (fun t ht => pairGenerator_metzler k (hqn t ht))
      (fun t ht i => (timeVaryingPairGenerator_row_bounds k (hcn t ht) i).2)
      ![1, 0] (by intro i; fin_cases i <;> norm_num)
  refine ⟨v, hvzero, hvc, he, hn, ha, ?_⟩
  intro t ht
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, add_zero] using hm t ht

theorem timeVaryingPairMass_survival_lower_bound (k : ℕ) (c q : ℝ → ℝ)
    (v : ℝ → Fin 2 → ℝ) (hc : Continuous c)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t)
    (he : ∀ t, 0 ≤ t → ∀ j, HasDerivAt (fun s => v s j)
      (∑ i, v t i * MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) t)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hvzero : v 0 = ![1, 0]) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(∫ s in (0 : ℝ)..t, c s)) ≤ ∑ i, v t i := by
  have h := finiteRowODE_mass_lower_integral
    (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) v c hc he hn
    (fun t ht i => (timeVaryingPairGenerator_row_bounds k (hcn t ht) i).1) ht
  simpa only [hvzero, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, add_zero, one_mul] using h

theorem timeVaryingPairMass_proper_coalescence_diverges (k : ℕ) (c q : ℝ → ℝ)
    (v : ℝ → Fin 2 → ℝ) (hc : Continuous c)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t)
    (he : ∀ t, 0 ≤ t → ∀ j, HasDerivAt (fun s => v s j)
      (∑ i, v t i * MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) t)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hvzero : v 0 = ![1, 0])
    (hproper : Tendsto (fun t => ∑ i, v t i) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ s in (0 : ℝ)..t, c s) atTop atTop := by
  apply tendsto_atTop_of_survival_lower_bound (fun t => ∑ i, v t i)
    (fun t => ∫ s in (0 : ℝ)..t, c s) (a := 1) (by norm_num) hproper
  intro t ht
  simpa only [one_mul] using
    timeVaryingPairMass_survival_lower_bound k c q v hc hcn he hn hvzero ht

theorem timeVaryingPairMass_survival_hasDerivAt (k : ℕ) (c q : ℝ → ℝ)
    (v : ℝ → Fin 2 → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j, HasDerivAt (fun s => v s j)
      (∑ i, v t i * MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) t)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ∑ i, v s i) (-c t * v t 0) t := by
  convert! finiteRowODE_mass_hasDerivAt
    (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) v he ht using 1
  simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_two]
  ring

theorem timeVaryingPairMass_together_positive (k : ℕ) (c q : ℝ → ℝ)
    (v : ℝ → Fin 2 → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (he : ∀ t, 0 ≤ t → ∀ j, HasDerivAt (fun s => v s j)
      (∑ i, v t i * MarkovChain.Identifiability.pairGenerator k (c t) (q t) i j) t)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hvzero : v 0 = ![1, 0]) {t : ℝ} (ht : 0 ≤ t) : 0 < v t 0 := by
  exact inhomogeneous_row_coordinate_positive
    (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) v 0
    (timeVaryingPairGenerator_continuous k c q hc hq 0 0)
    (fun t ht i hi => pairGenerator_metzler k (hqn t ht) i 0 hi)
    (fun t ht => he t ht 0) hn (by simp [hvzero]) ht

end Rhone.Statistics.Identifiability
