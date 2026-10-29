/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.Generator
public import Rhone.Statistics.Identifiability.MatrixFlow
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Tactic.Positivity

/-! # A nonzero analytic conditional-coalescence witness -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Filter Set

namespace Rhone.Statistics.Identifiability

noncomputable def survivalJet (k : Nat) (c q : ℝ) (a : Nat) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival a t

noncomputable def densityJet (k : Nat) (c q : ℝ) (a : Nat) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) 0
      (MarkovChain.Identifiability.pairDensity c) a t

noncomputable def firstAJet (k : Nat) (c q r : ℝ) (a : Nat) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.generator k c q r) 0
      (MarkovChain.Identifiability.firstA c) a t

noncomputable def postBJet (k : Nat) (c q r : ℝ) (a : Nat) (t : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.generator k c q r) 0 (MarkovChain.Identifiability.nextB c)
      a t

noncomputable def witness (k : Nat) (c q r t : ℝ) : ℝ :=
  survivalJet k c q 0 t * postBJet k c q r 0 t -
    densityJet k c q 0 t * firstAJet k c q r 0 t

noncomputable def witnessD (k : Nat) (c q r t : ℝ) : ℝ :=
  survivalJet k c q 1 t * postBJet k c q r 0 t +
    survivalJet k c q 0 t * postBJet k c q r 1 t -
    (densityJet k c q 1 t * firstAJet k c q r 0 t +
      densityJet k c q 0 t * firstAJet k c q r 1 t)

noncomputable def witnessDD (k : Nat) (c q r t : ℝ) : ℝ :=
  survivalJet k c q 2 t * postBJet k c q r 0 t +
    2 * survivalJet k c q 1 t * postBJet k c q r 1 t +
    survivalJet k c q 0 t * postBJet k c q r 2 t -
    (densityJet k c q 2 t * firstAJet k c q r 0 t +
      2 * densityJet k c q 1 t * firstAJet k c q r 1 t +
      densityJet k c q 0 t * firstAJet k c q r 2 t)

theorem witness_hasDerivAt (k : Nat) (c q r t : ℝ) :
    HasDerivAt (witness k c q r) (witnessD k c q r t) t := by
  exact ((flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 0 t).mul
    (flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
        (MarkovChain.Identifiability.nextB c) 0 t)).sub
    ((flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
        (MarkovChain.Identifiability.pairDensity c) 0 t).mul
      (flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
          (MarkovChain.Identifiability.firstA c) 0 t))

set_option backward.isDefEq.respectTransparency false in
theorem witnessD_hasDerivAt (k : Nat) (c q r t : ℝ) :
    HasDerivAt (witnessD k c q r) (witnessDD k c q r t) t := by
  have hs0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 0 t
  have hs1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 1 t
  have hf0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      (MarkovChain.Identifiability.pairDensity c) 0 t
  have hf1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) 0
      (MarkovChain.Identifiability.pairDensity c) 1 t
  have hb0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
      (MarkovChain.Identifiability.firstA c) 0 t
  have hb1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
      (MarkovChain.Identifiability.firstA c) 1 t
  have hj0 := flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
      (MarkovChain.Identifiability.nextB c) 0 t
  have hj1 := flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
      (MarkovChain.Identifiability.nextB c) 1 t
  convert! ((hs1.mul hj0).add (hs0.mul hj1)).sub
    ((hf1.mul hb0).add (hf0.mul hb1)) using 1
  dsimp [witnessDD, survivalJet, densityJet, firstAJet, postBJet]
  ring

@[simp] theorem witness_zero (k : Nat) (c q r : ℝ) : witness k c q r 0 = 0 := by
  simp [witness, survivalJet, densityJet, firstAJet, postBJet]

@[simp] theorem witnessD_zero (k : Nat) (c q r : ℝ) : witnessD k c q r 0 = 0 := by
  simp only [witnessD, survivalJet, densityJet, firstAJet, postBJet,
    flowOutput_zero, pow_zero, pow_one, Matrix.one_mulVec,
    MarkovChain.Identifiability.firstA_initial, MarkovChain.Identifiability.nextB_initial,
        MarkovChain.Identifiability.pairSurvival_initial,
        MarkovChain.Identifiability.pairDensity_initial,
    mul_zero, zero_add, one_mul,
    MarkovChain.Identifiability.firstA_jet_one, MarkovChain.Identifiability.nextB_jet_one]
  ring

theorem witnessDD_zero (k : Nat) (c q r : ℝ) :
    witnessDD k c q r 0 = 6*r*c^2*MarkovChain.Identifiability.totalMigration k q := by
  simp only [witnessDD, survivalJet, densityJet, firstAJet, postBJet,
    flowOutput_zero, pow_zero, pow_one, Matrix.one_mulVec,
    MarkovChain.Identifiability.firstA_initial, MarkovChain.Identifiability.nextB_initial,
        MarkovChain.Identifiability.pairSurvival_initial,
        MarkovChain.Identifiability.pairDensity_initial,
    mul_zero, zero_add, one_mul,
    MarkovChain.Identifiability.firstA_jet_one, MarkovChain.Identifiability.nextB_jet_one,
        MarkovChain.Identifiability.firstA_jet_two, MarkovChain.Identifiability.nextB_jet_two,
    MarkovChain.Identifiability.pair_survival_jet_one,
        MarkovChain.Identifiability.pair_density_jet_one]
  ring

theorem witnessDD_pos (k : Nat) {c q r : ℝ} (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    0 < witnessDD k c q r 0 := by
  rw [witnessDD_zero]
  unfold MarkovChain.Identifiability.totalMigration
  positivity

theorem not_zero_on_nonnegative_of_second_derivative
    (f f₁ f₂ : ℝ → ℝ)
    (h₀ : ∀ t, HasDerivAt f (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (h₁zero : f₁ 0 = 0) (hne : f₂ 0 ≠ 0) :
    ¬ (∀ t, 0 ≤ t → f t = 0) := by
  intro hz
  have hz₁ : ∀ t, 0 < t → f₁ t = 0 := by
    intro t ht
    have heq : f =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact hz x (le_of_lt hx)
    exact (h₀ t).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq)
  have heq₁ : ∀ t ∈ Ici (0 : ℝ), f₁ t = (0 : ℝ) := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with heq | hlt
    · simpa [← heq] using h₁zero
    · exact hz₁ t hlt
  have hconst : HasDerivWithinAt f₁ 0 (Ici (0 : ℝ)) 0 :=
    (hasDerivWithinAt_const 0 (Ici (0 : ℝ)) (0 : ℝ)).congr heq₁ h₁zero
  exact hne ((uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _
    (h₁ 0).hasDerivWithinAt hconst)

theorem island_witness_not_identically_zero (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ (∀ t, 0 ≤ t → witness k c q r t = 0) :=
  not_zero_on_nonnegative_of_second_derivative
    (witness k c q r) (witnessD k c q r) (witnessDD k c q r)
    (witness_hasDerivAt k c q r) (witnessD_hasDerivAt k c q r)
    (witnessD_zero k c q r) (ne_of_gt (witnessDD_pos k hc hq hr))

end Rhone.Statistics.Identifiability
