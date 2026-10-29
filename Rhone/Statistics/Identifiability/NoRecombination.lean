/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FlowSeries
public import Rhone.Statistics.Identifiability.PairNonidentifiability

/-! # With zero recombination, linked loci carry exactly one pair genealogy -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem generator_row_one_no_recomb (k : Nat) (c q : ℝ)
    (v : MarkovChain.Identifiability.State → ℝ) :
    (MarkovChain.Identifiability.generator k c q 0 *ᵥ v) 1 = 2*q*v 0 - 2*q*v 1 := by
  simp [MarkovChain.Identifiability.generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.occupiedTable,
        MarkovChain.Identifiability.emptyTable, MarkovChain.Identifiability.occupiedDemes]
  ring

theorem no_recombination_power_pair (k : Nat) (c q : ℝ) (v : MarkovChain.Identifiability.State → ℝ)
    (n : Nat) :
    ((MarkovChain.Identifiability.generator k c q 0)^n *ᵥ v) 0 =
        ((MarkovChain.Identifiability.pairGenerator k c q)^n *ᵥ ![v 0,v 1]) 0 ∧
    ((MarkovChain.Identifiability.generator k c q 0)^n *ᵥ v) 1 =
        ((MarkovChain.Identifiability.pairGenerator k c q)^n *ᵥ ![v 0,v 1]) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', ← Matrix.mulVec_mulVec]
    constructor
    · rw [MarkovChain.Identifiability.row_zero]
      simp only [mul_zero, zero_mul, add_zero, sub_zero, ih.1, ih.2]
      simp [MarkovChain.Identifiability.pairGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · rw [generator_row_one_no_recomb, ih.1, ih.2]
      simp [MarkovChain.Identifiability.pairGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring

set_option backward.isDefEq.respectTransparency false in
theorem no_recombination_flow_pair (k : Nat) (c q t : ℝ)
    (v : MarkovChain.Identifiability.State → ℝ) :
    flowOutput (MarkovChain.Identifiability.generator k c q 0) 0 v 0 t = flowOutput
        (MarkovChain.Identifiability.pairGenerator k c q) 0 ![v 0,v 1] 0 t := by
  have hQ := flowOutput_series (MarkovChain.Identifiability.generator k c q 0) 0 v t
  have hK := flowOutput_series (MarkovChain.Identifiability.pairGenerator k c q) 0 ![v 0,v 1] t
  simp only [(no_recombination_power_pair k c q v _).1] at hQ
  exact hQ.unique hK

theorem mark_counts_pair_states : ∀ m : Fin 5,
    markCount 0 m = (if m = 0 then 1 else 0) ∧ markCount 1 m = 0 := by decide

theorem no_recombination_markFlux (k : Nat) (c q t : ℝ) (m : Fin 5) :
    markFlux k c q 0 m t = if m = 0 then densityJet k c q 0 t else 0 := by
  unfold markFlux
  rw [no_recombination_flow_pair]
  have hv : (![markRates c 0 m,markRates c 1 m] : Fin 2 → ℝ) =
      if m = 0 then MarkovChain.Identifiability.pairDensity c else 0 := by
    by_cases hm : m = 0
    · simp [hm, markRates, (mark_counts_pair_states 0).1,
        (mark_counts_pair_states 0).2, MarkovChain.Identifiability.pairDensity]
    · simp [hm, markRates, (mark_counts_pair_states m).1, (mark_counts_pair_states m).2]
  rw [hv]
  by_cases hm : m = 0
  · simp [hm, densityJet]
  · simp [hm, flowOutput]

theorem no_recombination_markLaw (k : Nat) (c q : ℝ) (m : Fin 5) :
    markLaw k c q 0 m = if m = 0 then firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
        0 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp only [markLaw, ↓reduceIte, firstExitLaw, pair_exitRate]
    congr 1
    funext t
    rw [no_recombination_markFlux]
    rfl
  · simp [markLaw, no_recombination_markFlux, hm]

theorem no_recombination_joint_diagonal (k : Nat) (c q : ℝ) :
    jointLaw k c q 0 = (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0).map
        (fun t => (t,t)) := by
  have : SFinite (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0) := by
    unfold firstExitLaw
    infer_instance
  have hterm (m : Fin 5) :
      ((markLaw k c q 0 m).prod (lagLaw k c q m)).map (recoverTimes m) =
      if m = 0 then (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0).map
          (fun t => (t,t)) else 0 := by
    by_cases hm : m = 0
    · subst m
      rw [no_recombination_markLaw, ite_eq_left rfl, lagLaw, ite_eq_left rfl, Measure.prod_dirac,
        Measure.map_map (f := fun x : ℝ => (x,0)) (g := recoverTimes 0)
          (recoverTimes_continuous 0).measurable
          (measurable_id.prodMk measurable_const), ite_eq_left rfl]
      rfl
    · simp [no_recombination_markLaw, hm]
  unfold jointLaw
  simp_rw [hterm]
  ext s hs
  rw [Measure.sum_apply _ hs]
  have happly (m : Fin 5) :
      (if m = 0 then (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0).map
          (fun t => (t,t)) else 0) s =
      if m = 0 then ((firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0).map
          (fun t => (t,t))) s else 0 := by
    split <;> rfl
  simp_rw [happly]
  simp

noncomputable def diagonalPanLaw (rate : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (panPairLaw rate).map (fun t => (t,t))

theorem zero_recombination_law_identity (k : Nat) (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    jointLaw k c q 0 = diagonalPanLaw (pairHazard k c q) := by
  rw [no_recombination_joint_diagonal, diagonalPanLaw, panPairLaw_pairHazard_eq k c hq]

theorem zero_recombination_exact_size_match (k : Nat) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    ∃ rate : ℝ → ℝ, (∀ t, 0 ≤ t → 0 < rate t) ∧
      jointLaw k c q 0 = diagonalPanLaw rate ∧ IsProbabilityMeasure (diagonalPanLaw rate) := by
  refine ⟨pairHazard k c q, fun t ht => pairHazard_pos k hc hq.le ht,
    zero_recombination_law_identity k c hq.le, ?_⟩
  rw [← zero_recombination_law_identity k c hq.le]
  exact jointLaw_probability k hc hq (le_refl 0)

end Rhone.Statistics.Identifiability
