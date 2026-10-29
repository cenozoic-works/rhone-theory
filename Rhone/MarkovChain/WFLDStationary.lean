/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFMutationRecombination
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Stationary laws for the finite mutation-recombination haplotype chain

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset Filter
open scoped Topology

variable (M : ℕ) (hM : 0 < M) (c u : ℝ)
  (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
local notation "C" => ldWFChain M hM c u hc0 hc1 hu0 hu1
local notation "S" => Rhone.MarkovChain.AlleleCounts M 4

/-- Source: ewens2004, sec. 3.1. -/
def ldCesaro (x : S) (n : ℕ) (b : S) : ℝ :=
  (∑ k ∈ range (n+1), (C).stepN k x b)/(n+1)

local notation "A" => ldCesaro M hM c u hc0 hc1 hu0 hu1

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_cesaro_distribution (x : S) (n : ℕ) :
    (∀ b, 0 ≤ A x n b) ∧ ∑ b, A x n b = 1 := by
  constructor
  · intro b
    exact div_nonneg (sum_nonneg fun k _ => (C).stepN_nonneg k x b) (by positivity)
  · unfold ldCesaro
    rw [← sum_div, sum_comm]
    simp only [(C).stepN_row_sum, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    norm_num [hn]

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_cesaro_discrepancy (x b : S) (n : ℕ) :
    (∑ a, A x n a*(C).P a b)-A x n b =
      ((C).stepN (n+1) x b-(C).stepN 0 x b)/(n+1) := by
  have hstep (k : ℕ) : ∑ a, (C).stepN k x a*(C).P a b = (C).stepN (k+1) x b := by
    rw [(C).stepN_succ']
    rfl
  have htel : (∑ k ∈ range (n+1), (C).stepN (k+1) x b) -
      (∑ k ∈ range (n+1), (C).stepN k x b) = (C).stepN (n+1) x b-(C).stepN 0 x b := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ (f := fun k => (C).stepN (k+1) x b) (n := n+1),
        sum_range_succ (f := fun k => (C).stepN k x b) (n := n+1)]
      linear_combination ih
  unfold ldCesaro
  simp_rw [div_mul_eq_mul_div, ← sum_div, sum_mul]
  rw [sum_comm]
  simp_rw [hstep]
  rw [← sub_div, htel]

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_cesaro_discrepancy_limit (x b : S) :
    Tendsto (fun n => (∑ a, A x n a*(C).P a b)-A x n b) atTop (𝓝 0) := by
  have hb (k : ℕ) : (C).stepN k x b ≤ 1 := by
    calc
      (C).stepN k x b ≤ ∑ a, (C).stepN k x a :=
        single_le_sum (fun a _ => (C).stepN_nonneg k x a) (mem_univ b)
      _ = 1 := (C).stepN_row_sum k x
  simp only [ld_cesaro_discrepancy]
  apply tendsto_bdd_div_atTop_nhds_zero (b := -1) (B := 1)
  · exact Eventually.of_forall fun n => by
      have h := (C).stepN_nonneg (n+1) x b
      have h0 := hb 0
      linarith
  · exact Eventually.of_forall fun n => by
      have h := hb (n+1)
      have h0 := (C).stepN_nonneg 0 x b
      linarith
  · exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_wf_stationary_exists (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    ∃ π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ,
      (∀ a, 0 ≤ π a) ∧ ∑ a, π a = 1 ∧
        ∀ b, ∑ a, π a*forcedCountKernel M c u a b = π b := by
  let x : Rhone.MarkovChain.AlleleCounts M 4 :=
    Rhone.MarkovChain.wfAlleleAllocationCounts M 4 (fun _ => 0)
  let avg := ldCesaro M hM c u hc0 hc1 hu0.le hu1.le x
  have hd (n : ℕ) := ld_cesaro_distribution M hM c u hc0 hc1 hu0.le hu1.le x n
  have hbox (n : ℕ) : avg n ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) := by
    constructor
    · exact (hd n).1
    · intro b
      calc
        avg n b ≤ ∑ a, avg n a := single_le_sum (fun a _ => (hd n).1 a) (mem_univ b)
        _ = 1 := (hd n).2
  obtain ⟨π, hπ, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hbox
  have hcoord (a : Rhone.MarkovChain.AlleleCounts M 4) :
      Tendsto (fun n => avg (φ n) a) atTop (𝓝 (π a)) :=
    (tendsto_pi_nhds.mp hlim) a
  have hsum : Tendsto (fun n => ∑ a, avg (φ n) a) atTop (𝓝 (∑ a, π a)) :=
    tendsto_finsetSum _ fun a _ => hcoord a
  have hnorm : ∑ a, π a = 1 := by
    have hs1 : Tendsto (fun n => ∑ a, avg (φ n) a) atTop (𝓝 (1 : ℝ)) := by
      exact tendsto_const_nhds.congr (fun n => (hd (φ n)).2.symm)
    exact tendsto_nhds_unique hsum hs1
  refine ⟨π, hπ.1, hnorm, ?_⟩
  intro b
  have hleft : Tendsto (fun n => ∑ a, avg (φ n) a*forcedCountKernel M c u a b)
      atTop (𝓝 (∑ a, π a*forcedCountKernel M c u a b)) :=
    tendsto_finsetSum _ fun a _ => (hcoord a).mul_const _
  have hz := (ld_cesaro_discrepancy_limit M hM c u hc0 hc1 hu0.le hu1.le x b).comp
    hφ.tendsto_atTop
  have hdiff := hleft.sub (hcoord b)
  have heq : (∑ a, π a*forcedCountKernel M c u a b)-π b = 0 :=
    tendsto_nhds_unique hdiff hz
  exact sub_eq_zero.mp heq

end Rhone.MarkovChain.WFAllocationLD
