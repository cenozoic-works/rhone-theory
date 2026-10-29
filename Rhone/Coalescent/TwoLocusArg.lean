/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusChain
public import Rhone.Coalescent.FullARGTwoSampleChain

/-!
# Two-sample ancestral recombination graph chain and its two-locus outcome value

Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/

@[expose] public section
namespace Rhone.Coalescent
open Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy

def twoSampleStart : ASt 2 := ({({0}, {0}), ({1}, {1})} : Finset (Lin 2))

def twoSampleSet : Finset (Lin 2) := {({0}, {0}), ({1}, {1})}

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
noncomputable def argOutcome (ρ : ℝ) (L : ASt 2) : ℝ :=
  IntervalProcess.twoLocusOutcome ρ (na L) (nb L) (tt L)

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
noncomputable def argOutcomeSet (ρ : ℝ) (L : Finset (Lin 2)) : ℝ :=
  IntervalProcess.twoLocusOutcome ρ (na L) (nb L) (tt L)

theorem sum_stepU_indicator_mul {n : ℕ} (θA θB ρ : ℝ) (f : Finset (Lin n) → ℝ)
    (L : Finset (Lin n)) :
    (∑ M : Finset (Lin n), stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L * f M) =
      stepU θA θB ρ f L := by
  have h : ∀ M : Finset (Lin n),
      stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L * f M =
        stepU θA θB ρ (fun M' => if M' = M then f M else 0) L := by
    intro M
    simp only [stepU, add_mul, Finset.sum_mul, mul_assoc, ite_mul, one_mul, zero_mul]
  have hf : (fun M' : Finset (Lin n) => ∑ M : Finset (Lin n), if M' = M then f M else 0) =
      f := by
    funext M'
    rw [Finset.sum_ite_eq Finset.univ M' f, ite_eq_left (Finset.mem_univ M')]
  rw [Finset.sum_congr rfl fun M _ => h M, stepU_finsetSum, hf]

theorem twoSampleStart_coalL :
    ∀ p ∈ twoSampleSet, ∀ q ∈ twoSampleSet.erase p,
      na (coalL twoSampleSet p q) = 1 ∧ nb (coalL twoSampleSet p q) = 1 := by
  decide

theorem twoSampleStart_recL :
    ∀ p ∈ carC twoSampleSet,
      na (recL twoSampleSet p) = 2 ∧ nb (recL twoSampleSet p) = 2 ∧
        tt (recL twoSampleSet p) = 1 := by
  decide

theorem twoSampleStart_card :
    twoSampleSet.card = 2 ∧ tt twoSampleSet = 2 := by
  decide

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem sum_trans_mul_argOutcomeSet_start (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∑ M : Finset (Lin 2), trans 0 0 ρ twoSampleSet M * argOutcomeSet ρ M) =
      IntervalProcess.twoLocusValue ρ 2 := by
  have hD : 0 < ρ ^ 2 + 13 * ρ + 18 := by positivity
  have hcard := twoSampleStart_card.1
  have htt : (carC twoSampleSet).card = 2 := twoSampleStart_card.2
  have hd : dtot 0 0 ρ twoSampleSet = 2 + 2 * ρ := by
    rw [dtot, hcard, tt, htt]
    norm_num
    ring
  have hdpos : 0 < dtot 0 0 ρ twoSampleSet := by
    rw [hd]
    positivity
  have hf1 : ∀ p ∈ twoSampleSet,
      ∀ q ∈ twoSampleSet.erase p,
        argOutcomeSet ρ (coalL twoSampleSet p q) = 1 := by
    intro p hp q hq
    have h := twoSampleStart_coalL p hp q hq
    rw [argOutcomeSet, h.1, h.2]
    simp [IntervalProcess.twoLocusOutcome]
  have hf2 : ∀ p ∈ carC twoSampleSet,
      argOutcomeSet ρ (recL twoSampleSet p) = 6 / (ρ ^ 2 + 13 * ρ + 18) := by
    intro p hp
    have h := twoSampleStart_recL p hp
    rw [argOutcomeSet, h.1, h.2.1, h.2.2]
    simp [IntervalProcess.twoLocusOutcome, IntervalProcess.twoLocusValue]
  have hA : (∑ p ∈ twoSampleSet,
      ∑ q ∈ twoSampleSet.erase p,
        argOutcomeSet ρ (coalL twoSampleSet p q)) = 2 := by
    have hin : ∀ p ∈ twoSampleSet,
        (∑ q ∈ twoSampleSet.erase p,
          argOutcomeSet ρ (coalL twoSampleSet p q)) = 1 := by
      intro p hp
      rw [Finset.sum_congr rfl fun q hq => hf1 p hp q hq, Finset.sum_const,
        Finset.card_erase_of_mem hp, hcard]
      norm_num
    rw [Finset.sum_congr rfl hin, Finset.sum_const, hcard]
    norm_num
  have hB : (∑ p ∈ carC twoSampleSet,
      argOutcomeSet ρ (recL twoSampleSet p)) = 2 * (6 / (ρ ^ 2 + 13 * ρ + 18)) := by
    rw [Finset.sum_congr rfl hf2, Finset.sum_const, htt, nsmul_eq_mul]
    norm_num
  have hstep : stepU 0 0 ρ (argOutcomeSet ρ) twoSampleSet =
      2 + ρ * (2 * (6 / (ρ ^ 2 + 13 * ρ + 18))) := by
    simp only [stepU]
    rw [hA, hB]
    ring
  have hterm : ∀ M : Finset (Lin 2),
      trans 0 0 ρ twoSampleSet M * argOutcomeSet ρ M =
        stepU 0 0 ρ (fun M' => if M' = M then 1 else 0) twoSampleSet * argOutcomeSet ρ M /
          dtot 0 0 ρ twoSampleSet := by
    intro M
    rw [trans_of_pos M hdpos]
    ring
  rw [Finset.sum_congr rfl fun M _ => hterm M, ← Finset.sum_div, sum_stepU_indicator_mul,
    hstep, hd]
  change _ = (ρ + 18) / (ρ ^ 2 + 13 * ρ + 18)
  have h1 : (2 : ℝ) + 2 * ρ ≠ 0 := by positivity
  field_simp
  ring

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem argChain_expect_argOutcome_start (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (argChain 0 0 ρ le_rfl le_rfl hρ).expect (argOutcome ρ) twoSampleStart =
      IntervalProcess.twoLocusValue ρ 2 :=
  sum_trans_mul_argOutcomeSet_start ρ hρ

end Rhone.Coalescent
