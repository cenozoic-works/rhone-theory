/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.Watterson
public import Rhone.Coalescent.KingmanDiversityRewards

/-!
# Initial values of Kingman diversity potentials

Source: tajima1989, p. 585, eq. (6)–(7). -/

@[expose] public section
namespace Rhone.Statistics
open Coalescent Rhone.Combinatorics MarkovChain

theorem kingmanDiversityReward_bot {n : ℕ} (hn : 2 ≤ n) :
    kingmanDiversityReward n ⊥ = 2 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  simp only [kingmanDiversityReward, kingmanBlockMassMoment_bot]
  field_simp [hn0, hn1]

theorem kingmanDiversityMutationPotential_bot {n : ℕ} (hn : 2 ≤ n) :
    kingmanDiversityMutationPotential n ⊥ = 2 * (tajimaB1 n : ℝ) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  simp only [kingmanDiversityMutationPotential, kingmanBlockMassMoment_bot, tajimaB1]
  push_cast
  field_simp [hn0, hn1]
  ring

theorem kingmanDiversitySquarePotential_bot {n : ℕ} (hn : 2 ≤ n) :
    kingmanDiversitySquarePotential n ⊥ = 4 * (1 + (tajimaB2 n : ℝ)) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  simp only [kingmanDiversitySquarePotential, kingmanBlockMassMoment_bot, tajimaB2]
  push_cast
  field_simp [hn0, hn1]
  ring

end Rhone.Statistics
