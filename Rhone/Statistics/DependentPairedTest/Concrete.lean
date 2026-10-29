/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Coupling

/-! # Exact planning-budget consequences -/

@[expose] public section

namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem gap_fifteen_sixtyone_budget :
    (160 : ℝ) ≤ 2700 * (15 / 61) ^ 2 := by norm_num

theorem gap_three_threehundredtwenty_budget :
    (160 : ℝ) ≤ 1821000 * (3 / 320) ^ 2 := by norm_num

theorem coupling_power_2700 (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) {f : X → ℝ} {g : Y → ℝ}
    (hf : Binary f) (hg : Binary g) (hgap : rejection P f - rejection Q g = 15 / 61) :
    (19 : ℝ) / 20 ≤ probability (iid R 2700)
      (fun z => Rejects (fun i => f (z i).1 - g (z i).2)) := by
  apply coupling_worst_discordance_power R P Q h hf hg
  rw [hgap]
  exact gap_fifteen_sixtyone_budget

theorem coupling_power_1821000 (R : Law (X × Y)) (P : Law X) (Q : Law Y)
    (h : IsCoupling R P Q) {f : X → ℝ} {g : Y → ℝ}
    (hf : Binary f) (hg : Binary g) (hgap : rejection P f - rejection Q g = 3 / 320) :
    (19 : ℝ) / 20 ≤ probability (iid R 1821000)
      (fun z => Rejects (fun i => f (z i).1 - g (z i).2)) := by
  apply coupling_worst_discordance_power R P Q h hf hg
  rw [hgap]
  exact gap_three_threehundredtwenty_budget

end Rhone.Statistics.DependentPairedTest
