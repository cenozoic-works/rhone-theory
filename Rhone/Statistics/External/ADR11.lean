/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import ADR11.Identifiability.Theorem9
public import ADR11.Identifiability.Proposition3
public import ADR11.Identifiability.Corollary10
public import ADR11.Nonbinary.Proposition11
public import Rhone.Coalescent.Kingman
public import Rhone.Coalescent.KingmanChain

/-!
# Bridge to the Lean formalization of Allman, Degnan, and Rhodes (2011)

Uses `lean4-adr11` (https://github.com/vltanh/lean4-adr11, Apache-2.0, commit `2db7f81`) by The-Anh
Vu-Le.

Source: allman_degnan_rhodes2011, Thm 9, Prop. 3, Cor. 10, Prop. 11. -/

@[expose] public section

namespace Rhone.Statistics.External.ADR11

open Finset _root_.ADR11

section Bridge

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem kingmanGenerator_self_eq_neg_coalRate (F : Finset (Finset L)) :
    kingmanGenerator F F = -((Rhone.Coalescent.coalRate #(roots F) : ℚ) : ℝ) := by
  rw [kingmanGenerator_apply_self, Rhone.Coalescent.coalRate_eq_choose]
  push_cast
  rfl

theorem kingmanGenerator_eq_one_of_mem_merges {F G : Finset (Finset L)} (hF : IsForest F)
    (hG : G ∈ merges F) : kingmanGenerator F G = 1 := by
  have hne : G ≠ F := fun h => hF.self_not_mem_merges (h ▸ hG)
  rw [kingmanGenerator_apply_of_isForest]
  simp [hne, hG]

theorem sum_kingmanGenerator_merges {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G ∈ merges F, kingmanGenerator F G = ((Rhone.Coalescent.coalRate #(roots F) : ℚ) : ℝ) := by
  rw [Finset.sum_congr rfl fun G hG => kingmanGenerator_eq_one_of_mem_merges hF hG,
    Finset.sum_const, hF.card_merges, Rhone.Coalescent.coalRate_eq_choose]
  simp

theorem sum_kingmanGenerator_card_roots {F : Finset (Finset L)} (hF : IsForest F) (j : ℕ) :
    ∑ G ∈ univ.filter (fun G : Finset (Finset L) => #(roots G) = j), kingmanGenerator F G =
      (if j = #(roots F) then -((#(roots F)).choose 2 : ℝ) else 0) +
        (if j + 1 = #(roots F) then ((#(roots F)).choose 2 : ℝ) else 0) := by
  have hpt : ∀ G, kingmanGenerator F G =
      (if G = F then -((#(roots F)).choose 2 : ℝ) else 0) + (if G ∈ merges F then 1 else 0) := by
    intro G
    rw [kingmanGenerator_apply_of_isForest]
    by_cases h : G = F
    · subst h
      simp [hF.self_not_mem_merges]
    · simp [h]
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]
  congr 1
  · by_cases h : #(roots F) = j
    · simp [h]
    · simp [h, Ne.symm h]
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases h : j + 1 = #(roots F)
    · have : (univ.filter (fun G : Finset (Finset L) => #(roots G) = j)).filter
          (fun G => G ∈ merges F) = merges F := by
        ext G
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hG
        have := (hF.of_mem_merges hG).2.1
        omega
      rw [this, hF.card_merges]
      simp [h]
    · have : (univ.filter (fun G : Finset (Finset L) => #(roots G) = j)).filter
          (fun G => G ∈ merges F) = ∅ := by
        ext G
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        intro hj hG
        have := (hF.of_mem_merges hG).2.1
        omega
      rw [this]
      simp [h]

theorem sum_kingmanGenerator_card_roots_eq_blockQ {n : ℕ} {F : Finset (Finset L)}
    (hF : IsForest F) (hk : #(roots F) < n + 1) (j : Fin (n + 1)) :
    ∑ G ∈ univ.filter (fun G : Finset (Finset L) => #(roots G) = (j : ℕ)), kingmanGenerator F G =
      Rhone.Coalescent.blockQ n ⟨#(roots F), hk⟩ j := by
  rw [sum_kingmanGenerator_card_roots hF, Rhone.Coalescent.blockQ,
    Rhone.Coalescent.coalRate_eq_choose]
  have hj : (j = ⟨#(roots F), hk⟩) ↔ (j : ℕ) = #(roots F) := by
    rw [Fin.ext_iff]
  by_cases h1 : (j : ℕ) = #(roots F)
  · have h2 : ¬ ((j : ℕ) + 1 = #(roots F)) := by omega
    simp [hj.mpr h1]
  · by_cases h2 : (j : ℕ) + 1 = #(roots F)
    · simp [h1, h2, hj]
    · simp [h1, h2, hj]

end Bridge

section Headlines

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Thm 9. -/
theorem rootedSpeciesTree_identifiable (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' :=
  _root_.ADR11.theorem9 hX σ σ' hσ hσ' h

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Thm 9. -/
theorem unrootedDist_eq_iff_sameUnrootedMetricTree_of_card_four (hX : Fintype.card X = 4)
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  _root_.ADR11.theorem9_four hX σ σ' hσ hσ'

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Prop. 3. -/
theorem rootedSpeciesTree_not_identifiable_of_card_four (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' :=
  _root_.ADR11.proposition3 hX

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Cor. 10. -/
theorem rootedSpeciesTree_identifiable_of_multipleSamples (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  _root_.ADR11.corollary10 ℓ hℓ hcond σ σ' hσ hσ' h

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Prop. 11. -/
theorem rootedSpeciesTree_identifiable_nonbinary (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' :=
  _root_.ADR11.proposition11_theorem9 hX σ σ' h

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Prop. 11. -/
theorem unrootedDist_eq_iff_sameUnrootedMetricTree_of_card_four_nonbinary (hX : Fintype.card X = 4)
    (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  _root_.ADR11.proposition11_theorem9_four hX σ σ'

/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: allman_degnan_rhodes2011, Prop. 11. -/
theorem rootedSpeciesTree_identifiable_of_multipleSamples_nonbinary (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  _root_.ADR11.proposition11_corollary10 ℓ hℓ hcond σ σ' h

end Headlines

end Rhone.Statistics.External.ADR11
