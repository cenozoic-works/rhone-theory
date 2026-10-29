/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogy

/-! # Pairwise genealogy observations stop changing after completed sample ancestry -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def prefixGenealogyObservation (N K : ℕ) (ω : EventPath) : Genealogy N :=
  fun q i j => ⨅ k : Fin (K + 1),
    if ancestorLabel N ω q i k.val = ancestorLabel N ω q j k.val
    then ENNReal.ofReal (ω k.val).1.1 else ⊤

theorem genealogyObservation_eq_prefix (N K : ℕ) (ω : EventPath)
    (ht : Monotone (fun k => (ω k).1.1))
    (hc : ∀ q i j, ancestorLabel N ω q i K = ancestorLabel N ω q j K) :
    genealogyObservation N ω = prefixGenealogyObservation N K ω := by
  funext q i j
  apply le_antisymm
  · apply le_iInf
    intro k
    exact iInf_le_of_le k.val le_rfl
  · apply le_iInf
    intro k
    by_cases hk : k ≤ K
    · exact iInf_le_of_le (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1)) le_rfl
    · by_cases he : ancestorLabel N ω q i k = ancestorLabel N ω q j k
      · simp only [he, ite_eq_left]
        have hbound : prefixGenealogyObservation N K ω q i j ≤
            ENNReal.ofReal (ω K).1.1 := by
          unfold prefixGenealogyObservation
          exact iInf_le_of_le (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1))
            (by simp [hc q i j])
        exact hbound.trans (ENNReal.ofReal_le_ofReal (ht (Nat.le_of_lt (Nat.lt_of_not_ge hk))))
      · simp [he]

end Rhone.Coalescent.IntervalProcess
