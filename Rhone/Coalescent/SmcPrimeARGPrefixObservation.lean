/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGSectors

/-! # Measurable genealogy of a finite ARG prefix and its agreement with the full path -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

noncomputable def argPrefixGenealogy (N : ℕ) (h : ARGPrefix (N + 1)) : Genealogy N :=
  prefixGenealogyObservation N (N + 1) (extractionPrefixExtension N h)

theorem prefixGenealogyObservation_measurable (N K : ℕ) :
    Measurable (prefixGenealogyObservation N K) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.iInf
  intro k
  exact (ENNReal.measurable_ofReal.comp (measurable_pi_apply k.val).fst.fst).piecewise
    (measurableSet_eq_fun (ancestorLabel_measurable N q i k.val)
      (ancestorLabel_measurable N q j k.val)) measurable_const

theorem extractionPrefixExtension_measurable (N : ℕ) :
    Measurable (extractionPrefixExtension N) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k ≤ N + 1
  · simpa only [extractionPrefixExtension, dite_eq_left hk] using
      (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr hk⟩ : Finset.Iic (N + 1)))
  · simp only [extractionPrefixExtension, dite_eq_right hk]
    exact measurable_const

theorem argPrefixGenealogy_measurable (N : ℕ) : Measurable (argPrefixGenealogy N) :=
  (prefixGenealogyObservation_measurable N (N + 1)).comp (extractionPrefixExtension_measurable N)

theorem argPrefixGenealogy_prefix (N : ℕ) (ω : EventPath) :
    argPrefixGenealogy N (fun k : Finset.Iic (N + 1) => ω k.val) =
      prefixGenealogyObservation N (N + 1) ω := by
  funext q i j
  apply iInf_congr
  intro k
  have hk : k.val ≤ N + 1 := by have := k.isLt; omega
  have hp (l : ℕ) (hl : l ≤ k.val) :
      extractionPrefixExtension N (fun k : Finset.Iic (N + 1) => ω k.val) l = ω l := by
    rw [extractionPrefixExtension_prefix N _ l (hl.trans hk)]
  have hi := ancestorLabel_eq_of_prefix N
    (extractionPrefixExtension N (fun k : Finset.Iic (N + 1) => ω k.val)) ω q i k.val hp
  have hj := ancestorLabel_eq_of_prefix N
    (extractionPrefixExtension N (fun k : Finset.Iic (N + 1) => ω k.val)) ω q j k.val hp
  rw [hi, hj, hp k.val le_rfl]

theorem genealogy_eq_prefix_of_one (N : ℕ) (ω : EventPath)
    (hc : ChronologicalAncestryPath N ω) (K : ℕ) (hK : (ω K).1.2.2.1 = 1) :
    genealogyObservation N ω = prefixGenealogyObservation N K ω := by
  apply genealogyObservation_eq_prefix N K ω hc.time_monotone
  intro q i j
  obtain ⟨a, ha, _⟩ := hc.ancestorCarried q i K
  obtain ⟨b, hb, _⟩ := hc.ancestorCarried q j K
  have he : a = b := by
    apply Fin.ext
    have ha' := a.isLt
    have hb' := b.isLt
    omega
  exact ha.symm.trans (he ▸ hb)

end Rhone.Coalescent.SmcPrime
