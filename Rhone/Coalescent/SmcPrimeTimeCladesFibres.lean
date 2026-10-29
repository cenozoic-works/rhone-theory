/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction
public import Rhone.Coalescent.SmcPrimeRegraftChronology

/-! # Exact time partitions from indexed branch and sample-fibre realization -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime

theorem timeClades_eq_sample_fibres {N : ℕ} (hN : 0 < N) (T : Tree N)
    (hchron : TreeChronology T) (q : ℝ) (hq : 0 ≤ q) (f : Fin N → ℕ)
    (hactive : ∀ i ∈ activeBranches T q, ∃ a, (T.2 i).1 = extractionClade f a)
    (hproper : ∀ j, extractionClade f (f j) ≠ Finset.univ →
      ∃ i ∈ activeBranches T q, (T.2 i).1 = extractionClade f (f j)) :
    timeClades T q = Finset.univ.image (fun j => extractionClade f (f j)) := by
  classical
  by_cases hroot : rootHeight T ≤ q
  · have hall (j : Fin N) : extractionClade f (f j) = Finset.univ := by
      by_contra hne
      obtain ⟨i, hi, _⟩ := hproper j hne
      have hp := (Finset.mem_filter.mp hi).2
      exact (not_lt_of_ge hroot) (hp.2.2.trans_le (branch_hi_le_root T i hp.1))
    rw [show timeClades T q = {Finset.univ} by simp [timeClades, hroot]]
    ext c
    simp only [Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro hc
      exact ⟨⟨0, hN⟩, Finset.mem_univ _, (hall _).trans hc.symm⟩
    · rintro ⟨j, _, hj⟩
      exact hj.symm.trans (hall j)
  · have hclade (c : Finset (Fin N)) (hc : c ∈ timeClades T q) :
        ∃ a, c = extractionClade f a := by
      simp only [timeClades, hroot, ↓reduceIte, Finset.mem_image] at hc
      obtain ⟨i, hi, he⟩ := hc
      obtain ⟨a, ha⟩ := hactive i hi
      exact ⟨a, he.symm.trans ha⟩
    ext c
    constructor
    · intro hc
      obtain ⟨a, ha⟩ := hclade c hc
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr ((hchron.1 q hq).1 c hc)
      have hja : f j = a := by
        rw [ha] at hj
        exact (Finset.mem_filter.mp hj).2
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [hja, ← ha]⟩
    · intro hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      obtain ⟨d, hd, hjd⟩ := (hchron.1 q hq).2.1 j
      obtain ⟨a, ha⟩ := hclade d hd
      have hja : f j = a := by
        rw [ha] at hjd
        exact (Finset.mem_filter.mp hjd).2
      have he : d = c := ha.trans (by rw [← hja]; exact hj)
      rwa [← he]

end Rhone.Coalescent.SmcPrime
