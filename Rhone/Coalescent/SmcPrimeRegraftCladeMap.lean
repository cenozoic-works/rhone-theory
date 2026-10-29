/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeChronology

/-!
# Partition geometry of the ancestral clade map of the SMC′ regraft

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
noncomputable def regraftClade {N : ℕ} (s target c : Finset (Fin N)) : Finset (Fin N) :=
  (aboveAttachment (c, 0, 0) s target 0).1

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_clade_mono {N : ℕ} (s target c d : Finset (Fin N)) (hcd : c ⊆ d) :
    regraftClade s target c ⊆ regraftClade s target d := by
  classical
  intro i hi
  change i ∈ (c \ s) ∪ if (c ∩ target).Nonempty then s else ∅ at hi
  change i ∈ (d \ s) ∪ if (d ∩ target).Nonempty then s else ∅
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨hcd (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
  · by_cases hct : (c ∩ target).Nonempty
    · have hdt : (d ∩ target).Nonempty := by
        obtain ⟨j, hj⟩ := hct
        exact ⟨j, Finset.mem_inter.mpr ⟨hcd (Finset.mem_inter.mp hj).1,
          (Finset.mem_inter.mp hj).2⟩⟩
      simp only [hct, ↓reduceIte] at hi
      exact Finset.mem_union_right _ (by simpa only [hdt, ↓reduceIte] using hi)
    · simp [hct] at hi

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem chronology_regraft_clades_cover {N : ℕ} (T : Tree N) (hc : TreeChronology T)
    (s target : Finset (Fin N)) (a q : ℝ) (ha : 0 ≤ a) (haq : a ≤ q)
    (hat : target ∈ timeClades T a) (i : Fin N) :
    ∃ c ∈ timeClades T q, i ∈ regraftClade s target c := by
  classical
  by_cases his : i ∈ s
  · have ht0 : target.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr ((hc.1 a ha).1 target hat)
    obtain ⟨j, hj⟩ := ht0
    obtain ⟨c, hcq, hjc⟩ := (hc.1 q (ha.trans haq)).2.1 j
    have hint : (c ∩ target).Nonempty := ⟨j, Finset.mem_inter.mpr ⟨hjc, hj⟩⟩
    refine ⟨c, hcq, ?_⟩
    change i ∈ (c \ s) ∪ if (c ∩ target).Nonempty then s else ∅
    exact Finset.mem_union_right _ (by simpa only [hint, ↓reduceIte] using his)
  · obtain ⟨c, hcq, hic⟩ := (hc.1 q (ha.trans haq)).2.1 i
    exact ⟨c, hcq, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hic, his⟩)⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem chronology_regraft_clades_disjoint {N : ℕ} (T : Tree N) (hc : TreeChronology T)
    (s target : Finset (Fin N)) (a q : ℝ) (ha : 0 ≤ a) (haq : a ≤ q)
    (hat : target ∈ timeClades T a) (c d : Finset (Fin N))
    (hcq : c ∈ timeClades T q) (hdq : d ∈ timeClades T q) (hcd : c ≠ d) :
    Disjoint (regraftClade s target c) (regraftClade s target d) := by
  classical
  have hdis := (hc.1 q (ha.trans haq)).2.2 c hcq d hdq hcd
  apply Finset.disjoint_left.mpr
  intro i hic hid
  change i ∈ (c \ s) ∪ if (c ∩ target).Nonempty then s else ∅ at hic
  change i ∈ (d \ s) ∪ if (d ∩ target).Nonempty then s else ∅ at hid
  by_cases his : i ∈ s
  · have hct : (c ∩ target).Nonempty := by
      by_contra hn
      simp only [hn, ↓reduceIte, Finset.union_empty, Finset.mem_sdiff] at hic
      exact hic.2 his
    have hdt : (d ∩ target).Nonempty := by
      by_contra hn
      simp only [hn, ↓reduceIte, Finset.union_empty, Finset.mem_sdiff] at hid
      exact hid.2 his
    have htc := chronology_clade_subset_of_intersection T hc a q ha haq target c hat hcq
      (by simpa only [Finset.inter_comm] using hct)
    have htd := chronology_clade_subset_of_intersection T hc a q ha haq target d hat hdq
      (by simpa only [Finset.inter_comm] using hdt)
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr ((hc.1 a ha).1 target hat)
    exact Finset.disjoint_left.mp hdis (htc hj) (htd hj)
  · have hic' : i ∈ c := by
      rcases Finset.mem_union.mp hic with hic | hic
      · exact (Finset.mem_sdiff.mp hic).1
      · split_ifs at hic <;> simp_all
    have hid' : i ∈ d := by
      rcases Finset.mem_union.mp hid with hid | hid
      · exact (Finset.mem_sdiff.mp hid).1
      · split_ifs at hid <;> simp_all
    exact Finset.disjoint_left.mp hdis hic' hid'

end Rhone.Coalescent.SmcPrime
