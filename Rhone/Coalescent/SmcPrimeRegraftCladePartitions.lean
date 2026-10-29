/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftCladeRealization

/-!
# Chronological partitions of the regraft clade forms

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_clade_at_cover {N : ℕ} (T : Tree N) (hc : TreeChronology T)
    (s target : Finset (Fin N)) (t a q : ℝ)
    (ht : 0 ≤ t) (hta : t ≤ a) (ha : target ∈ timeClades T a)
    (hq : 0 ≤ q) (i : Fin N) :
    ∃ c, RegraftCladeAt T s target t a q c ∧ i ∈ c := by
  classical
  by_cases hqt : q < t
  · obtain ⟨c, hcq, hic⟩ := (hc.1 q hq).2.1 i
    exact ⟨c, Or.inl ⟨hqt, hcq⟩, hic⟩
  · have htq : t ≤ q := le_of_not_gt hqt
    by_cases hqa : q < a
    · by_cases his : i ∈ s
      · exact ⟨s, Or.inr (Or.inl ⟨htq, hqa, Or.inl rfl⟩), his⟩
      · obtain ⟨c, hcq, hic⟩ := (hc.1 q hq).2.1 i
        exact ⟨c \ s, Or.inr (Or.inl ⟨htq, hqa, Or.inr ⟨c, hcq, rfl⟩⟩),
          Finset.mem_sdiff.mpr ⟨hic, his⟩⟩
    · have haq : a ≤ q := le_of_not_gt hqa
      obtain ⟨c, hcq, hic⟩ := chronology_regraft_clades_cover T hc s target a q
        (ht.trans hta) haq ha i
      exact ⟨regraftClade s target c, Or.inr (Or.inr ⟨haq, c, hcq, rfl⟩), hic⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_clade_at_disjoint {N : ℕ} (T : Tree N) (hc : TreeChronology T)
    (s target : Finset (Fin N)) (t a q : ℝ)
    (ht : 0 ≤ t) (hta : t ≤ a) (ha : target ∈ timeClades T a) (hq : 0 ≤ q)
    (c d : Finset (Fin N)) (hcf : RegraftCladeAt T s target t a q c)
    (hdf : RegraftCladeAt T s target t a q d) (hcd : c ≠ d) : Disjoint c d := by
  classical
  rcases hcf with ⟨hqt, hcq⟩ | ⟨htq, hqa, hcf⟩ | ⟨haq, e, heq, hce⟩
  · rcases hdf with ⟨_, hdq⟩ | ⟨htq, _, _⟩ | ⟨haq, _⟩
    · exact (hc.1 q hq).2.2 c hcq d hdq hcd
    · linarith
    · linarith
  · rcases hdf with ⟨hqt, _⟩ | ⟨_, _, hdf⟩ | ⟨haq, _⟩
    · linarith
    · rcases hcf with rfl | ⟨e, heq, rfl⟩ <;>
        rcases hdf with rfl | ⟨f, hfq, rfl⟩
      · exact False.elim (hcd rfl)
      · apply Finset.disjoint_left.mpr
        intro i his hid
        exact (Finset.mem_sdiff.mp hid).2 his
      · apply Finset.disjoint_left.mpr
        intro i hic his
        exact (Finset.mem_sdiff.mp hic).2 his
      · have hef : e ≠ f := by intro he; subst f; exact hcd rfl
        have hdis := (hc.1 q hq).2.2 e heq f hfq hef
        apply Finset.disjoint_left.mpr
        intro i hic hid
        exact Finset.disjoint_left.mp hdis (Finset.mem_sdiff.mp hic).1
          (Finset.mem_sdiff.mp hid).1
    · linarith
  · rcases hdf with ⟨hqt, _⟩ | ⟨_, hqa, _⟩ | ⟨_, f, hfq, hdf⟩
    · linarith
    · linarith
    · subst c d
      have hef : e ≠ f := by intro he; subst f; exact hcd rfl
      exact chronology_regraft_clades_disjoint T hc s target a q (ht.trans hta) haq
        ha e f heq hfq hef

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_clade_at_refines {N : ℕ} (T : Tree N) (hc : TreeChronology T)
    (s target : Finset (Fin N)) (t a q r : ℝ)
    (ht : 0 ≤ t) (hta : t ≤ a) (hs : s ∈ timeClades T t)
    (ha : target ∈ timeClades T a) (hq : 0 ≤ q) (hqr : q ≤ r)
    (c : Finset (Fin N)) (hcf : RegraftCladeAt T s target t a q c) :
    ∃ d, RegraftCladeAt T s target t a r d ∧ c ⊆ d := by
  classical
  have hsfuture (har : a ≤ r) :
      ∃ d ∈ timeClades T r, s ⊆ regraftClade s target d := by
    obtain ⟨d, hdr, htd⟩ := hc.2 a r (ht.trans hta) har target ha
    have hint : (d ∩ target).Nonempty := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr ((hc.1 a (ht.trans hta)).1 target ha)
      exact ⟨i, Finset.mem_inter.mpr ⟨htd hi, hi⟩⟩
    refine ⟨d, hdr, ?_⟩
    intro i his
    change i ∈ (d \ s) ∪ if (d ∩ target).Nonempty then s else ∅
    exact Finset.mem_union_right _ (by simpa only [hint, ↓reduceIte] using his)
  have hdiffsubset (d : Finset (Fin N)) : d \ s ⊆ regraftClade s target d := by
    intro i hi
    exact Finset.mem_union_left _ hi
  rcases hcf with ⟨hqt, hcq⟩ | ⟨htq, hqa, hcf⟩ | ⟨haq, e, heq, hce⟩
  · by_cases hrt : r < t
    · obtain ⟨d, hdr, hcd⟩ := hc.2 q r hq hqr c hcq
      exact ⟨d, Or.inl ⟨hrt, hdr⟩, hcd⟩
    · have htr : t ≤ r := le_of_not_gt hrt
      by_cases hra : r < a
      · by_cases hcs : (c ∩ s).Nonempty
        · have hcss := chronology_clade_subset_of_intersection T hc q t hq hqt.le c s hcq hs hcs
          exact ⟨s, Or.inr (Or.inl ⟨htr, hra, Or.inl rfl⟩), hcss⟩
        · obtain ⟨d, hdr, hcd⟩ := hc.2 q r hq hqr c hcq
          refine ⟨d \ s, Or.inr (Or.inl ⟨htr, hra, Or.inr ⟨d, hdr, rfl⟩⟩), ?_⟩
          intro i hic
          refine Finset.mem_sdiff.mpr ⟨hcd hic, ?_⟩
          intro his
          exact hcs ⟨i, Finset.mem_inter.mpr ⟨hic, his⟩⟩
      · have har : a ≤ r := le_of_not_gt hra
        by_cases hcs : (c ∩ s).Nonempty
        · have hcss := chronology_clade_subset_of_intersection T hc q t hq hqt.le c s hcq hs hcs
          obtain ⟨d, hdr, hsd⟩ := hsfuture har
          exact ⟨regraftClade s target d, Or.inr (Or.inr ⟨har, d, hdr, rfl⟩), hcss.trans hsd⟩
        · obtain ⟨d, hdr, hcd⟩ := hc.2 q r hq hqr c hcq
          refine ⟨regraftClade s target d, Or.inr (Or.inr ⟨har, d, hdr, rfl⟩), ?_⟩
          intro i hic
          apply hdiffsubset d
          refine Finset.mem_sdiff.mpr ⟨hcd hic, ?_⟩
          intro his
          exact hcs ⟨i, Finset.mem_inter.mpr ⟨hic, his⟩⟩
  · have htr : t ≤ r := htq.trans hqr
    by_cases hra : r < a
    · rcases hcf with hcs | ⟨e, heq, rfl⟩
      · subst c
        exact ⟨s, Or.inr (Or.inl ⟨htr, hra, Or.inl rfl⟩), Finset.Subset.refl _⟩
      · obtain ⟨d, hdr, hed⟩ := hc.2 q r hq hqr e heq
        exact ⟨d \ s, Or.inr (Or.inl ⟨htr, hra, Or.inr ⟨d, hdr, rfl⟩⟩),
          Finset.sdiff_subset_sdiff_left s hed⟩
    · have har : a ≤ r := le_of_not_gt hra
      rcases hcf with hcs | ⟨e, heq, rfl⟩
      · subst c
        obtain ⟨d, hdr, hsd⟩ := hsfuture har
        exact ⟨regraftClade s target d, Or.inr (Or.inr ⟨har, d, hdr, rfl⟩), hsd⟩
      · obtain ⟨d, hdr, hed⟩ := hc.2 q r hq hqr e heq
        exact ⟨regraftClade s target d, Or.inr (Or.inr ⟨har, d, hdr, rfl⟩),
          (Finset.sdiff_subset_sdiff_left s hed).trans (hdiffsubset d)⟩
  · subst c
    obtain ⟨d, hdr, hed⟩ := hc.2 q r hq hqr e heq
    exact ⟨regraftClade s target d, Or.inr (Or.inr ⟨haq.trans hqr, d, hdr, rfl⟩),
      regraft_clade_mono s target e d hed⟩

end Rhone.Coalescent.SmcPrime
