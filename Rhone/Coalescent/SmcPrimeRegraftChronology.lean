/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftCover
public import Rhone.Coalescent.SmcPrimeRegraftCladePartitions

/-!
# Regrafting preserves chronological extant sample clade partitions

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_chronology {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ)
    (hT : TreeNormalized T) (hc : TreeChronology T)
    (ht : 0 ≤ t) (hta : t ≤ a)
    (hs : s ∈ timeClades T t) (hs0 : s ≠ ∅) (hs1 : s ≠ Finset.univ)
    (ha : target ∈ timeClades T a) : TreeChronology (regraft T s target t a) := by
  classical
  let U := regraft T s target t a
  have hcover : TreeTemporalCover U := regraft_temporal_cover T s target t a
    hT hc ht hta hs hs0 hs1 ha
  have htarget : target ≠ ∅ := (hc.1 a (ht.trans hta)).1 target ha
  have hcutroot : t ≤ rootHeight T := by
    by_contra hn
    have hr : rootHeight T ≤ t := (lt_of_not_ge hn).le
    simp only [timeClades, hr, ↓reduceIte, Finset.mem_singleton] at hs
    exact hs1 hs
  have hproper (b : Branch N) (hp : 0 < branchLength b) :
      b.1.Nonempty ∧ b.1 ≠ Finset.univ := by
    by_cases hb : b.1 = ∅ ∨ b.1 = Finset.univ
    · simp [branchLength, hb] at hp
    · exact ⟨Finset.nonempty_iff_ne_empty.mpr (not_or.mp hb).1, (not_or.mp hb).2⟩
  have hactiveform (q : ℝ) (i : Fin U.1) (hi : i ∈ activeBranches U q) :
      RegraftCladeAt T s target t a q (U.2 i).1 :=
    regraft_active_clade_form T s target t a q hT hcutroot hta i hi
  have hactiveproper (q : ℝ) (i : Fin U.1) (hi : i ∈ activeBranches U q) :
      (U.2 i).1.Nonempty ∧ (U.2 i).1 ≠ Finset.univ := by
    simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hproper _ hi.1
  have hformmem (q : ℝ) (hq : 0 ≤ q) (hqr : q < rootHeight U)
      (c : Finset (Fin N)) (hcf : RegraftCladeAt T s target t a q c) (hc0 : c.Nonempty) :
      c ∈ timeClades U q := by
    have hc1 : c ≠ Finset.univ := by
      intro he
      obtain ⟨j, hj⟩ := hcover q hq hqr
      have hfj := hactiveform q j hj
      obtain ⟨hjd0, hjd1⟩ := hactiveproper q j hj
      have hjdc : (U.2 j).1 ≠ c := by simpa only [he] using hjd1
      have hdis := regraft_clade_at_disjoint T hc s target t a q ht hta ha hq
        (U.2 j).1 c hfj hcf hjdc
      obtain ⟨i, hi⟩ := hjd0
      exact Finset.disjoint_left.mp hdis hi (by simp [he])
    obtain ⟨j, hj, hje⟩ := regraft_clade_at_active T s target t a q c htarget
      (Finset.nonempty_iff_ne_empty.mp hc0) hc1 hcf
    simp only [timeClades, not_le.mpr hqr, ↓reduceIte, Finset.mem_image]
    exact ⟨j, hj, hje⟩
  have hrootnonempty : (Finset.univ : Finset (Fin N)).Nonempty := by
    obtain ⟨i, _⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    exact ⟨i, Finset.mem_univ _⟩
  change TreeChronology U
  constructor
  · intro q hq
    by_cases hr : rootHeight U ≤ q
    · simp only [timeClades, hr, ↓reduceIte, Finset.mem_singleton]
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        simpa only [hc] using Finset.nonempty_iff_ne_empty.mp hrootnonempty
      · intro i
        exact ⟨Finset.univ, rfl, Finset.mem_univ _⟩
      · intro c hc d hd hcd
        exact False.elim (hcd (hc.trans hd.symm))
    · have hqr : q < rootHeight U := lt_of_not_ge hr
      refine ⟨?_, ?_, ?_⟩
      · intro c hcq
        simp only [timeClades, hr, ↓reduceIte, Finset.mem_image] at hcq
        obtain ⟨i, hi, rfl⟩ := hcq
        exact Finset.nonempty_iff_ne_empty.mp (hactiveproper q i hi).1
      · intro i
        obtain ⟨c, hcf, hic⟩ := regraft_clade_at_cover T hc s target t a q ht hta ha hq i
        exact ⟨c, hformmem q hq hqr c hcf ⟨i, hic⟩, hic⟩
      · intro c hcq d hdq hcd
        simp only [timeClades, hr, ↓reduceIte, Finset.mem_image] at hcq hdq
        obtain ⟨i, hi, rfl⟩ := hcq
        obtain ⟨j, hj, rfl⟩ := hdq
        exact regraft_clade_at_disjoint T hc s target t a q ht hta ha hq
          _ _ (hactiveform q i hi) (hactiveform q j hj) hcd
  · intro q r hq hqr c hcq
    by_cases hr : rootHeight U ≤ r
    · refine ⟨Finset.univ, ?_, Finset.subset_univ _⟩
      simp [timeClades, hr]
    · have hrroot : r < rootHeight U := lt_of_not_ge hr
      have hqroot : q < rootHeight U := hqr.trans_lt hrroot
      simp only [timeClades, not_le.mpr hqroot, ↓reduceIte, Finset.mem_image] at hcq
      obtain ⟨i, hi, rfl⟩ := hcq
      obtain ⟨d, hdf, hcd⟩ := regraft_clade_at_refines T hc s target t a q r ht hta hs ha
        hq hqr _ (hactiveform q i hi)
      have hd0 : d.Nonempty := by
        obtain ⟨j, hj⟩ := (hactiveproper q i hi).1
        exact ⟨j, hcd hj⟩
      exact ⟨d, hformmem r (hq.trans hqr) hrroot d hdf hd0, hcd⟩

end Rhone.Coalescent.SmcPrime
