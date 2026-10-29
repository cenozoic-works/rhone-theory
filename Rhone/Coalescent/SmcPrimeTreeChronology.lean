/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeAttachmentBudget
public import Rhone.Coalescent.SmcPrimeRootGeometry

/-!
# Concrete extant clade partitions and chronological coarsening

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
noncomputable def timeClades {N : ℕ} (T : Tree N) (q : ℝ) : Finset (Finset (Fin N)) := by
  classical
  exact if rootHeight T ≤ q then {Finset.univ}
    else (activeBranches T q).image (fun i => (T.2 i).1)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeChronology {N : ℕ} (T : Tree N) : Prop :=
  (∀ q, 0 ≤ q →
    (∀ c ∈ timeClades T q, c ≠ ∅) ∧
    (∀ i : Fin N, ∃ c ∈ timeClades T q, i ∈ c) ∧
    (∀ c ∈ timeClades T q, ∀ d ∈ timeClades T q, c ≠ d → Disjoint c d)) ∧
  (∀ q r, 0 ≤ q → q ≤ r → ∀ c ∈ timeClades T q,
    ∃ d ∈ timeClades T r, c ⊆ d)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tree_chronology_temporal_cover {N : ℕ} (T : Tree N)
    (hN : 0 < N) (hc : TreeChronology T) : TreeTemporalCover T := by
  classical
  intro q hq hroot
  obtain ⟨c, hcq, _⟩ := (hc.1 q hq).2.1 ⟨0, hN⟩
  simp only [timeClades, not_le.mpr hroot, ↓reduceIte, Finset.mem_image] at hcq
  obtain ⟨i, hi, _⟩ := hcq
  exact ⟨i, hi⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem chronology_clade_subset_of_intersection {N : ℕ} (T : Tree N)
    (hc : TreeChronology T) (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r)
    (c d : Finset (Fin N)) (hcq : c ∈ timeClades T q)
    (hdr : d ∈ timeClades T r) (hcd : (c ∩ d).Nonempty) : c ⊆ d := by
  classical
  obtain ⟨e, her, hce⟩ := hc.2 q r hq hqr c hcq
  have hed : e = d := by
    by_contra hne
    have hd := (hc.1 r (hq.trans hqr)).2.2 e her d hdr hne
    obtain ⟨i, hi⟩ := hcd
    have hci := (Finset.mem_inter.mp hi).1
    have hdi := (Finset.mem_inter.mp hi).2
    exact Finset.disjoint_left.mp hd (hce hci) hdi
  simpa only [hed] using hce

end Rhone.Coalescent.SmcPrime
