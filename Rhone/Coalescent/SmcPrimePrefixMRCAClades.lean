/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTreeMRCAClades
public import Rhone.Coalescent.SmcPrimeOneSplitExtraction

/-! # Finite observed MRCA from exact chronological tree clades -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem treePairMRCA_eq_prefix_of_timeClades (N K : ℕ) (ω : EventPath) (q : GenomicProbe)
    (T : Tree N) (hnorm : TreeNormalized T) (hnonneg : TreeNonnegative T)
    (hchron : TreeChronology T) (hzero : (ω 0).1.1 = 0)
    (htimes : ∀ k ≤ K, 0 ≤ (ω k).1.1)
    (hstrict : ∀ k < K, (ω k).1.1 < (ω (k + 1)).1.1)
    (hroot : rootHeight T ≤ (ω K).1.1)
    (hcomplete : ∀ i j, ancestorLabel N ω q i K = ancestorLabel N ω q j K)
    (hclades : ∀ k < K, ∀ y, (ω k).1.1 ≤ y → y < (ω (k + 1)).1.1 →
      timeClades T y = Finset.univ.image (fun j =>
        extractionClade (fun a => ancestorLabel N ω q a k) (ancestorLabel N ω q j k)))
    (i j : Fin N) :
    treePairMRCA T i j = prefixGenealogyObservation N K ω q i j := by
  classical
  apply le_antisymm
  · unfold prefixGenealogyObservation
    apply le_iInf
    intro k
    by_cases he : ancestorLabel N ω q i k.val = ancestorLabel N ω q j k.val
    · rw [ite_eq_left he]
      apply (treePairMRCA_le_iff_timeClades T hnorm hnonneg hchron _
        (htimes k.val (by have := k.isLt; omega)) i j).mpr
      by_cases hk : k.val < K
      · rw [hclades k.val hk _ le_rfl (hstrict k.val hk)]
        refine ⟨extractionClade (fun a => ancestorLabel N ω q a k.val)
          (ancestorLabel N ω q i k.val), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
          ?_, ?_⟩
        · simp [extractionClade]
        · simp [extractionClade, he]
      · have hk' : k.val = K := by have := k.isLt; omega
        rw [hk']
        exact ⟨Finset.univ, by simp [timeClades, hroot], by simp⟩
    · rw [ite_eq_right he]
      exact le_top
  · let y := (treePairMRCA T i j).toReal
    have hfinite := treePairMRCA_ne_top T i j
    have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
    have hy : ENNReal.ofReal y = treePairMRCA T i j := ENNReal.ofReal_toReal hfinite
    rw [← hy]
    by_cases hlast : (ω K).1.1 ≤ y
    · have hle : prefixGenealogyObservation N K ω q i j ≤ ENNReal.ofReal (ω K).1.1 := by
        apply iInf_le_of_le (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1))
        change (if ancestorLabel N ω q i K = ancestorLabel N ω q j K
          then ENNReal.ofReal (ω K).1.1 else ⊤) ≤ _
        rw [ite_eq_left (hcomplete i j)]
      exact hle.trans (ENNReal.ofReal_le_ofReal hlast)
    · have hex : ∃ m, m ≤ K ∧ y < (ω m).1.1 := ⟨K, le_rfl, lt_of_not_ge hlast⟩
      let m := Nat.find hex
      have hm := Nat.find_spec hex
      change m ≤ K ∧ y < (ω m).1.1 at hm
      have hm0 : 0 < m := by
        by_contra hz
        have hmzero : m = 0 := by omega
        rw [hmzero, hzero] at hm
        exact (not_lt_of_ge hy0) hm.2
      have hlow : (ω (m - 1)).1.1 ≤ y := by
        have hmin := Nat.find_min hex (show m - 1 < m by omega)
        change ¬ (m - 1 ≤ K ∧ y < (ω (m - 1)).1.1) at hmin
        exact le_of_not_gt (fun he => hmin ⟨by omega, he⟩)
      have hupp : y < (ω (m - 1 + 1)).1.1 := by
        simpa only [Nat.sub_add_cancel hm0] using hm.2
      have hshared := (treePairMRCA_le_iff_timeClades T hnorm hnonneg hchron y hy0 i j).mp
        (le_of_eq hy.symm)
      rw [hclades (m - 1) (by omega) y hlow hupp] at hshared
      obtain ⟨c, hc, hi, hj⟩ := hshared
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hc
      rw [← ha] at hi hj
      have he : ancestorLabel N ω q i (m - 1) = ancestorLabel N ω q j (m - 1) :=
        (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
      have hle : prefixGenealogyObservation N K ω q i j ≤ ENNReal.ofReal (ω (m - 1)).1.1 := by
        apply iInf_le_of_le (⟨m - 1, by omega⟩ : Fin (K + 1))
        change (if ancestorLabel N ω q i (m - 1) = ancestorLabel N ω q j (m - 1)
          then ENNReal.ofReal (ω (m - 1)).1.1 else ⊤) ≤ _
        rw [ite_eq_left he]
      exact hle.trans (ENNReal.ofReal_le_ofReal hlow)

end Rhone.Coalescent.SmcPrime
