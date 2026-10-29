/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeGenealogyLaw
public import Rhone.Coalescent.SmcPrimeBranchActive
public import Rhone.Coalescent.SmcPrimeProposalGeometry

/-!
# Pairwise MRCA thresholds and extant temporal sample clade partitions

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open scoped ENNReal

theorem treePairMRCA_le_iff_timeClades {N : ℕ} (T : Tree N)
    (hnorm : TreeNormalized T) (hnonneg : TreeNonnegative T)
    (hchron : TreeChronology T) (q : ℝ) (hq : 0 ≤ q) (i j : Fin N) :
    treePairMRCA T i j ≤ ENNReal.ofReal q ↔
      ∃ c ∈ timeClades T q, i ∈ c ∧ j ∈ c := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [treePairMRCA, ↓reduceIte, zero_le, true_iff]
    obtain ⟨c, hcq, hic⟩ := (hchron.1 q hq).2.1 i
    exact ⟨c, hcq, hic, hic⟩
  simp only [treePairMRCA, hij, ↓reduceIte]
  constructor
  · intro hm
    rw [inf_le_iff] at hm
    rcases hm with hroot | hbranch
    · have hr := (ENNReal.ofReal_le_ofReal_iff hq).mp hroot
      exact ⟨Finset.univ, by simp [timeClades, hr], by simp⟩
    · rw [← Finset.inf_univ_eq_iInf, Finset.inf_le_iff ENNReal.ofReal_lt_top] at hbranch
      obtain ⟨b, _, hb⟩ := hbranch
      by_cases hcond : i ∈ (T.2 b).1 ∧ j ∈ (T.2 b).1 ∧ 0 < branchLength (T.2 b)
      · rw [ite_eq_left hcond] at hb
        have hbirth := (ENNReal.ofReal_le_ofReal_iff hq).mp hb
        have hstrict : (T.2 b).2.1 < (T.2 b).2.2 := by
          by_contra hn
          have hsub : (T.2 b).2.2 - (T.2 b).2.1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hn)
          simp [branchLength, max_eq_left hsub] at hcond
        have hactive := branch_active_of_normalized_bounds T hnorm b (T.2 b).2.1
          le_rfl hstrict
        obtain ⟨c, hcq, hbc⟩ := hchron.2 (T.2 b).2.1 q (hnonneg b) hbirth
          _ (branch_active_time_clade T _ b hactive)
        exact ⟨c, hcq, hbc hcond.1, hbc hcond.2.1⟩
      · simp [hcond] at hb
  · rintro ⟨c, hcq, hic, hjc⟩
    by_cases hr : rootHeight T ≤ q
    · exact inf_le_left.trans (ENNReal.ofReal_le_ofReal hr)
    · simp only [timeClades, hr, ↓reduceIte, Finset.mem_image] at hcq
      obtain ⟨b, hb, hbc⟩ := hcq
      simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hcond : i ∈ (T.2 b).1 ∧ j ∈ (T.2 b).1 ∧ 0 < branchLength (T.2 b) :=
        ⟨hbc ▸ hic, hbc ▸ hjc, hb.1⟩
      exact inf_le_right.trans ((iInf_le_of_le b (by simp [hcond])).trans
        (ENNReal.ofReal_le_ofReal hb.2.1))

theorem treePairMRCA_ne_top {N : ℕ} (T : Tree N) (i j : Fin N) :
    treePairMRCA T i j ≠ ⊤ := by
  classical
  by_cases hij : i = j
  · simp [treePairMRCA, hij]
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
      simp only [treePairMRCA, hij, ↓reduceIte]
      exact inf_le_left)

theorem treePairMRCA_eq_of_timeClades_eq {N : ℕ} (T U : Tree N)
    (hTnorm : TreeNormalized T) (hTnonneg : TreeNonnegative T)
    (hTchron : TreeChronology T) (hUnorm : TreeNormalized U)
    (hUnonneg : TreeNonnegative U) (hUchron : TreeChronology U)
    (hclades : ∀ q, 0 ≤ q → timeClades T q = timeClades U q) (i j : Fin N) :
    treePairMRCA T i j = treePairMRCA U i j := by
  have hTU : treePairMRCA T i j ≤ treePairMRCA U i j := by
    let q := (treePairMRCA U i j).toReal
    have hq : 0 ≤ q := ENNReal.toReal_nonneg
    have hm : treePairMRCA U i j ≤ ENNReal.ofReal q := by
      rw [ENNReal.ofReal_toReal (treePairMRCA_ne_top U i j)]
    rw [treePairMRCA_le_iff_timeClades U hUnorm hUnonneg hUchron q hq i j] at hm
    rw [← hclades q hq] at hm
    have ht := (treePairMRCA_le_iff_timeClades T hTnorm hTnonneg hTchron q hq i j).mpr hm
    rwa [ENNReal.ofReal_toReal (treePairMRCA_ne_top U i j)] at ht
  have hUT : treePairMRCA U i j ≤ treePairMRCA T i j := by
    let q := (treePairMRCA T i j).toReal
    have hq : 0 ≤ q := ENNReal.toReal_nonneg
    have hm : treePairMRCA T i j ≤ ENNReal.ofReal q := by
      rw [ENNReal.ofReal_toReal (treePairMRCA_ne_top T i j)]
    rw [treePairMRCA_le_iff_timeClades T hTnorm hTnonneg hTchron q hq i j] at hm
    rw [hclades q hq] at hm
    have hu := (treePairMRCA_le_iff_timeClades U hUnorm hUnonneg hUchron q hq i j).mpr hm
    rwa [ENNReal.ofReal_toReal (treePairMRCA_ne_top T i j)] at hu
  exact le_antisymm hTU hUT
end Rhone.Coalescent.SmcPrime
