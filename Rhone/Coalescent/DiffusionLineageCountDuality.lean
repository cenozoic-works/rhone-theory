/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LineageCountPath
public import Rhone.Coalescent.DiffusionBlockProcessDuality

/-!
# Moment duality of the Wright–Fisher diffusion with the Kingman lineage count at one time

Source: mohle1999, Thm 2; etheridge2011, sec. 3.2; tavare1984, sec. 7.1, eq. (7.2)–(7.5), pp.
133–134; bryant_etal2011_exact_likelihoods, sec. 2, eq. (2). -/

@[expose] public section

noncomputable section

namespace Rhone.Coalescent

open MeasureTheory Finset Diffusion MarkovChain Rhone.Combinatorics Analysis
open scoped NNReal

/-- Source: mohle1999, Thm 2; etheridge2011, sec. 3.2. -/
theorem wf_lineageCount_duality {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) (n : ℕ) (t : ℝ≥0) :
    ∫ w, w t ^ n ∂P =
      ∫ p, x ^ lineageCountAt n t p ∂((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := hP.isProbabilityMeasure
    have h2 : (fun p => x ^ lineageCountAt 0 (t : ℝ) p) =ᵐ[(partitionChain (Fin 0)).jumpHoldLaw ⊥]
        fun _ => (1 : ℝ) := by
      filter_upwards [ae_lineageCountAt_eq 0 (t : ℝ)] with p hp
      rw [hp]
      simp
    rw [integral_congr_ae h2]
    simp
  · have h := integral_pow_eq_blockChain_semigroup hP n (Fin.last n) t
    rw [Fin.val_last] at h
    rw [h]
    exact (integral_lineageCountAt n hn t.coe_nonneg (fun j => x ^ j)).symm

/-- Source: mohle1999, Thm 2; etheridge2011, sec. 3.2. -/
theorem wf_lineageCount_duality_of_le {x : ℝ} {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsWrightFisherDiffusionLaw x P) {n k : ℕ} (hk : k ≤ n) (t : ℝ≥0) :
    (∫ w, w t ^ k ∂P =
      ∫ p, x ^ lineageCountAt k t p ∂((partitionChain (Fin k)).jumpHoldLaw ⊥)) ∧
    ∑ j : Fin (n + 1), (blockChain n).semigroup t ⟨k, by omega⟩ j * x ^ (j : ℕ) =
      ∫ p, x ^ lineageCountAt k t p ∂((partitionChain (Fin k)).jumpHoldLaw ⊥) := by
  refine ⟨wf_lineageCount_duality hP k t, ?_⟩
  rw [← wf_lineageCount_duality hP k t]
  exact (integral_pow_eq_blockChain_semigroup hP n ⟨k, by omega⟩ t).symm

theorem existsUnique_wfLaw_lineageCount_duality {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃! P : Measure C(ℝ≥0, ℝ), IsWrightFisherDiffusionLaw x P ∧
      ∀ (n : ℕ) (t : ℝ≥0), ∫ w, w t ^ n ∂P =
        ∫ p, x ^ lineageCountAt n t p ∂((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  obtain ⟨P, hP⟩ := Rhone.Diffusion.wrightFisherDiffusionLaw_exists hx
  exact ⟨P, ⟨hP, wf_lineageCount_duality hP⟩, fun Q hQ => hQ.1.unique hP⟩

end Rhone.Coalescent

end
