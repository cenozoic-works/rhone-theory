/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.MarginalLumping.LengthB

/-! # The marginal partition as a process: the one-step law, and why it is not a lumping -/

@[expose] public section

namespace Rhone.Coalescent.MarginalLumping

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory ProbabilityTheory

variable {n KA KB : ℕ} {ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem sum_transS_partA_eq (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB} (hw : WF s.st.1)
    (hd : 0 < dtotArg ρ s.st.1) (f : Finset (Finset (Fin n)) → ℝ) :
    (∑ t' : TS n KA KB, transS (0 : ℝ) 0 ρ πA πB s t' * f (partA t'.st.1))
      = f (partA s.st.1)
        + (∑ S ∈ partA s.st.1, ∑ T ∈ (partA s.st.1).erase S,
            (f (mergeP (partA s.st.1) S T) - f (partA s.st.1))) / dtotArg ρ s.st.1 := by
  have hdot : 0 < dtot (0 : ℝ) 0 ρ s.st.1 := by
    rw [dtot_zero_eq_dtotArg]
    exact hd
  have hstep : stepT (0 : ℝ) 0 ρ πA πB
      (fun t' : TSt n KA KB => f (partA t'.1)) s.st
      = stepArg ρ (fun M => f (partA M)) s.st.1 := by
    rw [← stepU_zero_eq_stepArg]
    exact stepT_of_fst h.sumA h.sumB (fun L => f (partA L)) s.st
  have hdne : dtotArg ρ s.st.1 ≠ 0 := ne_of_gt hd
  have hk := kingman_generator (ρ := ρ) hw f
  rw [sum_transS_eq hdot (fun t' : TS n KA KB => f (partA t'.st.1)), hstep,
    dtot_zero_eq_dtotArg]
  field_simp
  linarith [hk]

theorem sum_transS_partB_eq (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB} (hw : WF s.st.1)
    (hd : 0 < dtotArg ρ s.st.1) (f : Finset (Finset (Fin n)) → ℝ) :
    (∑ t' : TS n KA KB, transS (0 : ℝ) 0 ρ πA πB s t' * f (partB t'.st.1))
      = f (partB s.st.1)
        + (∑ S ∈ partB s.st.1, ∑ T ∈ (partB s.st.1).erase S,
            (f (mergeP (partB s.st.1) S T) - f (partB s.st.1))) / dtotArg ρ s.st.1 := by
  have hdot : 0 < dtot (0 : ℝ) 0 ρ s.st.1 := by
    rw [dtot_zero_eq_dtotArg]
    exact hd
  have hstep : stepT (0 : ℝ) 0 ρ πA πB
      (fun t' : TSt n KA KB => f (partB t'.1)) s.st
      = stepArg ρ (fun M => f (partB M)) s.st.1 := by
    rw [← stepU_zero_eq_stepArg]
    exact stepT_of_fst h.sumA h.sumB (fun L => f (partB L)) s.st
  have hdne : dtotArg ρ s.st.1 ≠ 0 := ne_of_gt hd
  have hk := kingman_generator_B (ρ := ρ) hw f
  rw [sum_transS_eq hdot (fun t' : TS n KA KB => f (partB t'.st.1)), hstep,
    dtot_zero_eq_dtotArg]
  field_simp
  linarith [hk]

theorem sum_transS_card_partA (h : Adm (0 : ℝ) 0 ρ πA πB) {s : TS n KA KB} (hw : WF s.st.1)
    (hd : 0 < dtotArg ρ s.st.1) :
    (∑ t' : TS n KA KB, transS (0 : ℝ) 0 ρ πA πB s t' * ((partA t'.st.1).card : ℝ))
      = ((partA s.st.1).card : ℝ)
        - (((partA s.st.1).card * ((partA s.st.1).card - 1) : ℕ) : ℝ) / dtotArg ρ s.st.1 := by
  have hmain := sum_transS_partA_eq h hw hd fun P => (P.card : ℝ)
  have hinner : ∀ S ∈ partA s.st.1, ∀ T ∈ (partA s.st.1).erase S,
      (((mergeP (partA s.st.1) S T).card : ℝ) - ((partA s.st.1).card : ℝ)) = -1 := by
    intro S hS T hT
    have hc := card_mergeP_partA hw hS hT
    have hcast : ((mergeP (partA s.st.1) S T).card : ℝ) + 1 = ((partA s.st.1).card : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hc
    linarith
  rw [Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl (hinner S hS),
    sum_pairs_const] at hmain
  rw [hmain]
  ring

def recTwo : Finset (Lin 2) := recL (fullState 2) ({0}, {0})

theorem pair_mem_fullState_two : (({0}, {0}) : Lin 2) ∈ fullState 2 :=
  mem_fullState.2 ⟨0, rfl⟩

theorem pair_mem_carC_two : (({0}, {0}) : Lin 2) ∈ carC (fullState 2) :=
  mem_carC.2 ⟨pair_mem_fullState_two, Finset.singleton_nonempty 0, Finset.singleton_nonempty 0⟩

theorem wf_recTwo : WF recTwo :=
  fullState_wf.recomb pair_mem_fullState_two (Finset.singleton_nonempty 0)
    (Finset.singleton_nonempty 0)

theorem partA_recTwo : partA recTwo = partA (fullState 2) :=
  partA_rec fullState_wf pair_mem_carC_two

theorem card_fullState_two : (fullState 2).card = 2 := by decide

theorem tt_fullState_two : tt (fullState 2) = 2 := by decide

theorem card_recTwo : recTwo.card = 3 := by decide

theorem tt_recTwo : tt recTwo = 1 := by decide

theorem dtotArg_fullState_two : dtotArg (1 : ℝ) (fullState 2) = 4 := by
  rw [dtotArg, card_fullState_two, tt_fullState_two]
  norm_num

theorem dtotArg_recTwo : dtotArg (1 : ℝ) recTwo = 7 := by
  rw [dtotArg, card_recTwo, tt_recTwo]
  norm_num

theorem partA_jump_not_lumpable (h : Adm (0 : ℝ) 0 1 πA πB) :
    ∃ s s' : TS 2 KA KB, WF s.st.1 ∧ WF s'.st.1 ∧ partA s.st.1 = partA s'.st.1
      ∧ (∑ t' : TS 2 KA KB, transS (0 : ℝ) 0 1 πA πB s t' * ((partA t'.st.1).card : ℝ))
        ≠ (∑ t' : TS 2 KA KB, transS (0 : ℝ) 0 1 πA πB s' t' * ((partA t'.st.1).card : ℝ)) := by
  refine ⟨⟨(fullState 2, noneT 2 KA, noneT 2 KB)⟩, ⟨(recTwo, noneT 2 KA, noneT 2 KB)⟩,
    fullState_wf, wf_recTwo, partA_recTwo.symm, ?_⟩
  have hk : (partA (fullState 2)).card = 2 := card_partA_fullState
  have hd1 : (0 : ℝ) < dtotArg (1 : ℝ) (fullState 2) := by
    rw [dtotArg_fullState_two]
    norm_num
  have hd2 : (0 : ℝ) < dtotArg (1 : ℝ) recTwo := by
    rw [dtotArg_recTwo]
    norm_num
  have e1 := sum_transS_card_partA (πA := πA) (πB := πB) h
    (s := (⟨(fullState 2, noneT 2 KA, noneT 2 KB)⟩ : TS 2 KA KB)) fullState_wf hd1
  have e2 := sum_transS_card_partA (πA := πA) (πB := πB) h
    (s := (⟨(recTwo, noneT 2 KA, noneT 2 KB)⟩ : TS 2 KA KB)) wf_recTwo hd2
  rw [show ((⟨(fullState 2, noneT 2 KA, noneT 2 KB)⟩ : TS 2 KA KB)).st.1 = fullState 2 from rfl,
    hk, dtotArg_fullState_two] at e1
  rw [show ((⟨(recTwo, noneT 2 KA, noneT 2 KB)⟩ : TS 2 KA KB)).st.1 = recTwo from rfl,
    partA_recTwo, hk, dtotArg_recTwo] at e2
  rw [e1, e2]
  norm_num

end Rhone.Coalescent.MarginalLumping
