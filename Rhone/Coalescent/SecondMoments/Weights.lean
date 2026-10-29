/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SecondMoments.Second

/-! # The `B`-marginal clade count and its branch-length functional -/

@[expose] public section

namespace Rhone.Coalescent.SecondMoments

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def rB (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  ((t.st.1.filter fun p => p.2 ∈ F).card : ℝ)

theorem rB_nonneg (F : Finset (Finset (Fin n))) (t : TS n KA KB) : 0 ≤ rB F t :=
  Nat.cast_nonneg _

@[simp] theorem rB_of_absorbed {F : Finset (Finset (Fin n))} {t : TS n KA KB}
    (ht : t.st.1 = ∅) : rB F t = 0 := by
  rw [rB, ht, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]

theorem card_line_le_one_B {L : Finset (Lin n)} (hw : WF L) {S : Finset (Fin n)}
    (hS : S.Nonempty) : (L.filter fun p => p.2 = S).card ≤ 1 := by
  refine Finset.card_le_one.2 fun p hp q hq => ?_
  rw [Finset.mem_filter] at hp hq
  by_contra hne
  obtain ⟨k, hk⟩ := hS
  have hd := hw.disjB p hp.1 q hq.1 hne
  have hkp : k ∈ p.2 := by rw [hp.2]; exact hk
  have hkq : k ∈ q.2 := by rw [hq.2]; exact hk
  exact (Finset.disjoint_left.1 hd) hkp hkq

theorem rB_eq_sum (F : Finset (Finset (Fin n))) (t : TS n KA KB) :
    rB F t = ∑ S ∈ F, rB {S} t := by
  classical
  have hcast : ∀ G : Finset (Finset (Fin n)),
      rB G t = ∑ p ∈ t.st.1, if p.2 ∈ G then (1 : ℝ) else 0 := by
    intro G
    rw [rB, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  have hsingle : ∀ S : Finset (Fin n),
      rB ({S} : Finset (Finset (Fin n))) t = ∑ p ∈ t.st.1, if p.2 = S then (1 : ℝ) else 0 := by
    intro S
    rw [hcast]
    exact Finset.sum_congr rfl fun p _ => by simp
  rw [hcast F]
  simp only [hsingle]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq F p.2 fun _ => (1 : ℝ)]

noncomputable def holdB (θA θB ρ : ℝ) (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  rB F t / rateTotS θA θB ρ t

theorem holdB_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (F : Finset (Finset (Fin n))) (t : TS n KA KB) : 0 ≤ holdB θA θB ρ F t :=
  div_nonneg (rB_nonneg F t) (rateTotS_nonneg hθA hθB hρ t)

@[simp] theorem holdB_of_absorbed {F : Finset (Finset (Fin n))} {t : TS n KA KB}
    (ht : t.st.1 = ∅) : holdB θA θB ρ F t = 0 := by
  rw [holdB, rB_of_absorbed ht, zero_div]

noncomputable def branchLenB (θA θB ρ : ℝ) (F : Finset (Finset (Fin n)))
    (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  occAll (holdB θA θB ρ F) ω

theorem branchLenB_eq_occAll (F : Finset (Finset (Fin n))) (ω : (_ : ℕ) → TS n KA KB) :
    branchLenB θA θB ρ F ω = occAll (holdB θA θB ρ F) ω := rfl

theorem branchLen_eq_occAll (F : Finset (Finset (Fin n))) (ω : (_ : ℕ) → TS n KA KB) :
    branchLen θA θB ρ F ω = occAll (holdA θA θB ρ F) ω := rfl

end Rhone.Coalescent.SecondMoments
