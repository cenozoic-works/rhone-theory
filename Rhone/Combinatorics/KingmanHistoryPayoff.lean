/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanColoredMerges
/-! # Payoffs of ranked Kingman forest histories and root-split purity of clades -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
noncomputable def historyPayoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (f : Finset (Finset L) → ℝ) : ℝ :=
  ∑ h : RankedForestHistory F t, historyMass F t h * f (historyEnd F t h)
theorem history_payoff_succ {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (f : Finset (Finset L) → ℝ) :
    historyPayoff F (t + 1) f =
      ∑ G ∈ ADR11.merges F, ADR11.jumpMatrix F G * historyPayoff G t f := by
  unfold historyPayoff
  change (∑ h : (Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t),
      (ADR11.jumpMatrix F h.1.1 * historyMass h.1.1 t h.2) *
        f (historyEnd h.1.1 t h.2)) = _
  rw [Fintype.sum_sigma]
  simp_rw [mul_assoc, ← mul_sum]
  exact sum_coe_sort (ADR11.merges F) (fun G => ADR11.jumpMatrix F G *
    ∑ h : RankedForestHistory G t, historyMass G t h * f (historyEnd G t h))
theorem root_split_clade_purity {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (A : Finset L)
    (hsplit : ADR11.roots (F.erase univ) = {A, univ \ A})
    (C : Finset L) (hC : C ∈ F) :
    C = univ ∨ C ⊆ A ∨ C ⊆ univ \ A := by
  by_cases hCu : C = univ
  · exact Or.inl hCu
  · obtain ⟨R, hR, hCR⟩ := ADR11.exists_mem_roots_subset (mem_erase.mpr ⟨hCu, hC⟩)
    rw [hsplit, mem_insert, mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact Or.inr (Or.inl hCR)
    · exact Or.inr (Or.inr hCR)
theorem root_split_excludes_mixed_history
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : RankedForestHistory F t) (A C : Finset L)
    (hC : C ∈ F) (hCu : C ≠ univ) (hCA : ¬C ⊆ A) (hCB : ¬C ⊆ univ \ A) :
    ADR11.roots ((historyEnd F t h).erase univ) ≠ {A, univ \ A} := by
  intro hs
  have hm := (historyEnd_spec F hF t h).2.2.1 hC
  rcases root_split_clade_purity _ A hs C hm with hc | hc | hc
  · exact hCu hc
  · exact hCA hc
  · exact hCB hc
end Rhone.Combinatorics
