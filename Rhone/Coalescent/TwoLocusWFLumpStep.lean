/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFInsert
public import Rhone.Coalescent.TwoLocusWFActive

/-!
# The lumped fixed-point equation of the two-locus Wright-Fisher dual

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset

theorem ancStepOn_eq_stepL {M n : ℕ} (ζ : DualState M) (A : Finset (Fin M)) (e : Fin n ≃ A)
    (α : A → Choice M) :
    ancStepOn ζ A α = stepL (fun k => ζ (e k)) (fun k => α (e k)) := by
  have key : ∀ (P Q : A → Prop), (∀ t, P t → Q t) ↔ ∀ k, P (e k) → Q (e k) := fun P Q =>
    ⟨fun h k => h (e k), fun h t => by obtain ⟨k, rfl⟩ := e.surjective t; exact h k⟩
  funext s
  ext1
  · ext b
    simp only [ancStepOn, stepL, mem_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key (fun t => parentA (α t) = s) (fun t => b ∈ mutReq (α t).2.2.1 (ζ t).1)
  · ext b
    simp only [ancStepOn, stepL, mem_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key (fun t => parentB (α t) = s) (fun t => b ∈ mutReq (α t).2.2.2.1 (ζ t).2)

theorem sum_active_eq_sum_stepL {M n : ℕ} (c u : ℝ) (ζ : DualState M) (A : Finset (Fin M))
    (e : Fin n ≃ A) (g : DualState M → ℝ) :
    ∑ α : A → Choice M, (∏ t : A, lineFactor c u (ζ t) (α t)) * g (ancStepOn ζ A α) =
      ∑ β : Fin n → Choice M,
        (∏ k, lineFactor c u (ζ (e k)) (β k)) * g (stepL (fun k => ζ (e k)) β) := by
  refine Fintype.sum_equiv (e.symm.arrowCongr (Equiv.refl (Choice M))) _ _ fun α => ?_
  change _ = (∏ k, lineFactor c u (ζ (e k)) (α (e k))) *
    g (stepL (fun k => ζ (e k)) (fun k => α (e k)))
  rw [ancStepOn_eq_stepL ζ A e α]
  congr 1
  exact (e.prod_comp (fun t => lineFactor c u (ζ t) (α t))).symm

open Classical in
def cntAbsorb (M : ℕ) (c u : ℝ) (κ : Req → ℕ) : ℝ :=
  if h : ∃ ξ : DualState M, cnt ξ = κ then ancAbsorb M c u h.choose else 0

theorem ancAbsorb_eq_cntAbsorb (M : ℕ) (c u : ℝ) (ξ : DualState M) :
    ancAbsorb M c u ξ = cntAbsorb M c u (cnt ξ) := by
  have h : ∃ ξ' : DualState M, cnt ξ' = cnt ξ := ⟨ξ, rfl⟩
  rw [cntAbsorb, dite_eq_left h]
  exact ancAbsorb_eq_of_cnt_eq c u fun r => (congrFun h.choose_spec r).symm

theorem ancAbsorb_eq_lumpChain {M n : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) {ζ : DualState M} {A : Finset (Fin M)}
    (hA : ∀ t, t ∉ A → ζ t = (univ, univ)) (e : Fin n ≃ A) :
    ancAbsorb M c u ζ =
      lumpChain M c u (fun k => ζ (e k)) (cntAbsorb M c u) (cnt (fullState M)) := by
  rw [ancAbsorb_eq_sum_ancKernel hM hc0 hc1 hu0 hu1 ζ, sum_ancKernel_mul,
    sum_ancWeight_eq_sum_active hM c u hA, sum_active_eq_sum_stepL c u ζ A e,
    ← sum_stepL hM c u]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [ancAbsorb_eq_cntAbsorb]

end Rhone.Coalescent.WFTwoLocusDual
