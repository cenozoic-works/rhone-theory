/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFDuality

/-!
# The ancestral step of the two-locus Wright-Fisher dual reduced to the active gene copies

Source: griffiths1991_two_locus_graph, p. 101; ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset

def ancStepOn {M : ℕ} (ζ : DualState M) (A : Finset (Fin M)) (α : A → Choice M) :
    DualState M := fun s =>
  ((univ.filter fun t : A => parentA (α t) = s).inf fun t => mutReq (α t).2.2.1 (ζ t).1,
   (univ.filter fun t : A => parentB (α t) = s).inf fun t => mutReq (α t).2.2.2.1 (ζ t).2)

theorem mutReq_univ (m : Bool) : mutReq m (univ : Finset (Fin 2)) = univ := by
  cases m <;> rfl

theorem lineFactor_univ {M : ℕ} (c u : ℝ) (ch : Choice M) :
    lineFactor c u (univ, univ) ch = choiceWeight M c u ch := by
  simp [lineFactor, mutFactor]

theorem inf_eq_inf_subtype {M : ℕ} (A : Finset (Fin M)) (P : Fin M → Prop) [DecidablePred P]
    (f : Fin M → Finset (Fin 2)) (hf : ∀ t, t ∉ A → f t = univ) :
    (univ.filter P).inf f = (univ.filter fun t : A => P t).inf fun t => f t := by
  apply le_antisymm
  · refine Finset.le_inf fun t ht => Finset.inf_le ?_
    simpa using ht
  · refine Finset.le_inf fun t ht => ?_
    by_cases htA : t ∈ A
    · exact Finset.inf_le (b := (⟨t, htA⟩ : A)) (by simpa using ht)
    · rw [hf t htA]
      exact Finset.subset_univ _

theorem ancStep_eq_ancStepOn {M : ℕ} {ζ : DualState M} {A : Finset (Fin M)}
    (hA : ∀ t, t ∉ A → ζ t = (univ, univ)) (ω : Fin M → Choice M) :
    ancStep ζ ω = ancStepOn ζ A (fun t => ω t) := by
  funext s
  simp only [ancStep, ancStepOn]
  ext1
  · exact inf_eq_inf_subtype A _ _ fun t ht => by rw [hA t ht, mutReq_univ]
  · exact inf_eq_inf_subtype A _ _ fun t ht => by rw [hA t ht, mutReq_univ]

theorem sum_ancWeight_eq_sum_active {M : ℕ} (hM : 0 < M) (c u : ℝ) {ζ : DualState M}
    {A : Finset (Fin M)} (hA : ∀ t, t ∉ A → ζ t = (univ, univ)) (g : DualState M → ℝ) :
    ∑ ω : Fin M → Choice M, ancWeight M c u ζ ω * g (ancStep ζ ω) =
      ∑ α : A → Choice M, (∏ t : A, lineFactor c u (ζ t) (α t)) * g (ancStepOn ζ A α) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun t : Fin M => t ∈ A) (fun _ => Choice M)
  have hw : ∀ ω : Fin M → Choice M, ancWeight M c u ζ ω =
      (∏ t : A, lineFactor c u (ζ t) (ω t)) *
        ∏ t : {t : Fin M // t ∉ A}, choiceWeight M c u (ω t) := by
    intro ω
    rw [ancWeight, ← Fintype.prod_subtype_mul_prod_subtype (fun t : Fin M => t ∈ A)]
    congr 1
    all_goals first
      | rfl
      | exact Finset.prod_congr (by ext; simp) fun t _ => by rw [hA t t.2, lineFactor_univ]
      | exact Finset.prod_congr (by ext; simp) fun t _ => rfl
  simp_rw [hw, ancStep_eq_ancStepOn hA]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hfree : ∑ β : ({t : Fin M // t ∉ A} → Choice M),
      ∏ t, choiceWeight M c u (β t) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : {t : Fin M // t ∉ A}) (ch : Choice M) =>
      choiceWeight M c u ch)]
    simp [sum_choiceWeight hM]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hα : ∀ β : {t : Fin M // t ∉ A} → Choice M, (fun t : A => e.symm (α, β) t) = α := by
    intro β
    funext t
    simp [e, Equiv.piEquivPiSubtypeProd, t.2]
  have hβ : ∀ β : {t : Fin M // t ∉ A} → Choice M,
      (fun t : {t : Fin M // t ∉ A} => e.symm (α, β) t) = β := by
    intro β
    funext t
    simp [e, Equiv.piEquivPiSubtypeProd, t.2]
  calc _ = ∑ β : ({t : Fin M // t ∉ A} → Choice M),
        ((∏ t : A, lineFactor c u (ζ t) (α t)) * g (ancStepOn ζ A α)) *
          ∏ t, choiceWeight M c u (β t) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        have h1 := congrFun (hα β)
        have h2 := congrFun (hβ β)
        simp only [h1, h2]
        ring
    _ = _ := by rw [← Finset.mul_sum, hfree, mul_one]

end Rhone.Coalescent.WFTwoLocusDual
