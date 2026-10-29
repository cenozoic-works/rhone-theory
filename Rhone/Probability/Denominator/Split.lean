/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Surj

/-! # The top-block coefficient is a unit, and the top-block summand of `q` -/

@[expose] public section

universe u

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

section Coeff

variable {F : Type*} [Field F] {SA SB : Type u} [Fintype SA] [Fintype SB]

theorem eps_mul_self (F : Type*) [Field F] (i : Fin 2) : eps F i * eps F i = 1 := by
  fin_cases i <;> norm_num

def topCoeff (F : Type*) [Field F] (α : SA → Fin 2) (β : SB → Fin 2) : F :=
  (∏ u : SA, eps F (α u)) * (∏ v : SB, eps F (β v))

theorem topCoeff_mul_self (α : SA → Fin 2) (β : SB → Fin 2) :
    topCoeff F α β * topCoeff F α β = 1 := by
  have hA : (∏ u : SA, eps F (α u)) * (∏ u : SA, eps F (α u)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun u _ => eps_mul_self F (α u)
  have hB : (∏ v : SB, eps F (β v)) * (∏ v : SB, eps F (β v)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun v _ => eps_mul_self F (β v)
  rw [topCoeff]
  calc (∏ u : SA, eps F (α u)) * (∏ v : SB, eps F (β v))
        * ((∏ u : SA, eps F (α u)) * (∏ v : SB, eps F (β v)))
      = ((∏ u : SA, eps F (α u)) * (∏ u : SA, eps F (α u)))
        * ((∏ v : SB, eps F (β v)) * (∏ v : SB, eps F (β v))) := by ring
    _ = 1 := by rw [hA, hB, one_mul]

theorem topCoeff_mem (A : Subring F) (α : SA → Fin 2) (β : SB → Fin 2) :
    topCoeff F α β ∈ A :=
  A.mul_mem (A.prod_mem fun u _ => eps_mem A (α u)) (A.prod_mem fun v _ => eps_mem A (β v))

theorem isUnit_topCoeff (α : SA → Fin 2) (β : SB → Fin 2) : IsUnit (topCoeff F α β) :=
  ⟨⟨topCoeff F α β, topCoeff F α β, topCoeff_mul_self α β, topCoeff_mul_self α β⟩, rfl⟩

theorem card_lt_card_univ {S : Finset SA} (h : S ≠ univ) : S.card < Fintype.card SA :=
  (Finset.card_lt_iff_ne_univ S).2 h

end Coeff

section Split

variable {F : Type*} [Field F]
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {πA πB : Fin 2 → F} {q : Config 2 2 → F}

noncomputable def labelledTerm (q : Config 2 2 → F) (πA πB : Fin 2 → F) (M : Finset (SA × SB))
    (α : SA → Fin 2) (β : SB → Fin 2) (S : Finset SA) (T : Finset SB) : F :=
  ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
      * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v)))
    * Phi q πA πB S.card T.card (pairsIn M S T).card

noncomputable def psi (q : Config 2 2 → F) (πA πB : Fin 2 → F) (M : Finset (SA × SB))
    (α : SA → Fin 2) (β : SB → Fin 2) : F :=
  (∑ T ∈ (univ : Finset (Finset SB)).erase univ, labelledTerm q πA πB M α β univ T)
    + ∑ S ∈ (univ : Finset (Finset SA)).erase univ, ∑ T : Finset SB,
        labelledTerm q πA πB M α β S T

theorem pairsIn_univ_univ (M : Finset (SA × SB)) :
    pairsIn M (univ : Finset SA) (univ : Finset SB) = M :=
  Finset.filter_true_of_mem fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩

theorem labelledTerm_univ (M : Finset (SA × SB)) (α : SA → Fin 2) (β : SB → Fin 2) :
    labelledTerm q πA πB M α β univ univ
      = topCoeff F α β * Phi q πA πB (Fintype.card SA) (Fintype.card SB) M.card := by
  rw [labelledTerm, topCoeff, Finset.compl_univ, Finset.compl_univ, Finset.prod_empty,
    Finset.prod_empty, one_mul, one_mul, pairsIn_univ_univ, Finset.card_univ, Finset.card_univ]

variable [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem q_xi_eq_topCoeff_mul_Phi_add_psi (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β)
      = topCoeff F α β * Phi q πA πB (Fintype.card SA) (Fintype.card SB) M.card
        + psi q πA πB M α β := by
  have hbody : (∑ S : Finset SA, ∑ T : Finset SB,
      (((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
          * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v)))
        * Phi q πA πB S.card T.card (pairsIn M S T).card))
      = ∑ S : Finset SA, ∑ T : Finset SB, labelledTerm q πA πB M α β S T := rfl
  rw [q_xi_eq_sum_Phi hθA hθB hρ hq hπA hπB M hM α β, hbody,
    ← Finset.add_sum_erase _
      (fun S : Finset SA => ∑ T : Finset SB, labelledTerm q πA πB M α β S T)
      (Finset.mem_univ (univ : Finset SA)),
    ← Finset.add_sum_erase _ (fun T : Finset SB => labelledTerm q πA πB M α β univ T)
      (Finset.mem_univ (univ : Finset SB)),
    labelledTerm_univ, psi, add_assoc]

theorem Dcut_mul_labelledTerm_mem (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (α : SA → Fin 2) (β : SB → Fin 2)
    (S : Finset SA) (T : Finset SB)
    (hne : S.card < Fintype.card SA ∨ T.card < Fintype.card SB)
    (hcard : 2 ≤ Fintype.card SA) :
    Dcut θA θB ρ (Fintype.card SA) (Fintype.card SB) * labelledTerm q πA πB M α β S T ∈ A := by
  have hle1 : S.card ≤ Fintype.card SA := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hle2 : T.card ≤ Fintype.card SB := by
    simpa using Finset.card_le_card (Finset.subset_univ T)
  obtain ⟨c, hcA, hc⟩ := Dfull_dvd_Dcut_mem A haA haB haρ hle1 hle2 hne hcard
  have hrw : Dcut θA θB ρ (Fintype.card SA) (Fintype.card SB) * labelledTerm q πA πB M α β S T
      = (((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
            * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v))) * c)
        * (Dfull θA θB ρ S.card T.card
            * Phi q πA πB S.card T.card (pairsIn M S T).card) := by
    rw [labelledTerm, hc]
    ring
  rw [hrw]
  exact A.mul_mem (A.mul_mem (labelledCoeff_prod_mem A hπAm hπBm S T α β) hcA)
    (Dfull_mul_Phi_mem' hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB _ _ _)

theorem Dcut_mul_psi_mem (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (α : SA → Fin 2) (β : SB → Fin 2)
    (hcard : 2 ≤ Fintype.card SA) :
    Dcut θA θB ρ (Fintype.card SA) (Fintype.card SB) * psi q πA πB M α β ∈ A := by
  rw [psi, mul_add]
  refine A.add_mem ?_ ?_
  · rw [Finset.mul_sum]
    refine A.sum_mem fun T hT => ?_
    exact Dcut_mul_labelledTerm_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB M α β _ T
      (Or.inr (card_lt_card_univ (Finset.mem_erase.mp hT).1)) hcard
  · rw [Finset.mul_sum]
    refine A.sum_mem fun S hS => ?_
    rw [Finset.mul_sum]
    refine A.sum_mem fun T _ => ?_
    exact Dcut_mul_labelledTerm_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB M α β S T
      (Or.inl (card_lt_card_univ (Finset.mem_erase.mp hS).1)) hcard

end Split

end Rhone.Probability.Denominator
