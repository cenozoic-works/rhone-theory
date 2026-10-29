/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Matrix

/-! # DL‑2 — assembly -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section Eps

variable {F : Type*} [Field F]

def eps (F : Type*) [Field F] : Fin 2 → F := ![1, -1]

@[simp] theorem eps_zero : eps F 0 = 1 := rfl

@[simp] theorem eps_one : eps F 1 = -1 := rfl

theorem centre_single {π : Fin 2 → F} (hπ : π 0 + π 1 = 1) (i : Fin 2) :
    centre π (Pi.single i 1) = eps F i • fvec π := by
  have h0 : centre π (Pi.single (0 : Fin 2) 1) = eps F 0 • fvec π := by
    rw [centre, mean_single, eps_zero, one_smul, fvec]
  have h1 : centre π (Pi.single (1 : Fin 2) 1) = eps F 1 • fvec π := by
    rw [centre, mean_single, single_one_eq hπ, eps_one, neg_one_smul]
    abel
  fin_cases i
  · simpa using h0
  · simpa using h1

end Eps

section Expansion

variable {F : Type*} [Field F] {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable (q : Config 2 2 → F) (M : Finset (SA × SB)) (πA πB : Fin 2 → F)

theorem Q_centred_expansion (s : SA → Fin 2 → F) (w : SB → Fin 2 → F) :
    Q q M s w = ∑ S : Finset SA, ∑ T : Finset SB,
      (∏ u ∈ Sᶜ, mean πA (s u)) * (∏ v ∈ Tᶜ, mean πB (w v))
        * Q q M (fun u => if u ∈ S then centre πA (s u) else 1)
              (fun v => if v ∈ T then centre πB (w v) else 1) := by
  rw [(Q_isMultiA q M w).centred_expansion πA s]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [(Q_isMultiB q M _).centred_expansion πB w, Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem Q_pull_scalars_A (w : SB → Fin 2 → F) (S : Finset SA) (c : SA → F) :
    Q q M (fun u => if u ∈ S then c u • fvec πA else 1) w
      = (∏ u ∈ S, c u) * Q q M (killAt (fvec πA) Sᶜ) w := by
  have hc : (fun u => if u ∈ S then c u • fvec πA else (1 : Fin 2 → F))
      = fun u => (if u ∈ S then c u else 1) • killAt (fvec πA) Sᶜ u := by
    funext u
    by_cases h : u ∈ S <;> simp [killAt, h]
  have hp : (∏ u : SA, (if u ∈ S then c u else 1)) = ∏ u ∈ S, c u := by
    rw [← Finset.prod_filter]
    exact Finset.prod_congr (Finset.filter_univ_mem S) fun _ _ => rfl
  have h0 : ∀ x : SA → Fin 2 → F, (Q_isMultiA q M w).toML x = Q q M x w := fun _ => rfl
  rw [hc, ← h0 (fun u => (if u ∈ S then c u else 1) • killAt (fvec πA) Sᶜ u),
    (Q_isMultiA q M w).toML.map_smul_univ, h0, hp, smul_eq_mul]

theorem Q_pull_scalars_B (s : SA → Fin 2 → F) (T : Finset SB) (c : SB → F) :
    Q q M s (fun v => if v ∈ T then c v • fvec πB else 1)
      = (∏ v ∈ T, c v) * Q q M s (killAt (fvec πB) Tᶜ) := by
  have hc : (fun v => if v ∈ T then c v • fvec πB else (1 : Fin 2 → F))
      = fun v => (if v ∈ T then c v else 1) • killAt (fvec πB) Tᶜ v := by
    funext v
    by_cases h : v ∈ T <;> simp [killAt, h]
  have hp : (∏ v : SB, (if v ∈ T then c v else 1)) = ∏ v ∈ T, c v := by
    rw [← Finset.prod_filter]
    exact Finset.prod_congr (Finset.filter_univ_mem T) fun _ _ => rfl
  have h0 : ∀ x : SB → Fin 2 → F, (Q_isMultiB q M s).toML x = Q q M s x := fun _ => rfl
  rw [hc, ← h0 (fun v => (if v ∈ T then c v else 1) • killAt (fvec πB) Tᶜ v),
    (Q_isMultiB q M s).toML.map_smul_univ, h0, hp, smul_eq_mul]

end Expansion

section DL2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def pairsIn (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) : Finset (SA × SB) :=
  M.filter fun p => p.1 ∈ S ∧ p.2 ∈ T

theorem liveM_compl (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) :
    liveM M Sᶜ Tᶜ = pairsIn M S T := by
  rw [liveM, pairsIn]
  exact Finset.filter_congr fun p _ => by simp

variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem q_xi_eq_sum_Phi (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β)
      = ∑ S : Finset SA, ∑ T : Finset SB,
          ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
            * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v)))
          * Phi q πA πB S.card T.card (pairsIn M S T).card := by
  rw [← Q_basis q M α β, Q_centred_expansion q M πA πB]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  have hSc : ∀ u : SA, mean πA ((fun u => (Pi.single (α u) 1 : Fin 2 → F)) u) = πA (α u) :=
    fun u => mean_single πA (α u)
  have hTc : ∀ v : SB, mean πB ((fun v => (Pi.single (β v) 1 : Fin 2 → F)) v) = πB (β v) :=
    fun v => mean_single πB (β v)
  have hA : (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else (1 : Fin 2 → F))
      = fun u => if u ∈ S then eps F (α u) • fvec πA else 1 := by
    funext u
    by_cases h : u ∈ S
    · rw [ite_eq_left h, ite_eq_left h, centre_single hπA]
    · rw [ite_eq_right h, ite_eq_right h]
  have hB : (fun v => if v ∈ T then centre πB (Pi.single (β v) 1) else (1 : Fin 2 → F))
      = fun v => if v ∈ T then eps F (β v) • fvec πB else 1 := by
    funext v
    by_cases h : v ∈ T
    · rw [ite_eq_left h, ite_eq_left h, centre_single hπB]
    · rw [ite_eq_right h, ite_eq_right h]
  have hcardS : Fintype.card SA - Sᶜ.card = S.card := by
    have h1 := Finset.card_compl S
    have h2 : S.card ≤ Fintype.card SA := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    omega
  have hcardT : Fintype.card SB - Tᶜ.card = T.card := by
    have h1 := Finset.card_compl T
    have h2 : T.card ≤ Fintype.card SB := by
      simpa using Finset.card_le_card (Finset.subset_univ T)
    omega
  rw [Finset.prod_congr rfl fun u _ => hSc u, Finset.prod_congr rfl fun v _ => hTc v, hA, hB,
    Q_pull_scalars_A q M πA _ S (fun u => eps F (α u)),
    Q_pull_scalars_B q M πB _ T (fun v => eps F (β v)),
    Q_killAt_eq_Phi hθA hθB hρ hq hπA hπB M Sᶜ Tᶜ hM, hcardS, hcardT, liveM_compl]
  ring

end DL2

section Coeff

variable {F : Type*} [Field F] {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem eps_mem (A : Subring F) (i : Fin 2) : eps F i ∈ A := by
  fin_cases i
  · exact A.one_mem
  · exact A.neg_mem A.one_mem

theorem labelledCoeff_prod_mem {πA πB : Fin 2 → F} (A : Subring F) (hπA : ∀ i, πA i ∈ A)
    (hπB : ∀ j, πB j ∈ A) (S : Finset SA) (T : Finset SB) (α : SA → Fin 2) (β : SB → Fin 2) :
    ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
      * (∏ u ∈ S, eps F (α u)) * (∏ v ∈ T, eps F (β v))) ∈ A :=
  A.mul_mem (A.mul_mem (A.mul_mem (A.prod_mem fun u _ => hπA (α u))
      (A.prod_mem fun v _ => hπB (β v))) (A.prod_mem fun u _ => eps_mem A (α u)))
    (A.prod_mem fun v _ => eps_mem A (β v))

end Coeff

end Rhone.Probability.SlotDeletion
