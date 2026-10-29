/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Bidegree
public import Rhone.Probability.SlotDeletion.Assembly

/-! # Assembly of the residue hierarchy and its bidegree -/

@[expose] public section

universe u

namespace Rhone.Probability.Assembly

open Finset MvPolynomial LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear
open SlotDeletion

section Coeff

variable {R : Type*} [CommRing R] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def labelledCoeff (πA πB : Fin 2 → R) (α : SA → Fin 2) (β : SB → Fin 2) (S : Finset SA)
    (T : Finset SB) : R :=
  (∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v)) * (∏ u ∈ S, epsR R (α u))
    * (∏ v ∈ T, epsR R (β v))

end Coeff

section Corpus

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {q : Rhone.LinearAlgebra.Recursion.Config 2 2 → F}

theorem q_xi_eq_sum_labelledCoeff_mul_Phi (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β)
      = ∑ S : Finset SA, ∑ T : Finset SB,
          labelledCoeff πA πB α β S T * Phi q πA πB S.card T.card (pairsIn M S T).card :=
  q_xi_eq_sum_Phi hθA hθB hρ hq hπA hπB M hM α β

end Corpus

section Card

variable {SA SB : Type u} [DecidableEq SA] [DecidableEq SB]

theorem card_pairsIn_le_left {M : Finset (SA × SB)} (hM : IsMatching M) (S : Finset SA)
    (T : Finset SB) : (pairsIn M S T).card ≤ S.card := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · rw [pairsIn] at hx
    exact (Finset.mem_filter.mp hx).2.1
  · rw [Finset.mem_coe, pairsIn] at hx hy
    exact hM.fst x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy

theorem card_pairsIn_le_right {M : Finset (SA × SB)} (hM : IsMatching M) (S : Finset SA)
    (T : Finset SB) : (pairsIn M S T).card ≤ T.card := by
  refine Finset.card_le_card_of_injOn Prod.snd (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · rw [pairsIn] at hx
    exact (Finset.mem_filter.mp hx).2.2
  · rw [Finset.mem_coe, pairsIn] at hx hy
    exact hM.snd x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy

theorem card_pairsIn_le_min {M : Finset (SA × SB)} (hM : IsMatching M) (S : Finset SA)
    (T : Finset SB) : (pairsIn M S T).card ≤ min S.card T.card :=
  le_min (card_pairsIn_le_left hM S T) (card_pairsIn_le_right hM S T)

end Card

section Assembly

variable {R : Type*} [CommRing R] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

noncomputable def assembly (N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R)
    (κA γA κB γB : R) (p q : ℕ) (v : ℕ → R) (πA πB : Fin 2 → R) (α : SA → Fin 2)
    (β : SB → Fin 2) (M : Finset (SA × SB)) : R :=
  ∑ S : Finset SA, ∑ T : Finset SB,
    labelledCoeff πA πB α β S T * psi N κA γA κB γB p q v S.card T.card (pairsIn M S T).card

end Assembly

section Homog

variable {K : Type*} [CommRing K] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem piAX_homog (a : Fin 2) : IsWeightedHomogeneous wt (piAX K a) (1, 0) := by
  fin_cases a
  · simpa using isWeightedHomogeneous_X K wt 0
  · simpa using isWeightedHomogeneous_X K wt 1

theorem piBX_homog (b : Fin 2) : IsWeightedHomogeneous wt (piBX K b) (0, 1) := by
  fin_cases b
  · simpa using isWeightedHomogeneous_X K wt 2
  · simpa using isWeightedHomogeneous_X K wt 3

theorem epsR_homog (a : Fin 2) : IsWeightedHomogeneous wt (epsR (PiRing K) a) 0 := by
  fin_cases a
  · simpa using isWeightedHomogeneous_one K wt
  · simpa using (isWeightedHomogeneous_one K wt (σ := Fin 4)).neg

theorem labelledCoeff_homog (α : SA → Fin 2) (β : SB → Fin 2) (S : Finset SA) (T : Finset SB) :
    IsWeightedHomogeneous wt (labelledCoeff (piAX K) (piBX K) α β S T)
      (Fintype.card SA - S.card, Fintype.card SB - T.card) := by
  have hA : IsWeightedHomogeneous wt (∏ u ∈ Sᶜ, piAX K (α u)) ((Sᶜ).card, 0) := by
    have h := IsWeightedHomogeneous.prod (R := K) (w := wt) Sᶜ (fun u => piAX K (α u))
      (fun _ => ((1, 0) : ℕ × ℕ)) (fun u _ => piAX_homog (α u))
    simpa [Finset.sum_const, Prod.ext_iff] using h
  have hB : IsWeightedHomogeneous wt (∏ v ∈ Tᶜ, piBX K (β v)) (0, (Tᶜ).card) := by
    have h := IsWeightedHomogeneous.prod (R := K) (w := wt) Tᶜ (fun v => piBX K (β v))
      (fun _ => ((0, 1) : ℕ × ℕ)) (fun v _ => piBX_homog (β v))
    simpa [Finset.sum_const, Prod.ext_iff] using h
  have hεA : IsWeightedHomogeneous wt (∏ u ∈ S, epsR (PiRing K) (α u)) 0 := by
    have h := IsWeightedHomogeneous.prod (R := K) (w := wt) S (fun u => epsR (PiRing K) (α u))
      (fun _ => (0 : ℕ × ℕ)) (fun u _ => epsR_homog (α u))
    simpa using h
  have hεB : IsWeightedHomogeneous wt (∏ v ∈ T, epsR (PiRing K) (β v)) 0 := by
    have h := IsWeightedHomogeneous.prod (R := K) (w := wt) T (fun v => epsR (PiRing K) (β v))
      (fun _ => (0 : ℕ × ℕ)) (fun v _ => epsR_homog (β v))
    simpa using h
  have hcompl : (Sᶜ).card = Fintype.card SA - S.card := Finset.card_compl S
  have hcompl' : (Tᶜ).card = Fintype.card SB - T.card := Finset.card_compl T
  rw [labelledCoeff, ← hcompl, ← hcompl']
  refine homog_mul (homog_mul (homog_mul hA hB ?_) hεA (add_zero _)) hεB (add_zero _)
  simp

theorem assembly_homog {N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) (PiRing K)}
    {κA γA κB γB : PiRing K} {p q : ℕ} {v : ℕ → PiRing K}
    (hN : ∀ i j s u, IsWeightedHomogeneous wt (N i j s u) 0)
    (hv : ∀ u, IsWeightedHomogeneous wt (v u) 0)
    (hκA : IsWeightedHomogeneous wt κA (2, 0)) (hγA : IsWeightedHomogeneous wt γA (1, 0))
    (hκB : IsWeightedHomogeneous wt κB (0, 2)) (hγB : IsWeightedHomogeneous wt γB (0, 1))
    (hp : 2 ≤ p) (hq : 2 ≤ q) (α : SA → Fin 2) (β : SB → Fin 2) (M : Finset (SA × SB)) :
    IsWeightedHomogeneous wt
      (assembly N κA γA κB γB p q v (piAX K) (piBX K) α β M)
      (Fintype.card SA - p, Fintype.card SB - q) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun S _ => IsWeightedHomogeneous.sum _ _ _ fun T _ => ?_
  by_cases hup : p ≤ S.card ∧ q ≤ T.card
  · refine homog_mul (labelledCoeff_homog α β S T)
      (psi_homog hN hv hκA hγA hκB hγB hp hq S.card T.card _) ?_
    have h1 : S.card ≤ Fintype.card SA := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    have h2 : T.card ≤ Fintype.card SB := by
      simpa using Finset.card_le_card (Finset.subset_univ T)
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    omega
  · rw [psi_off hup, mul_zero]
    exact isWeightedHomogeneous_zero K wt
      (Fintype.card SA - p, Fintype.card SB - q)

end Homog

end Rhone.Probability.Assembly
