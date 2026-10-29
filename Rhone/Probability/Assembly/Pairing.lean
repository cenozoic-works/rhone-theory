/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Assembly

/-! # Binomial-weighted pair sums of labelled coefficients vanish beyond the matching size -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Finset Polynomial LinearAlgebra.Multilinear Multilinear SlotDeletion

universe u

section Pairing

variable {K : Type*} [CommRing K]

theorem coeff_comp_one_add (h : K[X]) (t₀ : ℕ) :
    (h.comp (1 + X)).coeff t₀ = ∑ d ∈ h.support, h.coeff d * (d.choose t₀ : K) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]

end Pairing

section Base

variable {K : Type*} [CommRing K] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable (πA πB : Fin 2 → K) (α : SA → Fin 2) (β : SB → Fin 2) (M : Finset (SA × SB))

noncomputable def Gz (p q : ℕ) : K[X] :=
  ∑ S ∈ univ.filter (fun S : Finset SA => S.card = p),
    ∑ T ∈ univ.filter (fun T : Finset SB => T.card = q),
      C (labelledCoeff πA πB α β S T) * X ^ (pairsIn M S T).card

noncomputable def pairBinomialSum (p q t₀ : ℕ) : K :=
  ∑ S ∈ univ.filter (fun S : Finset SA => S.card = p),
    ∑ T ∈ univ.filter (fun T : Finset SB => T.card = q),
      (((pairsIn M S T).card.choose t₀ : ℕ) : K) * labelledCoeff πA πB α β S T

theorem natDegree_Gz_le (p q : ℕ) : (Gz πA πB α β M p q).natDegree ≤ M.card := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun S _ => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun T _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  have h1 : ((X : K[X]) ^ (pairsIn M S T).card).natDegree ≤ (pairsIn M S T).card := by
    refine le_trans Polynomial.natDegree_pow_le ?_
    have hX : (X : K[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
    calc (pairsIn M S T).card * (X : K[X]).natDegree
        ≤ (pairsIn M S T).card * 1 := Nat.mul_le_mul_left _ hX
      _ = (pairsIn M S T).card := by ring
  exact le_trans h1 (Finset.card_le_card (Finset.filter_subset _ _))

theorem pairBinomialSum_eq_coeff_comp (p q t₀ : ℕ) :
    pairBinomialSum πA πB α β M p q t₀ = ((Gz πA πB α β M p q).comp (1 + X)).coeff t₀ := by
  have hcomp : (Gz πA πB α β M p q).comp (1 + X)
      = ∑ S ∈ univ.filter (fun S : Finset SA => S.card = p),
          ∑ T ∈ univ.filter (fun T : Finset SB => T.card = q),
            C (labelledCoeff πA πB α β S T) * (1 + X) ^ (pairsIn M S T).card := by
    rw [Gz]
    rw [show ∀ f : Finset SA → K[X], (∑ S ∈ univ.filter (fun S : Finset SA => S.card = p), f S).comp
        (1 + X) = ∑ S ∈ univ.filter (fun S : Finset SA => S.card = p), (f S).comp (1 + X) from
      fun f => map_sum (Polynomial.eval₂RingHom (C : K →+* K[X]) (1 + X)) f _]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [show ∀ g : Finset SB → K[X], (∑ T ∈ univ.filter (fun T : Finset SB => T.card = q), g T).comp
        (1 + X) = ∑ T ∈ univ.filter (fun T : Finset SB => T.card = q), (g T).comp (1 + X) from
      fun g => map_sum (Polynomial.eval₂RingHom (C : K →+* K[X]) (1 + X)) g _]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
  rw [hcomp, Polynomial.finsetSum_coeff, pairBinomialSum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, mul_comm]

theorem pairBinomialSum_eq_zero_of_lt (p q t₀ : ℕ) (h : M.card < t₀) :
    pairBinomialSum πA πB α β M p q t₀ = 0 := by
  refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun T _ => ?_
  have hle : (pairsIn M S T).card ≤ M.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

theorem coeff_comp_eq_zero_of_lt (p q t₀ : ℕ) (h : M.card < t₀) :
    ((Gz πA πB α β M p q).comp (1 + X)).coeff t₀ = 0 := by
  rw [← pairBinomialSum_eq_coeff_comp]
  exact pairBinomialSum_eq_zero_of_lt πA πB α β M p q t₀ h

end Base

end Rhone.Probability.Assembly
