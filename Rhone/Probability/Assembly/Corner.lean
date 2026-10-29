/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Assembly

/-! # Corner principle for the assembly polynomial (one direction only) -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Finset MvPolynomial LinearAlgebra.Tridiag LinearAlgebra.Multilinear Multilinear
open SlotDeletion

section Weight

variable {K : Type*} [CommRing K]

theorem weight_wt (d : Fin 4 →₀ ℕ) : Finsupp.weight wt d = (d 0 + d 1, d 2 + d 3) := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_four]
  simp [wt]

theorem eval_ne_zero_imp {φ : PiRing K} (π : Fin 4 → K) (h : eval π φ ≠ 0) : φ ≠ 0 := by
  intro h0
  rw [h0, map_zero] at h
  exact h rfl

theorem eval_corner_eq_coeff {φ : PiRing K} {dA dB : ℕ}
    (hφ : IsWeightedHomogeneous wt φ (dA, dB)) :
    eval ![1, 0, 1, 0] φ = φ.coeff (Finsupp.single 0 dA + Finsupp.single 2 dB) := by
  classical
  have c0 : (![1, 0, 1, 0] : Fin 4 → K) 0 = 1 := rfl
  have c1 : (![1, 0, 1, 0] : Fin 4 → K) 1 = 0 := rfl
  have c2 : (![1, 0, 1, 0] : Fin 4 → K) 2 = 1 := rfl
  have c3 : (![1, 0, 1, 0] : Fin 4 → K) 3 = 0 := rfl
  set d₀ : Fin 4 →₀ ℕ := Finsupp.single 0 dA + Finsupp.single 2 dB with hd₀
  have hd0 : d₀ 0 = dA := by simp [hd₀]
  have hd1 : d₀ 1 = 0 := by simp [hd₀]
  have hd2 : d₀ 2 = dB := by simp [hd₀]
  have hd3 : d₀ 3 = 0 := by simp [hd₀]
  have hprod : (∏ i, (![1, 0, 1, 0] : Fin 4 → K) i ^ d₀ i) = 1 := by
    rw [Fin.prod_univ_four, c0, c1, c2, c3, hd0, hd1, hd2, hd3]
    norm_num
  have key : (∑ d ∈ φ.support, φ.coeff d * ∏ i, (![1, 0, 1, 0] : Fin 4 → K) i ^ d i)
      = φ.coeff d₀ * ∏ i, (![1, 0, 1, 0] : Fin 4 → K) i ^ d₀ i := by
    refine Finset.sum_eq_single d₀ (fun d hd hne => ?_) (fun hd => ?_)
    · have hw : Finsupp.weight wt d = (dA, dB) := hφ (mem_support_iff.mp hd)
      rw [weight_wt] at hw
      have h1 : d 0 + d 1 = dA := congrArg Prod.fst hw
      have h2 : d 2 + d 3 = dB := congrArg Prod.snd hw
      have hz : d 1 ≠ 0 ∨ d 3 ≠ 0 := by
        by_cases h1' : d 1 = 0
        · by_cases h3' : d 3 = 0
          · refine absurd (Finsupp.ext fun k => ?_) hne
            fin_cases k
            · change d 0 = d₀ 0
              rw [hd0]; omega
            · change d 1 = d₀ 1
              rw [hd1]; exact h1'
            · change d 2 = d₀ 2
              rw [hd2]; omega
            · change d 3 = d₀ 3
              rw [hd3]; exact h3'
          · exact Or.inr h3'
        · exact Or.inl h1'
      have hzero : (∏ i, (![1, 0, 1, 0] : Fin 4 → K) i ^ d i) = 0 := by
        rw [Fin.prod_univ_four, c0, c1, c2, c3]
        rcases hz with h | h
        · simp [zero_pow h]
        · simp [zero_pow h]
      rw [hzero, mul_zero]
    · have hc0 : φ.coeff d₀ = 0 := by rwa [mem_support_iff, not_not] at hd
      rw [hc0, zero_mul]
  rw [eval_eq' ![1, 0, 1, 0] φ, key, hprod, mul_one]

section Poly

variable {K : Type*} [Field K]

noncomputable def psiPoly (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) : ℕ → ℕ → ℕ → PiRing K :=
  psi (fun i j => ((T K i j θA θB ρ)⁻¹).map C) (kapR (piAX K)) (gamR (piAX K)) (kapR (piBX K))
    (gamR (piBX K)) p q (fun u => C (v u))

theorem psiPoly_homog (θA θB ρ : K) {p q : ℕ} (v : ℕ → K) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (i j t : ℕ) : IsWeightedHomogeneous wt (psiPoly θA θB ρ p q v i j t) (i - p, j - q) :=
  psi_homog (fun _ _ _ _ => by
      rw [Matrix.map_apply]; exact isWeightedHomogeneous_C _ _)
    (fun _ => isWeightedHomogeneous_C _ _) kapA_homog gamA_homog kapB_homog gamB_homog hp hq
    i j t

theorem psiPoly_eval_eq_w (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) (π : Fin 4 → K) (i j t : ℕ) :
    eval π (psiPoly θA θB ρ p q v i j t)
      = Rhone.Probability.Propagation.w θA θB ρ (kapR ![π 0, π 1]) (gamR ![π 0, π 1])
          (kapR ![π 2, π 3]) (gamR ![π 2, π 3]) p q v i j t := by
  rw [psiPoly, psi_map (eval π : PiRing K →+* K)]
  have hN : (fun i j => (((T K i j θA θB ρ)⁻¹).map (C : K →+* PiRing K)).map
      (eval π : PiRing K →+* K)) = fun i j => (T K i j θA θB ρ)⁻¹ := by
    funext i j
    rw [Matrix.map_map]
    have : ((eval π : PiRing K →+* K) ∘ (C : K →+* PiRing K)) = id := by
      funext x
      simp
    rw [this, Matrix.map_id]
  rw [hN]
  have hkA : (eval π : PiRing K →+* K) (kapR (piAX K)) = kapR ![π 0, π 1] := by
    simp [kapR, piAX]
  have hgA : (eval π : PiRing K →+* K) (gamR (piAX K)) = gamR ![π 0, π 1] := by
    simp [gamR, piAX]
  have hkB : (eval π : PiRing K →+* K) (kapR (piBX K)) = kapR ![π 2, π 3] := by
    simp [kapR, piBX]
  have hgB : (eval π : PiRing K →+* K) (gamR (piBX K)) = gamR ![π 2, π 3] := by
    simp [gamR, piBX]
  rw [hkA, hgA, hkB, hgB, show (fun u => (eval π : PiRing K →+* K) (C (v u))) = v from
    funext fun u => by simp]
  exact psi_eq_w θA θB ρ _ _ _ _ p q v i j t

theorem psiPoly_corner_eq_w (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) (i j t : ℕ) :
    eval ![1, 0, 1, 0] (psiPoly θA θB ρ p q v i j t)
      = Rhone.Probability.Propagation.w θA θB ρ 0 (-1) 0 (-1) p q v i j t := by
  rw [psiPoly_eval_eq_w]
  norm_num [kapR, gamR, show (![1, 0, 1, 0] : Fin 4 → K) 2 = 1 from rfl,
    show (![1, 0, 1, 0] : Fin 4 → K) 3 = 0 from rfl]

theorem psiPoly_corner_eq_w' (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) (i j t : ℕ) :
    eval ![0, 1, 0, 1] (psiPoly θA θB ρ p q v i j t)
      = Rhone.Probability.Propagation.w θA θB ρ 0 1 0 1 p q v i j t := by
  rw [psiPoly_eval_eq_w]
  norm_num [kapR, gamR, show (![0, 1, 0, 1] : Fin 4 → K) 2 = 0 from rfl,
    show (![0, 1, 0, 1] : Fin 4 → K) 3 = 1 from rfl]

end Poly

end Weight

universe u

section AssemblyCorner

variable {K : Type*} [Field K] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

noncomputable def assemblyPoly (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) (α : SA → Fin 2)
    (β : SB → Fin 2) (M : Finset (SA × SB)) : PiRing K :=
  assembly (fun i j => ((T K i j θA θB ρ)⁻¹).map C) (kapR (piAX K)) (gamR (piAX K))
    (kapR (piBX K)) (gamR (piBX K)) p q (fun u => C (v u)) (piAX K) (piBX K) α β M

theorem assemblyPoly_homog (θA θB ρ : K) {p q : ℕ} (v : ℕ → K) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (α : SA → Fin 2) (β : SB → Fin 2) (M : Finset (SA × SB)) :
    IsWeightedHomogeneous wt (assemblyPoly θA θB ρ p q v α β M)
      (Fintype.card SA - p, Fintype.card SB - q) :=
  assembly_homog (fun _ _ _ _ => by rw [Matrix.map_apply]; exact isWeightedHomogeneous_C _ _)
    (fun _ => isWeightedHomogeneous_C _ _) kapA_homog gamA_homog kapB_homog gamB_homog hp hq
    α β M

theorem assemblyPoly_ne_zero_of_corner (θA θB ρ : K) (p q : ℕ) (v : ℕ → K) (α : SA → Fin 2)
    (β : SB → Fin 2) (M : Finset (SA × SB)) (π : Fin 4 → K)
    (h : eval π (assemblyPoly θA θB ρ p q v α β M) ≠ 0) :
    assemblyPoly θA θB ρ p q v α β M ≠ 0 :=
  eval_ne_zero_imp π h

theorem assemblyPoly_corner_eq_coeff (θA θB ρ : K) {p q : ℕ} (v : ℕ → K) (hp : 2 ≤ p)
    (hq : 2 ≤ q) (α : SA → Fin 2) (β : SB → Fin 2) (M : Finset (SA × SB)) :
    eval ![1, 0, 1, 0] (assemblyPoly θA θB ρ p q v α β M)
      = (assemblyPoly θA θB ρ p q v α β M).coeff
        (Finsupp.single 0 (Fintype.card SA - p) + Finsupp.single 2 (Fintype.card SB - q)) :=
  eval_corner_eq_coeff (assemblyPoly_homog θA θB ρ v hp hq α β M)

end AssemblyCorner

section Res

variable {K : Type*} [Field K] {SA SB : Type u}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {θA θB ρ κA γA κB γB : K} {p q : ℕ} {v : ℕ → K} {πA πB : Fin 2 → K}

theorem assembly_res_eq {r : ℕ → ℕ → ℕ → K} {c : K} (M : Finset (SA × SB)) (hM : IsMatching M)
    (α : SA → Fin 2) (β : SB → Fin 2)
    (hprop : ∀ i j t, t ≤ min i j →
      r i j t = c * Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v i j t) :
    (∑ S : Finset SA, ∑ T : Finset SB,
        labelledCoeff πA πB α β S T * r S.card T.card (pairsIn M S T).card)
      = c * ∑ S : Finset SA, ∑ T : Finset SB,
          labelledCoeff πA πB α β S T * Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v
            S.card T.card (pairsIn M S T).card := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [hprop _ _ _ (card_pairsIn_le_min hM S T)]
  ring

theorem assembly_res_ne_zero_iff {r : ℕ → ℕ → ℕ → K} {c : K} (hc : c ≠ 0)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2)
    (hprop : ∀ i j t, t ≤ min i j →
      r i j t = c * Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v i j t) :
    (∑ S : Finset SA, ∑ T : Finset SB,
        labelledCoeff πA πB α β S T * r S.card T.card (pairsIn M S T).card) ≠ 0
      ↔ (∑ S : Finset SA, ∑ T : Finset SB,
          labelledCoeff πA πB α β S T * Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v
            S.card T.card (pairsIn M S T).card) ≠ 0 := by
  rw [assembly_res_eq M hM α β hprop]
  exact mul_ne_zero_iff.trans ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

end Res

end Rhone.Probability.Assembly
