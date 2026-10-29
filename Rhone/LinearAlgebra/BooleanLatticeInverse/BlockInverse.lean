/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.Projector
public import Rhone.LinearAlgebra.BooleanLatticeInverse.Tk

/-! # The block inverse on the truncated Boolean lattice -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Matrix Tridiag RecombinationExpansion

variable {F : Type*} [Field F] {i : ℕ}

def phiK (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) (k s : ℕ) : Finset (Fin i) → F :=
  ∑ s' ∈ range (sig i j k + 1), GK θA θB ρ i j k s s' • proj k (k + s') (lev (k + s') R)

def blockSol (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) : Finset (Fin i) → F := fun S =>
  (∑ k ∈ range (min S.card (i - S.card) + 1),
    (D ^ (S.card - k)) (phiK θA θB ρ j R k (S.card - k))) S

def IsBlockSol (θA θB ρ : F) (j : ℕ) (R Φ : Finset (Fin i) → F) : Prop :=
  ∀ S : Finset (Fin i), S.card ≤ j →
    dcoef F i j θA θB ρ S.card * Φ S - ρ * D Φ S - 2 * ((j - S.card : ℕ) : F) * U Φ S = R S

def strSum (φ : ℕ → ℕ → Finset (Fin i) → F) (t : ℕ) : Finset (Fin i) → F :=
  ∑ k ∈ range (t + 1), (D ^ (t - k)) (φ k (t - k))

def brk (d ρ c : F) (φ : ℕ → ℕ → Finset (Fin i) → F) (k s : ℕ) : Finset (Fin i) → F :=
  d • φ k s - (if s = 0 then 0 else ρ • φ k (s - 1))
    - (c * ((s : F) + 1) * ((i : F) - 2 * (k : F) - (s : F))) • φ k (s + 1)

theorem isPrim_brk {φ : ℕ → ℕ → Finset (Fin i) → F} (hφ : ∀ k s, IsPrim k (φ k s))
    (d ρ c : F) (k s : ℕ) : IsPrim k (brk d ρ c φ k s) := by
  refine (((hφ k s).smul d).sub ?_).sub ((hφ k (s + 1)).smul _)
  split_ifs
  · exact isPrim_zero k
  · exact (hφ k (s - 1)).smul ρ

theorem D_strSum (φ : ℕ → ℕ → Finset (Fin i) → F) (t : ℕ) :
    D (strSum φ t) = ∑ k ∈ range (t + 1), (D ^ (t + 1 - k)) (φ k (t - k)) := by
  rw [strSum, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show t + 1 - k = (t - k) + 1 from by omega, pow_succ', Module.End.mul_apply]

theorem U_strSum {φ : ℕ → ℕ → Finset (Fin i) → F} (hφ : ∀ k s, IsPrim k (φ k s)) (t : ℕ) :
    U (strSum φ (t + 1)) = ∑ k ∈ range (t + 1),
      ((((t - k : ℕ) : F) + 1) * ((i : F) - 2 * (k : F) - ((t - k : ℕ) : F)))
        • (D ^ (t - k)) (φ k (t - k + 1)) := by
  rw [strSum, map_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, Module.End.one_apply,
    (hφ _ _).2, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show t + 1 - k = (t - k) + 1 from by omega, (hφ k _).U_string (t - k)]

theorem strSum_op {φ : ℕ → ℕ → Finset (Fin i) → F} (hφ : ∀ k s, IsPrim k (φ k s))
    (d ρ c : F) (t : ℕ) :
    d • strSum φ t - ρ • (if t = 0 then 0 else D (strSum φ (t - 1))) - c • U (strSum φ (t + 1))
      = ∑ k ∈ range (t + 1), (D ^ (t - k)) (brk d ρ c φ k (t - k)) := by
  have e1 : ∑ k ∈ range (t + 1), (D ^ (t - k)) (brk d ρ c φ k (t - k))
      = (∑ k ∈ range (t + 1), d • (D ^ (t - k)) (φ k (t - k)))
        - (∑ k ∈ range (t + 1), (D ^ (t - k)) (if t - k = 0 then 0 else ρ • φ k (t - k - 1)))
        - ∑ k ∈ range (t + 1), (c * (((t - k : ℕ) : F) + 1)
            * ((i : F) - 2 * (k : F) - ((t - k : ℕ) : F))) • (D ^ (t - k)) (φ k (t - k + 1)) := by
    simp only [brk, map_sub, map_smul, Finset.sum_sub_distrib]
  rw [e1]
  congr 1
  · congr 1
    · rw [strSum, Finset.smul_sum]
    · cases t with
      | zero => simp
      | succ t =>
        rw [ite_eq_right (Nat.succ_ne_zero t), Nat.add_sub_cancel, D_strSum, Finset.smul_sum]
        conv_rhs => rw [Finset.sum_range_succ]
        rw [Nat.sub_self, ite_eq_left rfl, map_zero, add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [ite_eq_right (by omega), map_smul, show t + 1 - k - 1 = t - k from by omega]
  · rw [U_strSum hφ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
    congr 1
    ring

theorem strSum_eq [CharZero F] {φ : ℕ → ℕ → Finset (Fin i) → F}
    (hφ : ∀ k s, IsPrim k (φ k s)) (t : ℕ) :
    strSum φ t = ∑ k ∈ range (min t (i - t) + 1), (D ^ (t - k)) (φ k (t - k)) := by
  have hsub : range (min t (i - t) + 1) ⊆ range (t + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  rw [strSum, Finset.sum_subset hsub]
  intro k hk hk2
  rw [Finset.mem_range] at hk hk2
  exact (hφ k _).D_pow_eq_zero (by omega)

theorem block_apply_of_strSum (θA θB ρ : F) (j : ℕ) {φ : ℕ → ℕ → Finset (Fin i) → F}
    (hφ : ∀ k s, IsPrim k (φ k s)) {Φ : Finset (Fin i) → F}
    (hΦ : ∀ S : Finset (Fin i), S.card ≤ j → Φ S = strSum φ S.card S)
    {S : Finset (Fin i)} (hS : S.card ≤ j) :
    dcoef F i j θA θB ρ S.card * Φ S - ρ * D Φ S - 2 * ((j - S.card : ℕ) : F) * U Φ S
      = (∑ k ∈ range (S.card + 1), (D ^ (S.card - k))
          (brk (dcoef F i j θA θB ρ S.card) ρ (2 * ((j - S.card : ℕ) : F)) φ k
            (S.card - k))) S := by
  rw [← strSum_op hφ]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · congr 1
    · rw [hΦ S hS]
    · congr 1
      by_cases h0 : S.card = 0
      · rw [ite_eq_left h0, Finset.card_eq_zero.mp h0, D_apply, Finset.sum_empty, Pi.zero_apply]
      · rw [ite_eq_right h0, D_apply, D_apply]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hc : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
        rw [hΦ _ (by omega), hc]
  · by_cases hj : S.card = j
    · rw [hj, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, zero_mul]
    · congr 1
      rw [U_apply, U_apply]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hc : (insert x S).card = S.card + 1 :=
        Finset.card_insert_of_notMem (Finset.mem_compl.mp hx)
      rw [hΦ _ (by omega), hc]

section CharZero

variable [CharZero F]

theorem isPrim_phiK (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) {k : ℕ} (hk : 2 * k ≤ i)
    (s : ℕ) : IsPrim k (phiK θA θB ρ j R k s) := by
  refine isPrim_sum _ _ fun s' hs' => IsPrim.smul ?_ _
  have h1 : s' ≤ sig i j k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs')
  have h2 : s' ≤ i - 2 * k := le_trans h1 (min_le_left _ _)
  exact proj_isPrim (by omega) (by omega) (by omega) (isLevel_lev _ R)

def phiR (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) (k s : ℕ) : Finset (Fin i) → F :=
  if 2 * k ≤ i ∧ k ≤ j then phiK θA θB ρ j R k s else 0

theorem isPrim_phiR (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F) (k s : ℕ) :
    IsPrim k (phiR θA θB ρ j R k s) := by
  rw [phiR]
  split_ifs with h
  · exact isPrim_phiK θA θB ρ j R h.1 s
  · exact isPrim_zero k

omit [CharZero F] in
theorem brk_phiR {θA θB ρ : F} {j : ℕ} (R : Finset (Fin i) → F) {k : ℕ} (hk : 2 * k ≤ i)
    (hkj : k ≤ j) (hdet : detK θA θB ρ i j k ≠ 0) {s : ℕ} (hs : s ≤ sig i j k) :
    brk (dcoef F i j θA θB ρ (k + s)) ρ (2 * ((j - (k + s) : ℕ) : F)) (phiR θA θB ρ j R) k s
      = proj k (k + s) (lev (k + s) R) := by
  have hsum : proj k (k + s) (lev (k + s) R) = ∑ s' ∈ range (sig i j k + 1),
      (if s = s' then (1 : F) else 0) • proj k (k + s') (lev (k + s') R) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (by omega))]
  have hite : (if s = 0 then (0 : Finset (Fin i) → F) else ρ • phiK θA θB ρ j R k (s - 1))
      = ∑ s' ∈ range (sig i j k + 1),
          (if s = 0 then 0 else ρ * GK θA θB ρ i j k (s - 1) s')
            • proj k (k + s') (lev (k + s') R) := by
    split_ifs
    · simp
    · rw [phiK, Finset.smul_sum]
      exact Finset.sum_congr rfl fun s' _ => smul_smul _ _ _
  rw [hsum, brk]
  simp only [phiR, ite_eq_left (And.intro hk hkj)]
  rw [hite, phiK, phiK, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s' hs' => ?_
  have hs'' : s' ≤ sig i j k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs')
  rw [smul_smul, smul_smul, ← sub_smul, ← sub_smul, ← TK_GK hk hdet hs hs'']

theorem blockSol_eq_strSum (θA θB ρ : F) (j : ℕ) (R : Finset (Fin i) → F)
    {S : Finset (Fin i)} (hS : S.card ≤ j) :
    blockSol θA θB ρ j R S = strSum (phiR θA θB ρ j R) S.card S := by
  have hSi : S.card ≤ i := by simpa using Finset.card_le_univ S
  rw [strSum_eq (isPrim_phiR θA θB ρ j R)]
  unfold blockSol
  refine congrFun (Finset.sum_congr rfl fun k hk => ?_) S
  have hk' : k ≤ min S.card (i - S.card) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 := le_trans hk' (min_le_left _ _)
  have h2 := le_trans hk' (min_le_right _ _)
  rw [phiR, ite_eq_left ⟨by omega, by omega⟩]

theorem blockSol_isBlockSol {θA θB ρ : F} {j : ℕ}
    (hdet : ∀ k, 2 * k ≤ i → k ≤ j → detK θA θB ρ i j k ≠ 0) (R : Finset (Fin i) → F) :
    IsBlockSol θA θB ρ j R (blockSol θA θB ρ j R) := by
  intro S hS
  have hSi : S.card ≤ i := by simpa using Finset.card_le_univ S
  rw [block_apply_of_strSum θA θB ρ j (isPrim_phiR θA θB ρ j R)
    (fun S hS => blockSol_eq_strSum θA θB ρ j R hS) hS]
  have key : ∑ k ∈ range (S.card + 1), (D ^ (S.card - k))
      (brk (dcoef F i j θA θB ρ S.card) ρ (2 * ((j - S.card : ℕ) : F)) (phiR θA θB ρ j R) k
        (S.card - k)) = lev S.card R := by
    have hsub : range (min S.card (i - S.card) + 1) ⊆ range (S.card + 1) := by
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    rw [← sum_D_proj hSi (isLevel_lev S.card R), ← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ min S.card (i - S.card) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 := le_trans hk' (min_le_left _ _)
      have h2 := le_trans hk' (min_le_right _ _)
      have h3 := brk_phiR R (show 2 * k ≤ i from by omega) (show k ≤ j from by omega)
        (hdet k (by omega) (by omega)) (s := S.card - k)
        (le_min (by omega) (by omega))
      rw [show k + (S.card - k) = S.card from by omega] at h3
      rw [h3]
    · intro k hk hk2
      rw [Finset.mem_range] at hk hk2
      exact (isPrim_brk (isPrim_phiR θA θB ρ j R) _ _ _ k _).D_pow_eq_zero (by omega)
  rw [key, lev_apply_of_card R rfl]

theorem eq_blockSol_of_isBlockSol {θA θB ρ : F} {j : ℕ}
    (hdet : ∀ k, 2 * k ≤ i → k ≤ j → detK θA θB ρ i j k ≠ 0) {R Φ : Finset (Fin i) → F}
    (h : IsBlockSol θA θB ρ j R Φ) {S : Finset (Fin i)} (hS : S.card ≤ j) :
    Φ S = blockSol θA θB ρ j R S := by
  choose y hy hyeq using fun t => exists_prim_decomp t (lev t Φ) (isLevel_lev t Φ)
  set φ : ℕ → ℕ → Finset (Fin i) → F := fun k s => y (k + s) k with hφdef
  have hφ : ∀ k s, IsPrim k (φ k s) := fun k s => hy (k + s) k
  have hstr : ∀ t, strSum φ t = lev t Φ := by
    intro t
    rw [hyeq t, strSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [hφdef]
    simp only
    rw [show k + (t - k) = t from by omega]
  have hΦ : ∀ S : Finset (Fin i), S.card ≤ j → Φ S = strSum φ S.card S := by
    intro S _
    rw [hstr, lev_apply_of_card Φ rfl]
  have hB : ∀ t, t ≤ j → ∑ k ∈ range (t + 1), (D ^ (t - k))
      (brk (dcoef F i j θA θB ρ t) ρ (2 * ((j - t : ℕ) : F)) φ k (t - k)) = lev t R := by
    intro t ht
    refine IsLevel.ext (isLevel_sum _ _ fun k hk => ?_) (isLevel_lev t R) fun S hSt => ?_
    · have hk' := Finset.mem_range.mp hk
      have := (isPrim_brk hφ (dcoef F i j θA θB ρ t) ρ (2 * ((j - t : ℕ) : F)) k
        (t - k)).1.map_D_pow (t - k)
      rwa [show k + (t - k) = t from by omega] at this
    · subst hSt
      rw [lev_apply_of_card R rfl, ← h S ht]
      exact (block_apply_of_strSum θA θB ρ j hφ hΦ ht).symm
  have hbr : ∀ k s, 2 * k ≤ i → k ≤ j → s ≤ sig i j k →
      brk (dcoef F i j θA θB ρ (k + s)) ρ (2 * ((j - (k + s) : ℕ) : F)) φ k s
        = proj k (k + s) (lev (k + s) R) := by
    intro k s hk hkj hs
    have hs1 : s ≤ i - 2 * k := le_trans hs (min_le_left _ _)
    have hs2 : s ≤ j - k := le_trans hs (min_le_right _ _)
    have h1 : proj k (k + s) (∑ k' ∈ range (k + s + 1), (D ^ (k + s - k'))
        (brk (dcoef F i j θA θB ρ (k + s)) ρ (2 * ((j - (k + s) : ℕ) : F)) φ k' (k + s - k')))
        = brk (dcoef F i j θA θB ρ (k + s)) ρ (2 * ((j - (k + s) : ℕ) : F)) φ k (k + s - k) :=
      proj_decomp (F := F) (k := k) (t := k + s) (by omega) (by omega) (by omega)
        (y := fun k' => brk (dcoef F i j θA θB ρ (k + s)) ρ (2 * ((j - (k + s) : ℕ) : F)) φ k'
          (k + s - k'))
        (fun k' => isPrim_brk hφ _ _ _ k' _)
    rw [hB (k + s) (by omega), Nat.add_sub_cancel_left] at h1
    exact h1.symm
  have hsolve : ∀ k s, 2 * k ≤ i → k ≤ j → s ≤ sig i j k → φ k s = phiK θA θB ρ j R k s := by
    intro k s hk hkj hs
    funext S'
    set w : ℕ → F := fun m => if m ≤ sig i j k then φ k m S' else 0 with hw
    have hsys : trid (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)
        *ᵥ (fun m : Fin (sig i j k + 1) => w m)
          = fun m : Fin (sig i j k + 1) => proj k (k + m) (lev (k + m) R) S' := by
      funext ⟨m, hm⟩
      have hm' : m ≤ sig i j k := by omega
      rw [trid_mulVec_apply _ _ _ w (by rw [hw]; exact ite_eq_right (by omega)) hm]
      have h1 := congrFun (hbr k m hk hkj hm') S'
      rw [brk] at h1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      have hb : bK F i j k m * w (m + 1) = bK F i j k m * φ k (m + 1) S' := by
        by_cases hm1 : m + 1 ≤ sig i j k
        · rw [hw]
          simp only [ite_eq_left hm1]
        · rw [show m = sig i j k from by omega, bK_sig, zero_mul, zero_mul]
      have hwm : w m = φ k m S' := by
        rw [hw]
        simp only [ite_eq_left hm']
      rw [hb, hwm, bK_eq hk (le_trans hm' (min_le_left _ _)), dK, cK]
      by_cases h0 : m = 0
      · rw [ite_eq_left h0] at h1 ⊢
        simp only [Pi.zero_apply] at h1
        linear_combination h1
      · have hwm1 : w (m - 1) = φ k (m - 1) S' := by
          rw [hw]
          simp only [ite_eq_left (show m - 1 ≤ sig i j k from by omega)]
        rw [ite_eq_right h0] at h1 ⊢
        simp only [Pi.smul_apply, smul_eq_mul] at h1
        rw [hwm1]
        linear_combination h1
    have h2 := congrFun (mulVec_usmani_eq _ _ _ (hdet k hk hkj) hsys) ⟨s, by omega⟩
    have hws : w s = φ k s S' := by
      rw [hw]
      simp only [ite_eq_left hs]
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, usmani_apply, smul_eq_mul] at h2
    rw [hws] at h2
    rw [h2, phiK, Finset.sum_apply,
      Fin.sum_univ_eq_sum_range (fun m => usmaniEntry (dK θA θB ρ i j k) (bK F i j k) (cK ρ)
        (sig i j k + 1) s m * proj k (k + m) (lev (k + m) R) S') (sig i j k + 1),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, GK, detK]
    ring
  have hSi : S.card ≤ i := by simpa using Finset.card_le_univ S
  rw [hΦ S hS, strSum_eq hφ]
  unfold blockSol
  refine congrFun (Finset.sum_congr rfl fun k hk => ?_) S
  have hk' : k ≤ min S.card (i - S.card) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 := le_trans hk' (min_le_left _ _)
  have h2 := le_trans hk' (min_le_right _ _)
  rw [hsolve k (S.card - k) (by omega) (by omega) (le_min (by omega) (by omega))]

theorem isBlockSol_iff {θA θB ρ : F} {j : ℕ}
    (hdet : ∀ k, 2 * k ≤ i → k ≤ j → detK θA θB ρ i j k ≠ 0) (R Φ : Finset (Fin i) → F) :
    IsBlockSol θA θB ρ j R Φ ↔
      ∀ S : Finset (Fin i), S.card ≤ j → Φ S = blockSol θA θB ρ j R S := by
  refine ⟨fun h S hS => eq_blockSol_of_isBlockSol hdet h hS, fun h => ?_⟩
  have hsol := blockSol_isBlockSol hdet R
  have hΦ : ∀ S : Finset (Fin i), S.card ≤ j →
      Φ S = strSum (phiR θA θB ρ j R) S.card S := fun S hS => by
    rw [h S hS, blockSol_eq_strSum θA θB ρ j R hS]
  intro S hS
  rw [block_apply_of_strSum θA θB ρ j (isPrim_phiR θA θB ρ j R) hΦ hS, ← hsol S hS,
    block_apply_of_strSum θA θB ρ j (isPrim_phiR θA θB ρ j R)
      (fun S hS => blockSol_eq_strSum θA θB ρ j R hS) hS]

end CharZero

theorem isBlockSol_iff_of_pos [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F} {j : ℕ}
    (hρ : 0 ≤ ρ) (hδ : 0 < θA * i + θB * j) (R Φ : Finset (Fin i) → F) :
    IsBlockSol θA θB ρ j R Φ ↔
      ∀ S : Finset (Fin i), S.card ≤ j → Φ S = blockSol θA θB ρ j R S :=
  isBlockSol_iff (fun k _ _ => detK_ne_zero hρ hδ k) R Φ

end Rhone.LinearAlgebra.BooleanLatticeInverse
