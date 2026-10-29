/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.NonnegativeCoefficients
public import Rhone.Probability.RareAlleleHierarchy.Lambda
public import Rhone.Analysis.Rescale.Rescale
public import Rhone.Probability.SlotDeletion.Matrix
public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive

/-! # Subtraction-free cleared diagonal chain -/

@[expose] public section

namespace Rhone.Probability.DiagonalChain

open Matrix LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation
open Analysis.RareAlleleHierarchy RareAlleleHierarchy

section Defs

variable {S : Type*} [CommRing S]

def adjD (k : ℕ) (θ ρ : S) (t u : ℕ) : S :=
  usmaniEntry (dcoef S k k θ 0 ρ) (bcoef S k k) (ccoef S ρ) (min k k + 1) t u

def ED (k : ℕ) (θ ρ : S) : S := E S k k θ 0 ρ

def frakE (k : ℕ) (θ ρ : S) : S := ∏ p ∈ Finset.Icc 2 k, ED p θ ρ

def clearedStep (k : ℕ) (θ ρ : S) (w : ℕ → S) (t : ℕ) : S :=
  ∑ u ∈ Finset.range (min k k + 1), adjD k θ ρ t u * diagSource w u

noncomputable def clearedChain (θ ρ : S) : ℕ → ℕ → S
  | 0 => fun _ => 0
  | 1 => varthetaOne
  | (k + 2) => clearedStep (k + 2) θ ρ (clearedChain θ ρ (k + 1))

noncomputable def W (k : ℕ) (θ ρ : S) : S := clearedChain θ ρ k 0

@[simp] theorem clearedChain_one (θ ρ : S) : clearedChain θ ρ 1 = varthetaOne := rfl

@[simp] theorem clearedChain_succ_succ (θ ρ : S) (k : ℕ) :
    clearedChain θ ρ (k + 2) = clearedStep (k + 2) θ ρ (clearedChain θ ρ (k + 1)) := rfl

theorem clearedChain_step (θ ρ : S) {k : ℕ} (hk : 2 ≤ k) :
    clearedChain θ ρ k = clearedStep k θ ρ (clearedChain θ ρ (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rfl

theorem clearedStep_eq_range (k : ℕ) (θ ρ : S) (w : ℕ → S) (t : ℕ) :
    clearedStep k θ ρ w t = ∑ u ∈ Finset.range (k + 1), adjD k θ ρ t u * diagSource w u := by
  rw [clearedStep, min_self]

@[simp] theorem frakE_one (θ ρ : S) : frakE 1 θ ρ = 1 := by
  rw [frakE, Finset.Icc_eq_empty (by omega), Finset.prod_empty]

theorem frakE_succ (θ ρ : S) (k : ℕ) (hk : 1 ≤ k) :
    frakE (k + 1) θ ρ = frakE k θ ρ * ED (k + 1) θ ρ := by
  rw [frakE, frakE, Finset.prod_Icc_succ_top (by omega)]

theorem dcoef_diag_eq (k : ℕ) (θ ρ : S) (t : ℕ) :
    dcoef S k k θ 0 ρ t = dcoefS S k k ((k : S) * θ) ρ t := by
  simp only [dcoef, dcoefS]
  ring

end Defs

section Mem

variable {S : Type*} [CommRing S] (A : Subsemiring S) {θ ρ : S}

theorem adjD_mem (hθ : θ ∈ A) (hρ : ρ ∈ A) (k : ℕ) {t u : ℕ} (ht : t ≤ k) (hu : u ≤ k) :
    adjD k θ ρ t u ∈ A :=
  Analysis.RecombinationExpansion.usmaniEntry_mem A hθ A.zero_mem hρ k k
      (by simpa using ht) (by simpa using hu)

theorem ED_mem (hθ : θ ∈ A) (hρ : ρ ∈ A) (k : ℕ) : ED k θ ρ ∈ A :=
  Analysis.RecombinationExpansion.E_mem A hθ A.zero_mem hρ k k

theorem frakE_mem (hθ : θ ∈ A) (hρ : ρ ∈ A) (k : ℕ) : frakE k θ ρ ∈ A :=
  A.prod_mem fun p _ => ED_mem A hθ hρ p

theorem clearedChain_mem (hθ : θ ∈ A) (hρ : ρ ∈ A) :
    ∀ k : ℕ, ∀ t : ℕ, t ≤ k → clearedChain θ ρ k t ∈ A := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => exact fun _ _ => A.zero_mem
    | 1 =>
      intro t _
      rw [clearedChain_one, varthetaOne]
      split_ifs
      · exact A.one_mem
      · exact A.zero_mem
    | (j + 2) =>
      intro t ht
      rw [clearedChain_succ_succ, clearedStep_eq_range]
      refine A.sum_mem fun u hu => ?_
      rw [Finset.mem_range] at hu
      refine A.mul_mem (adjD_mem A hθ hρ (j + 2) ht (by omega)) ?_
      rw [diagSource]
      exact A.mul_mem (natCast_mem A _) (ih (j + 1) (by omega) (u - 1) (by omega))

theorem W_mem (hθ : θ ∈ A) (hρ : ρ ∈ A) (k : ℕ) : W k θ ρ ∈ A :=
  clearedChain_mem A hθ hρ k 0 (Nat.zero_le k)

end Mem

section OffBlock

variable {S : Type*} [CommRing S]

theorem adjD_eq_zero_of_gt (k : ℕ) (θ ρ : S) {t : ℕ} (ht : k < t) (u : ℕ) :
    adjD k θ ρ t u = 0 := by
  rw [adjD]
  rcases Nat.le_total t u with h | h
  · rw [usmaniEntry_of_le _ _ _ _ h, Qc_of_gt _ _ _ (by omega), mul_zero]
  · rw [usmaniEntry_of_ge _ _ _ _ h, Qc_of_gt _ _ _ (by omega), mul_zero]

theorem clearedChain_eq_zero_of_gt {k : ℕ} (hk : 2 ≤ k) (θ ρ : S) {t : ℕ} (ht : k < t) :
    clearedChain θ ρ k t = 0 := by
  rw [clearedChain_step θ ρ hk, clearedStep_eq_range]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [adjD_eq_zero_of_gt k θ ρ ht u, zero_mul]

end OffBlock

section System

variable {S : Type*} [CommRing S] (θ ρ : S)

theorem clearedChain_eq_mulVec {k : ℕ} (hk : 2 ≤ k) :
    (fun p : Fin (min k k + 1) => clearedChain θ ρ k (p : ℕ))
      = U S k k θ 0 ρ *ᵥ fun p : Fin (min k k + 1) =>
          diagSource (clearedChain θ ρ (k - 1)) (p : ℕ) := by
  funext p
  rw [clearedChain_step θ ρ hk, clearedStep]
  simp only [Matrix.mulVec, dotProduct, U_apply]
  exact (Fin.sum_univ_eq_sum_range
    (fun u => adjD k θ ρ (p : ℕ) u * diagSource (clearedChain θ ρ (k - 1)) u)
    (min k k + 1)).symm

theorem trid_mul_clearedChain {k : ℕ} (hk : 2 ≤ k) {t : ℕ} (ht : t ≤ k) :
    dcoef S k k θ 0 ρ t * clearedChain θ ρ k t
        - 2 * (((k - t) * (k - t) : ℕ) : S) * clearedChain θ ρ k (t + 1)
        - ρ * (t : S) * clearedChain θ ρ k (t - 1)
      = ED k θ ρ * diagSource (clearedChain θ ρ (k - 1)) t := by
  have hp : t < min k k + 1 := by omega
  have hmv := congrArg (fun x => T S k k θ 0 ρ *ᵥ x) (clearedChain_eq_mulVec θ ρ hk)
  simp only [Matrix.mulVec_mulVec, T_mul_U, Matrix.smul_mulVec, Matrix.one_mulVec] at hmv
  have h := congrFun hmv ⟨t, hp⟩
  rw [SlotDeletion.T_mulVec_apply k k θ 0 ρ (fun s => clearedChain θ ρ k s) ⟨t, hp⟩] at h
  simpa [ED] using h

theorem adj_dot_source {ϑ : ℕ → ℕ → S} (hc : IsDiagChain θ ρ ϑ) {k : ℕ} (hk : 2 ≤ k)
    {t : ℕ} (ht : t ≤ k) :
    (∑ u ∈ Finset.range (k + 1), adjD k θ ρ t u * diagSource (ϑ (k - 1)) u)
      = ED k θ ρ * ϑ k t := by
  have hrow : T S k k θ 0 ρ *ᵥ (fun p : Fin (min k k + 1) => ϑ k (p : ℕ))
      = fun p : Fin (min k k + 1) => diagSource (ϑ (k - 1)) (p : ℕ) := by
    funext p
    have hple : (p : ℕ) ≤ k := by have := p.isLt; omega
    rw [SlotDeletion.T_mulVec_apply k k θ 0 ρ (fun s => ϑ k s) p, dcoef_diag_eq]
    exact hc.2 k hk (p : ℕ) hple
  have hU := congrArg (fun x => U S k k θ 0 ρ *ᵥ x) hrow
  simp only [Matrix.mulVec_mulVec, U_mul_T, Matrix.smul_mulVec, Matrix.one_mulVec] at hU
  have hp : t < min k k + 1 := by omega
  have h := congrFun hU ⟨t, hp⟩
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, U_apply] at h
  have h2 : (∑ i : Fin (min k k + 1), adjD k θ ρ t (i : ℕ) * diagSource (ϑ (k - 1)) (i : ℕ))
      = ED k θ ρ * ϑ k t := h.symm
  rwa [Fin.sum_univ_eq_sum_range
    (fun u => adjD k θ ρ t u * diagSource (ϑ (k - 1)) u) (min k k + 1), min_self] at h2

theorem clearedChain_eq_frakE_mul {ϑ : ℕ → ℕ → S} (hc : IsDiagChain θ ρ ϑ) :
    ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, t ≤ k → clearedChain θ ρ k t = frakE k θ ρ * ϑ k t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro h; omega
    | 1 =>
      intro _ t _
      rw [clearedChain_one, frakE_one, one_mul, hc.1 t]
    | (j + 2) =>
      intro _ t ht
      have hsrc : ∀ u : ℕ, u ≤ j + 2 → diagSource (clearedChain θ ρ (j + 1)) u
          = frakE (j + 1) θ ρ * diagSource (ϑ (j + 1)) u := by
        intro u hu
        rw [diagSource, diagSource, ih (j + 1) (by omega) (by omega) (u - 1) (by omega)]
        ring
      rw [clearedChain_succ_succ, clearedStep_eq_range]
      have hrw : ∀ u ∈ Finset.range (j + 3),
          adjD (j + 2) θ ρ t u * diagSource (clearedChain θ ρ (j + 1)) u
            = frakE (j + 1) θ ρ * (adjD (j + 2) θ ρ t u * diagSource (ϑ (j + 1)) u) := by
        intro u hu
        rw [Finset.mem_range] at hu
        rw [hsrc u (by omega)]
        ring
      have hkey : (∑ u ∈ Finset.range (j + 3), adjD (j + 2) θ ρ t u * diagSource (ϑ (j + 1)) u)
          = ED (j + 2) θ ρ * ϑ (j + 2) t :=
        adj_dot_source θ ρ hc (by omega : 2 ≤ j + 2) ht
      rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, hkey, frakE_succ θ ρ (j + 1) (by omega)]
      ring

@[simp] theorem clearedChain_zero (t : ℕ) : clearedChain θ ρ 0 t = 0 := rfl

end System

abbrev Pol2 : Type := MvPolynomial (Fin 2) ℤ

noncomputable def th : Pol2 := MvPolynomial.X 0

noncomputable def rh : Pol2 := MvPolynomial.X 1

noncomputable def NN2 : Subsemiring Pol2 :=
  (MvPolynomial.map (Nat.castRingHom ℤ)).rangeS

theorem coeff_nonneg_of_mem_NN2 {p : Pol2} (hp : p ∈ NN2) (m : Fin 2 →₀ ℕ) :
    0 ≤ p.coeff m := by
  obtain ⟨q, rfl⟩ := RingHom.mem_rangeS.1 hp
  rw [MvPolynomial.coeff_map]
  exact Int.natCast_nonneg _

theorem th_mem_NN2 : th ∈ NN2 := ⟨MvPolynomial.X 0, MvPolynomial.map_X _ _⟩

theorem rh_mem_NN2 : rh ∈ NN2 := ⟨MvPolynomial.X 1, MvPolynomial.map_X _ _⟩

theorem clearedChain_mem_NN (k t : ℕ) (ht : t ≤ k) : clearedChain th rh k t ∈ NN2 :=
  clearedChain_mem NN2 th_mem_NN2 rh_mem_NN2 k t ht

theorem clearedChain_coeff_nonneg (k t : ℕ) (ht : t ≤ k) (m : Fin 2 →₀ ℕ) :
    0 ≤ (clearedChain th rh k t).coeff m :=
  coeff_nonneg_of_mem_NN2 (clearedChain_mem_NN k t ht) m

theorem W_mem_NN (k : ℕ) : W k th rh ∈ NN2 := W_mem NN2 th_mem_NN2 rh_mem_NN2 k

theorem W_coeff_nonneg (k : ℕ) (m : Fin 2 →₀ ℕ) :
    0 ≤ (W k th rh).coeff m :=
  coeff_nonneg_of_mem_NN2 (W_mem_NN k) m

section Ordered

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] {θ ρ : R}

theorem clearedChain_nonneg (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (k t : ℕ) (ht : t ≤ k) :
    0 ≤ clearedChain θ ρ k t :=
  clearedChain_mem (Subsemiring.nonneg R) hθ hρ k t ht

theorem W_nonneg (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (k : ℕ) : 0 ≤ W k θ ρ :=
  W_mem (Subsemiring.nonneg R) hθ hρ k

end Ordered

section Positivity

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {θ ρ : R}

theorem pos_of_mul_pos_left {a b : R} (ha : 0 < a) (hab : 0 < a * b) : 0 < b := by
  by_contra hb
  simp only [not_lt] at hb
  nlinarith

theorem dcoef_diag_pos (hθ : 0 < θ) (hρ : 0 ≤ ρ) {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    0 < dcoef R k k θ 0 ρ t := by
  have h1 : (0 : R) ≤ (((k + k - t) * (k + k - t - 1) : ℕ) : R) := Nat.cast_nonneg _
  have h2 : (0 : R) < θ * (k : R) := mul_pos hθ (by exact_mod_cast hk)
  have h3 : (0 : R) ≤ ρ * (t : R) := mul_nonneg hρ (Nat.cast_nonneg _)
  simp only [dcoef, zero_mul, add_zero]
  linarith

theorem clearedChain_top_pos (hθ : 0 < θ) (hρ : 0 ≤ ρ) :
    ∀ k : ℕ, 1 ≤ k → 0 < clearedChain θ ρ k k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [varthetaOne]
    · have hk : 2 ≤ n + 1 := by omega
      have hprev := ih hn
      have hrow := trid_mul_clearedChain θ ρ hk (le_refl (n + 1))
      rw [show n + 1 - (n + 1) = 0 from by omega] at hrow
      simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero] at hrow
      have hE : 0 < ED (n + 1) θ ρ := LinearAlgebra.GaloisDegreeSeven.E_pos hk hk (le_of_lt hθ)
          (le_refl 0) hρ
      have hsrc : 0 < diagSource (clearedChain θ ρ (n + 1 - 1)) (n + 1) := by
        rw [diagSource, show n + 1 - 1 = n from rfl]
        refine mul_pos ?_ hprev
        have : 0 < (n + 1) * (n + 1 - 1) := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast this
      have hlow : 0 ≤ ρ * ((n + 1 : ℕ) : R) * clearedChain θ ρ (n + 1) (n + 1 - 1) :=
        mul_nonneg (mul_nonneg hρ (Nat.cast_nonneg _))
          (clearedChain_nonneg (le_of_lt hθ) hρ (n + 1) (n + 1 - 1) (by omega))
      have hd := dcoef_diag_pos (R := R) hθ hρ (by omega : 1 ≤ n + 1) (n + 1)
      refine pos_of_mul_pos_left hd ?_
      nlinarith [mul_pos hE hsrc]

theorem clearedChain_pos (hθ : 0 < θ) (hρ : 0 ≤ ρ) {k : ℕ} (hk : 2 ≤ k) {t : ℕ} (ht : t ≤ k) :
    0 < clearedChain θ ρ k t := by
  have hE : 0 < ED k θ ρ := LinearAlgebra.GaloisDegreeSeven.E_pos hk hk (le_of_lt hθ) (le_refl 0) hρ
  have hdown : ∀ d : ℕ, d ≤ k → 0 < clearedChain θ ρ k (k - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using clearedChain_top_pos hθ hρ k (by omega)
    | succ e ihe =>
      intro he
      have hnext : 0 < clearedChain θ ρ k (k - e) := ihe (by omega)
      have hidx : k - (e + 1) + 1 = k - e := by omega
      have hrow := trid_mul_clearedChain θ ρ hk (show k - (e + 1) ≤ k by omega)
      rw [hidx] at hrow
      have hsrc : 0 ≤ diagSource (clearedChain θ ρ (k - 1)) (k - (e + 1)) := by
        rw [diagSource]
        exact mul_nonneg (Nat.cast_nonneg _)
          (clearedChain_nonneg (le_of_lt hθ) hρ (k - 1) _ (by omega))
      have hlow : 0 ≤ ρ * ((k - (e + 1) : ℕ) : R) * clearedChain θ ρ k (k - (e + 1) - 1) :=
        mul_nonneg (mul_nonneg hρ (Nat.cast_nonneg _))
          (clearedChain_nonneg (le_of_lt hθ) hρ k _ (by omega))
      have hup : 0 < 2 * (((k - (k - (e + 1))) * (k - (k - (e + 1))) : ℕ) : R)
          * clearedChain θ ρ k (k - e) := by
        refine mul_pos ?_ hnext
        have hpos : 0 < (k - (k - (e + 1))) * (k - (k - (e + 1))) :=
          Nat.mul_pos (by omega) (by omega)
        have : (0 : R) < (((k - (k - (e + 1))) * (k - (k - (e + 1))) : ℕ) : R) := by
          exact_mod_cast hpos
        linarith
      have hd := dcoef_diag_pos (R := R) hθ hρ (by omega : 1 ≤ k) (k - (e + 1))
      refine pos_of_mul_pos_left hd ?_
      nlinarith [mul_nonneg (le_of_lt hE) hsrc]
  have hpt := hdown (k - t) (by omega)
  rwa [show k - (k - t) = t from by omega] at hpt

theorem clearedChain_ne_zero (hθ : 0 < θ) (hρ : 0 ≤ ρ) {k : ℕ} (hk : 2 ≤ k) {t : ℕ}
    (ht : t ≤ k) : clearedChain θ ρ k t ≠ 0 :=
  (clearedChain_pos hθ hρ hk ht).ne'

theorem W_pos (hθ : 0 < θ) (hρ : 0 ≤ ρ) {k : ℕ} (hk : 2 ≤ k) : 0 < W k θ ρ :=
  clearedChain_pos hθ hρ hk (Nat.zero_le k)

end Positivity

section Naturality

variable {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S')

theorem Qc_map (d b c : ℕ → S) (n s : ℕ) :
    f (Qc d b c n s) = Qc (fun t => f (d t)) (fun t => f (b t)) (fun t => f (c t)) n s := by
  rw [Qc, Qc]
  split_ifs with h
  · rw [RingHom.map_det]
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, tridFrom_apply, tridEntry]
    split_ifs <;> simp
  · exact map_zero f

theorem usmaniEntry_map (d b c : ℕ → S) (n i j : ℕ) :
    f (usmaniEntry d b c n i j)
      = usmaniEntry (fun t => f (d t)) (fun t => f (b t)) (fun t => f (c t)) n i j := by
  have hprod : ∀ (g : ℕ → S) (lo hi : ℕ),
      f (runProd g lo hi) = runProd (fun t => f (g t)) lo hi := by
    intro g lo hi
    rw [runProd, runProd, map_prod]
  rw [usmaniEntry, usmaniEntry]
  split_ifs
  · rw [map_mul, map_mul, map_mul, map_pow, map_neg, map_one, hprod,
      Analysis.Rescale.cont_map f, Qc_map f]
  · rw [map_mul, map_mul, map_mul, map_pow, map_neg, map_one, hprod,
      Analysis.Rescale.cont_map f, Qc_map f]

theorem adjD_map (k : ℕ) (θ ρ : S) (t u : ℕ) :
    f (adjD k θ ρ t u) = adjD k (f θ) (f ρ) t u := by
  rw [adjD, adjD, usmaniEntry_map f]
  congr 1
  · funext s; simp [dcoef]
  · funext s; simp [bcoef, map_ofNat]
  · funext s; simp [ccoef]

theorem ED_map (k : ℕ) (θ ρ : S) : f (ED k θ ρ) = ED k (f θ) (f ρ) := by
  rw [ED, ED, E_map f]
  simp

theorem frakE_map (k : ℕ) (θ ρ : S) : f (frakE k θ ρ) = frakE k (f θ) (f ρ) := by
  rw [frakE, frakE, map_prod]
  exact Finset.prod_congr rfl fun p _ => ED_map f p θ ρ

theorem clearedChain_map (θ ρ : S) : ∀ k t : ℕ,
    f (clearedChain θ ρ k t) = clearedChain (f θ) (f ρ) k t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro t; rw [clearedChain_zero, clearedChain_zero, map_zero]
    | 1 =>
      intro t
      simp only [clearedChain_one, varthetaOne]
      split_ifs
      · exact map_one f
      · exact map_zero f
    | (j + 2) =>
      intro t
      rw [clearedChain_succ_succ, clearedChain_succ_succ, clearedStep_eq_range,
        clearedStep_eq_range, map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [map_mul, adjD_map f, diagSource, diagSource, map_mul, map_natCast,
        ih (j + 1) (by omega)]

theorem W_map (k : ℕ) (θ ρ : S) : f (W k θ ρ) = W k (f θ) (f ρ) :=
  clearedChain_map f θ ρ k 0

end Naturality

end Rhone.Probability.DiagonalChain
