/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalChain.Cleared
public import Rhone.LinearAlgebra.Tridiag.RhoDegree

/-! # Exact `ρ`-degrees of the cleared diagonal chain -/

@[expose] public section

namespace Rhone.Probability.DiagonalChain

open Matrix Polynomial LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation
open Analysis.RareAlleleHierarchy RareAlleleHierarchy

section Cone

variable (F : Type*) [CommRing F] [PartialOrder F] [IsOrderedRing F]

def NNc : Subsemiring (Polynomial F) where
  carrier := {p | ∀ n, 0 ≤ p.coeff n}
  zero_mem' := by intro n; simp
  one_mem' := by
    intro n
    rw [Polynomial.coeff_one]
    split_ifs <;> simp
  add_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_add]
    exact add_nonneg (hp n) (hq n)
  mul_mem' := by
    intro p q hp hq n
    rw [Polynomial.coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp x.1) (hq x.2)

variable {F}

theorem mem_NNc_iff {p : Polynomial F} : p ∈ NNc F ↔ ∀ n, 0 ≤ p.coeff n := Iff.rfl

theorem C_mem_NNc {a : F} (ha : 0 ≤ a) : Polynomial.C a ∈ NNc F := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · exact le_refl 0

theorem X_mem_NNc : (Polynomial.X : Polynomial F) ∈ NNc F := by
  intro n
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem leadingCoeff_pos_of_mem_NNc [Nontrivial F] {p : Polynomial F} (hp : p ∈ NNc F)
    (h0 : p ≠ 0) : 0 < p.leadingCoeff :=
  lt_of_le_of_ne (hp p.natDegree) (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr h0))

theorem natDegree_sum_of_mem_NNc [Nontrivial F] {ι : Type*} {s : Finset ι}
    {f : ι → Polynomial F} (hf : ∀ i ∈ s, f i ∈ NNc F) {d : ℕ}
    (hle : ∀ i ∈ s, (f i).natDegree ≤ d) {i₀ : ι} (hi₀ : i₀ ∈ s) (hne : f i₀ ≠ 0)
    (hd : (f i₀).natDegree = d) :
    (∑ i ∈ s, f i).natDegree = d ∧ (∑ i ∈ s, f i) ≠ 0 := by
  have hpos : 0 < (f i₀).coeff d := by
    rw [← hd]
    exact leadingCoeff_pos_of_mem_NNc (hf i₀ hi₀) hne
  have hsum : 0 < (∑ i ∈ s, f i).coeff d := by
    rw [Polynomial.finsetSum_coeff]
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun i hi => hf i hi d) hi₀)
  have hge : d ≤ (∑ i ∈ s, f i).natDegree := Polynomial.le_natDegree_of_ne_zero hsum.ne'
  have hle' : (∑ i ∈ s, f i).natDegree ≤ d :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ hle
  refine ⟨le_antisymm hle' hge, fun h0 => ?_⟩
  rw [h0, Polynomial.coeff_zero] at hsum
  exact lt_irrefl 0 hsum

end Cone

section Blocks

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

noncomputable def Dlead (k : ℕ) (a : F) (r : ℕ) : Polynomial F :=
  cont (dcoef (Polynomial F) k k (Polynomial.C a) 0 Polynomial.X) (bcoef (Polynomial F) k k)
    (ccoef (Polynomial F) Polynomial.X) r

noncomputable def Dtrail (k : ℕ) (a : F) (c : ℕ) : Polynomial F :=
  Qc (dcoef (Polynomial F) k k (Polynomial.C a) 0 Polynomial.X) (bcoef (Polynomial F) k k)
    (ccoef (Polynomial F) Polynomial.X) (k + 1) c

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem poly_zero_eq_C : (0 : Polynomial F) = Polynomial.C (0 : F) :=
  Polynomial.C_0.symm

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem Dlead_eq_det (k : ℕ) (a : F) (r : ℕ) :
    Dlead k a r
      = (tridFrom (dcoef (Polynomial F) k k (Polynomial.C a) (Polynomial.C (0 : F)) Polynomial.X)
          (bcoef (Polynomial F) k k) (ccoef (Polynomial F) Polynomial.X) 0 r).det := by
  rw [Dlead, poly_zero_eq_C, ← det_trid_eq_cont, ← tridFrom_zero]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem Dtrail_eq_det (k : ℕ) (a : F) {c : ℕ} (hc : c ≤ k + 1) :
    Dtrail k a c
      = (tridFrom (dcoef (Polynomial F) k k (Polynomial.C a) (Polynomial.C (0 : F)) Polynomial.X)
          (bcoef (Polynomial F) k k) (ccoef (Polynomial F) Polynomial.X) c (k + 1 - c)).det := by
  rw [Dtrail, poly_zero_eq_C, Qc_of_le _ _ _ hc]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem natDegree_Dtrail_le (k : ℕ) (a : F) {c : ℕ} (hc : c ≤ k + 1) :
    (Dtrail k a c).natDegree ≤ k + 1 - c := by
  rw [Dtrail_eq_det k a hc]
  exact (degree_and_coeff_T k k a 0 (k + 1 - c) c).1

theorem natDegree_Dtrail (k : ℕ) (a : F) {c : ℕ} (hc1 : 1 ≤ c) (hc : c ≤ k + 1) :
    (Dtrail k a c).natDegree = k + 1 - c ∧ Dtrail k a c ≠ 0 := by
  have hcoeff := (degree_and_coeff_T k k a 0 (k + 1 - c) c).2
  rw [← Dtrail_eq_det k a hc] at hcoeff
  have hne : (Dtrail k a c).coeff (k + 1 - c) ≠ 0 := by
    rw [hcoeff]
    refine Finset.prod_ne_zero_iff.2 fun u _ => ?_
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨le_antisymm (natDegree_Dtrail_le k a hc) (Polynomial.le_natDegree_of_ne_zero hne),
    fun h0 => hne ?_⟩
  rw [h0, Polynomial.coeff_zero]

theorem natDegree_Dlead_le (k : ℕ) (a : F) {r : ℕ} (hr : 1 ≤ r) :
    (Dlead k a r).natDegree ≤ r - 1 := by
  obtain ⟨hdeg, hcoeff⟩ := degree_and_coeff_T k k a 0 r 0
  rw [← Dlead_eq_det k a r] at hdeg hcoeff
  have hzero : (Dlead k a r).coeff r = 0 := by
    rw [hcoeff]
    refine Finset.prod_eq_zero (Finset.mem_range.2 (by omega : 0 < r)) ?_
    simp
  rcases Nat.lt_or_ge (Dlead k a r).natDegree r with h | h
  · omega
  · have heq : (Dlead k a r).natDegree = r := le_antisymm hdeg h
    have hlead : (Dlead k a r).leadingCoeff = 0 := by
      rw [Polynomial.leadingCoeff, heq]; exact hzero
    rw [Polynomial.leadingCoeff_eq_zero] at hlead
    rw [hlead]
    simp

theorem kappaT_diag_pos {a : F} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) : 0 < kappaT k k a 0 := by
  have hk1 : (1 : F) ≤ (k : F) := by exact_mod_cast hk
  have hkpos : (0 : F) < (k : F) := by linarith
  have h1 : (0 : F) < (k : F) * ((k : F) - 1 + a) := by nlinarith
  have h2 : (0 : F) ≤ (k : F) * ((k : F) - 1 + 0) := by nlinarith
  rw [kappaT]
  linarith

theorem natDegree_Dlead {a : F} (ha : 0 < a) (k : ℕ) (hk : 1 ≤ k) {r : ℕ} (hr : 2 ≤ r) :
    (Dlead k a r).natDegree = r - 1 ∧ Dlead k a r ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hcoeff := coeff_leading_block k k a (0 : F) m
  rw [← Dlead_eq_det k a (m + 2)] at hcoeff
  have hne : (Dlead k a (m + 2)).coeff (m + 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      (kappaT_diag_pos ha hk).ne'
  refine ⟨le_antisymm (natDegree_Dlead_le k a (by omega)) ?_, fun h0 => hne ?_⟩
  · exact Polynomial.le_natDegree_of_ne_zero (by simpa using hne)
  · rw [h0, Polynomial.coeff_zero]

theorem Dlead_one_ne_zero {a : F} (ha : 0 < a) (k : ℕ) (hk : 1 ≤ k) : Dlead k a 1 ≠ 0 := by
  have hval : Polynomial.eval 0 (Dlead k a 1)
      = (((k + k) * (k + k - 1) : ℕ) : F) + a * (k : F) + 0 * (k : F) := by
    simp [Dlead, cont, dcoef]
  intro h0
  rw [h0] at hval
  have h1 : (0 : F) ≤ (((k + k) * (k + k - 1) : ℕ) : F) := Nat.cast_nonneg _
  have h2 : (0 : F) < a * (k : F) := mul_pos ha (by exact_mod_cast hk)
  simp only [Polynomial.eval_zero, zero_mul, add_zero] at hval
  linarith

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem Dlead_zero (k : ℕ) (a : F) : Dlead k a 0 = 1 := rfl

end Blocks

section Adj

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prefactor_upper (k t u : ℕ) :
    (2 : Polynomial F) ^ (u - t)
        * (∏ s ∈ Finset.Ico t u, (((k - s) * (k - s) : ℕ) : Polynomial F))
      = ((2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k - s) * (k - s)) : ℕ) : Polynomial F) := by
  push_cast
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem adjD_upper (k : ℕ) (a : F) {t u : ℕ} (h : t ≤ u) :
    adjD k (Polynomial.C a) Polynomial.X t u
      = ((2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k - s) * (k - s)) : ℕ) : Polynomial F)
        * Dlead k a t * Dtrail k a (u + 1) := by
  rw [adjD, usmaniEntry_T_of_le k k (Polynomial.C a) 0 Polynomial.X h, min_self,
    ← prefactor_upper]
  rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem adjD_lower (k : ℕ) (a : F) {t u : ℕ} (h : u ≤ t) :
    adjD k (Polynomial.C a) Polynomial.X t u
      = Polynomial.X ^ (t - u) * (∏ s ∈ Finset.Ico u t, ((s : Polynomial F) + 1))
        * Dlead k a u * Dtrail k a (t + 1) := by
  rw [adjD, usmaniEntry_T_of_ge k k (Polynomial.C a) 0 Polynomial.X h, min_self]
  rfl

theorem natDegree_adjD_upper {a : F} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) {t u : ℕ} (h : t ≤ u)
    (hu : u ≤ k) :
    (adjD k (Polynomial.C a) Polynomial.X t u).natDegree = (t - 1) + (k - u) ∧
      adjD k (Polynomial.C a) Polynomial.X t u ≠ 0 := by
  obtain ⟨hdt, hnt⟩ : (Dtrail k a (u + 1)).natDegree = k - u ∧ Dtrail k a (u + 1) ≠ 0 := by
    have h := natDegree_Dtrail k a (by omega : 1 ≤ u + 1) (by omega)
    rw [show k + 1 - (u + 1) = k - u from by omega] at h
    exact h
  obtain ⟨hdl, hnl⟩ : (Dlead k a t).natDegree = t - 1 ∧ Dlead k a t ≠ 0 := by
    match t with
    | 0 => exact ⟨by simp, by simp⟩
    | 1 => exact ⟨by simpa using natDegree_Dlead_le k a (le_refl 1), Dlead_one_ne_zero ha k hk⟩
    | (m + 2) => exact natDegree_Dlead ha k hk (by omega)
  have hcpos : 0 < 2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k - s) * (k - s)) := by
    refine Nat.mul_pos (Nat.two_pow_pos _) (Finset.prod_pos fun s hs => ?_)
    rw [Finset.mem_Ico] at hs
    exact Nat.mul_pos (by omega) (by omega)
  have hc : ((2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k - s) * (k - s)) : ℕ) : Polynomial F)
      ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hcd : ((2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k - s) * (k - s)) : ℕ)
      : Polynomial F).natDegree = 0 := Polynomial.natDegree_natCast _
  rw [adjD_upper k a h]
  refine ⟨?_, mul_ne_zero (mul_ne_zero hc hnl) hnt⟩
  rw [Polynomial.natDegree_mul (mul_ne_zero hc hnl) hnt, Polynomial.natDegree_mul hc hnl,
    hcd, hdl, hdt, Nat.zero_add]

theorem natDegree_adjD_lower (k : ℕ) (a : F) {t u : ℕ} (h : u ≤ t) (ht : t ≤ k) :
    (adjD k (Polynomial.C a) Polynomial.X t u).natDegree ≤ (t - u) + (u - 1) + (k - t) := by
  have hprod : (∏ s ∈ Finset.Ico u t, ((s : Polynomial F) + 1)).natDegree = 0 := by
    have h1 : ∀ s ∈ Finset.Ico u t, ((s : Polynomial F) + 1).natDegree = 0 := by
      intro s _
      have hcast : ((s : Polynomial F) + 1) = ((s + 1 : ℕ) : Polynomial F) := by push_cast; ring
      rw [hcast, Polynomial.natDegree_natCast]
    refine Nat.le_zero.1 (le_trans (Polynomial.natDegree_prod_le _ _) ?_)
    rw [Finset.sum_congr rfl h1, Finset.sum_const_zero]
  have hdt : (Dtrail k a (t + 1)).natDegree ≤ k - t := by
    have h := natDegree_Dtrail_le k a (by omega : t + 1 ≤ k + 1)
    rw [show k + 1 - (t + 1) = k - t from by omega] at h
    exact h
  have hdl : (Dlead k a u).natDegree ≤ u - 1 := by
    match u with
    | 0 => simp
    | (m + 1) => exact natDegree_Dlead_le k a (by omega)
  rw [adjD_lower k a h]
  have h1 : (Polynomial.X ^ (t - u)
      * ∏ s ∈ Finset.Ico u t, ((s : Polynomial F) + 1)).natDegree ≤ t - u := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_X_pow, hprod]
    omega
  have h2 : (Polynomial.X ^ (t - u) * (∏ s ∈ Finset.Ico u t, ((s : Polynomial F) + 1))
      * Dlead k a u).natDegree ≤ (t - u) + (u - 1) :=
    le_trans (Polynomial.natDegree_mul_le) (Nat.add_le_add h1 hdl)
  exact le_trans (Polynomial.natDegree_mul_le) (Nat.add_le_add h2 hdt)

end Adj

section Degrees

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem chain_mem_NNc {a : F} (ha : 0 ≤ a) (k t : ℕ) (ht : t ≤ k) :
    clearedChain (Polynomial.C a) Polynomial.X k t ∈ NNc F :=
  clearedChain_mem (NNc F) (C_mem_NNc ha) X_mem_NNc k t ht

theorem adjD_mem_NNc {a : F} (ha : 0 ≤ a) (k : ℕ) {t u : ℕ} (ht : t ≤ k) (hu : u ≤ k) :
    adjD k (Polynomial.C a) Polynomial.X t u ∈ NNc F :=
  adjD_mem (NNc F) (C_mem_NNc ha) X_mem_NNc k ht hu

theorem clearedChain_poly_ne_zero {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) {t : ℕ}
    (ht : t ≤ k) : clearedChain (Polynomial.C a) Polynomial.X k t ≠ 0 := by
  intro h0
  have hmap := clearedChain_map (Polynomial.evalRingHom (0 : F)) (Polynomial.C a) Polynomial.X k t
  rw [h0] at hmap
  simp only [map_zero, Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X] at hmap
  exact (clearedChain_pos ha (le_refl (0 : F)) hk ht).ne' hmap.symm

theorem clearedChain_poly_ne_zero' {a : F} (ha : 0 < a) {k t : ℕ} (hk : 1 ≤ k) (ht1 : 1 ≤ t)
    (ht : t ≤ k) : clearedChain (Polynomial.C a) Polynomial.X k t ≠ 0 := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    obtain rfl : t = 1 := by omega
    simp [varthetaOne]
  · exact clearedChain_poly_ne_zero ha h ht

theorem choose_two_succ (n : ℕ) : Nat.choose (n + 1) 2 = n + Nat.choose n 2 := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]

theorem choose_two_add_two (n : ℕ) :
    Nat.choose (n + 2) 2 = (n + 1) + Nat.choose (n + 1) 2 := choose_two_succ (n + 1)

theorem natDegree_clearedChain {a : F} (ha : 0 < a) : ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, t ≤ k →
    (clearedChain (Polynomial.C a) Polynomial.X k t).natDegree
      = Nat.choose (k - 1) 2 + (t - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro h; omega
    | 1 =>
      intro _ t ht
      interval_cases t
      · simp [varthetaOne]
      · simp [varthetaOne]
    | (j + 2) =>
      intro _ t ht
      set d := Nat.choose (j + 1) 2 + (t - 1) with hd
      set f : ℕ → Polynomial F := fun u =>
        adjD (j + 2) (Polynomial.C a) Polynomial.X t u
          * diagSource (clearedChain (Polynomial.C a) Polynomial.X (j + 1)) u with hf
      have hcone : ∀ u ∈ Finset.range (j + 3), f u ∈ NNc F := by
        intro u hu
        rw [Finset.mem_range] at hu
        refine (NNc F).mul_mem (adjD_mem_NNc (le_of_lt ha) (j + 2) ht (by omega)) ?_
        rw [diagSource]
        exact (NNc F).mul_mem (natCast_mem _ _)
          (chain_mem_NNc (le_of_lt ha) (j + 1) (u - 1) (by omega))
      have hstep : ∀ u : ℕ, 2 ≤ u → u ≤ j + 2 →
          (clearedChain (Polynomial.C a) Polynomial.X (j + 1) (u - 1)).natDegree
            = Nat.choose j 2 + (u - 2) := by
        intro u hu2 hu
        have h := ih (j + 1) (by omega) (by omega) (u - 1) (by omega)
        rw [show j + 1 - 1 = j from rfl, show u - 1 - 1 = u - 2 from by omega] at h
        exact h
      have hsrcne : ∀ u : ℕ, 2 ≤ u → u ≤ j + 2 →
          diagSource (clearedChain (Polynomial.C a) Polynomial.X (j + 1)) u ≠ 0 := by
        intro u hu2 hu
        rw [diagSource]
        refine mul_ne_zero (Nat.cast_ne_zero.2 ?_) ?_
        · exact Nat.mul_ne_zero (by omega) (by omega)
        · exact clearedChain_poly_ne_zero' ha (by omega) (by omega) (by omega)
      have hsrcdeg : ∀ u : ℕ, 2 ≤ u → u ≤ j + 2 →
          (diagSource (clearedChain (Polynomial.C a) Polynomial.X (j + 1)) u).natDegree
            = Nat.choose j 2 + (u - 2) := by
        intro u hu2 hu
        rw [diagSource, Polynomial.natDegree_mul (Nat.cast_ne_zero.2
          (Nat.mul_ne_zero (by omega) (by omega)))
          (clearedChain_poly_ne_zero' ha (by omega) (by omega) (by omega)),
          Polynomial.natDegree_natCast, Nat.zero_add, hstep u hu2 hu]
      have hle : ∀ u ∈ Finset.range (j + 3), (f u).natDegree ≤ d := by
        intro u hu
        rw [Finset.mem_range] at hu
        rcases Nat.lt_or_ge u 2 with hu2 | hu2
        · have : f u = 0 := by
            rw [hf]
            simp only
            rw [diagSource, show u * (u - 1) = 0 from by interval_cases u <;> rfl]
            simp
          rw [this]
          simp
        rcases Nat.le_total t u with htu | htu
        · rw [hf]
          simp only
          rw [Polynomial.natDegree_mul (natDegree_adjD_upper ha (by omega) htu (by omega)).2
            (hsrcne u hu2 (by omega)), (natDegree_adjD_upper ha (by omega) htu (by omega)).1,
            hsrcdeg u hu2 (by omega), hd, choose_two_succ]
          omega
        · rw [hf]
          simp only
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          rw [hsrcdeg u hu2 (by omega), hd, choose_two_succ]
          have hb := natDegree_adjD_lower (j + 2) a htu ht
          omega
      have hmem : max t 2 ∈ Finset.range (j + 3) := by
        rw [Finset.mem_range]; omega
      have hattain : (f (max t 2)).natDegree = d := by
        rw [hf]
        simp only
        rw [Polynomial.natDegree_mul
            (natDegree_adjD_upper ha (by omega) (le_max_left t 2) (by omega)).2
            (hsrcne (max t 2) (le_max_right t 2) (by omega)),
          (natDegree_adjD_upper ha (by omega) (le_max_left t 2) (by omega)).1,
          hsrcdeg (max t 2) (le_max_right t 2) (by omega), hd, choose_two_succ]
        omega
      have hne : f (max t 2) ≠ 0 :=
        mul_ne_zero (natDegree_adjD_upper ha (by omega) (le_max_left t 2) (by omega)).2
          (hsrcne (max t 2) (le_max_right t 2) (by omega))
      rw [clearedChain_succ_succ, clearedStep_eq_range]
      exact (natDegree_sum_of_mem_NNc hcone hle hmem hne hattain).1

theorem natDegree_W {a : F} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    (W k (Polynomial.C a) Polynomial.X).natDegree = Nat.choose (k - 1) 2 := by
  rw [W, natDegree_clearedChain ha k hk 0 (Nat.zero_le k)]
  simp

theorem W_poly_ne_zero {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    W k (Polynomial.C a) Polynomial.X ≠ 0 :=
  clearedChain_poly_ne_zero ha hk (Nat.zero_le k)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem ED_eq_EC (p : ℕ) (a : F) :
    ED p (Polynomial.C a) Polynomial.X
      = E (Polynomial F) p p (Polynomial.C a) (Polynomial.C (0 : F)) Polynomial.X := by
  rw [ED, poly_zero_eq_C]

theorem ED_poly_ne_zero {a : F} (ha : 0 < a) {p : ℕ} (hp : 1 ≤ p) :
    ED p (Polynomial.C a) Polynomial.X ≠ 0 := by
  rw [ED_eq_EC]
  exact E_ne_zero p p a 0 (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (kappaT_diag_pos ha hp).ne')

theorem natDegree_ED {a : F} (ha : 0 < a) {p : ℕ} (hp : 1 ≤ p) :
    (ED p (Polynomial.C a) Polynomial.X).natDegree = p := by
  rw [ED_eq_EC]
  have h := natDegree_E p p a (0 : F) (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (kappaT_diag_pos ha hp).ne')
  rwa [min_self] at h

theorem sum_Icc_two (k : ℕ) : (∑ p ∈ Finset.Icc 2 k, p) = Nat.choose (k + 1) 2 - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · obtain rfl : n = 0 := by omega
      simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih, choose_two_succ (n + 1), choose_two_succ n]
      have : 1 ≤ n + Nat.choose n 2 := by omega
      omega

theorem natDegree_frakE {a : F} (ha : 0 < a) (k : ℕ) :
    (frakE k (Polynomial.C a) Polynomial.X).natDegree = Nat.choose (k + 1) 2 - 1 := by
  rw [frakE, Polynomial.natDegree_prod _ _ (fun p hp => ED_poly_ne_zero ha
    (by rw [Finset.mem_Icc] at hp; omega))]
  rw [Finset.sum_congr rfl (fun p hp => natDegree_ED ha
    (by rw [Finset.mem_Icc] at hp; omega : 1 ≤ p))]
  exact sum_Icc_two k

theorem frakE_poly_ne_zero {a : F} (ha : 0 < a) (k : ℕ) :
    frakE k (Polynomial.C a) Polynomial.X ≠ 0 := by
  rw [frakE]
  exact Finset.prod_ne_zero_iff.2 fun p hp =>
    ED_poly_ne_zero ha (by rw [Finset.mem_Icc] at hp; omega)

theorem degInfty_vartheta_zero {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    ((W k (Polynomial.C a) Polynomial.X).natDegree : ℤ)
        - ((frakE k (Polynomial.C a) Polynomial.X).natDegree : ℤ)
      = 2 - 2 * (k : ℤ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [natDegree_W ha (by omega), natDegree_frakE ha]
  have h1 : Nat.choose (j + 2 + 1) 2 = (j + 2) + ((j + 1) + Nat.choose (j + 1) 2) := by
    rw [choose_two_succ (j + 2), choose_two_add_two j]
  have h2 : Nat.choose (j + 2 - 1) 2 = Nat.choose (j + 1) 2 := by norm_num
  have h3 : Nat.choose (j + 2 + 1) 2 - 1 = (2 * j + 2) + Nat.choose (j + 1) 2 := by omega
  rw [h2, h3]
  push_cast
  ring

theorem natDegree_W_add_two_le {a : F} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) :
    (W k (Polynomial.C a) Polynomial.X).natDegree + 2
      ≤ (frakE k (Polynomial.C a) Polynomial.X).natDegree := by
  have h := degInfty_vartheta_zero ha hk
  have hk' : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  omega

end Degrees

end Rhone.Probability.DiagonalChain
