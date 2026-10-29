/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Lambda
public import Rhone.LinearAlgebra.SlotDeletion.Denom

/-! # Leading denominator along the mutation-sum preserving line -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open Polynomial LinearAlgebra.Tridiag LinearAlgebra.SlotDeletion SlotDeletion
open SamplingNumerators DiagonalChain
variable {K : Type*} [CommRing K]

theorem hasTop_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial K)
    (n : ι → ℕ) (c : ι → K) (h : ∀ i ∈ s, HasTop (f i) (n i) (c i)) :
    HasTop (∏ i ∈ s, f i) (∑ i ∈ s, n i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasTop.C (1 : K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cont_linear_hasTop (d b c : ℕ → Polynomial K) (a : K)
    (hd : ∀ t, HasTop (d t) 1 a)
    (hb : ∀ t, (b t).natDegree ≤ 0) (hc : ∀ t, (c t).natDegree ≤ 0) (r : ℕ) :
    HasTop (cont d b c r) r (a ^ r) := by
  induction r using Nat.twoStepInduction with
  | zero => simpa [cont] using HasTop.C (1 : K)
  | one => simpa [cont] using hd 0
  | more r ih0 ih1 =>
    rw [cont]
    have hn : 1 + (r + 1) = r + 2 := by omega
    have hp : HasTop (d (r + 1) * cont d b c (r + 1)) (r + 2) (a * a ^ (r + 1)) :=
      by simpa only [hn] using (hd (r + 1)).mul ih1
    have hbc : HasTop (b r * c r) 0 ((b r * c r).coeff 0) :=
      ⟨natDegree_mul_le.trans (by have := hb r; have := hc r; omega), rfl⟩
    have hq := (hbc.mul ih0).raise (by omega : 0 + r < r + 2)
    have h := hp.sub hq
    simpa [pow_succ, Nat.add_comm, mul_comm] using h

theorem dcoef_lambda_hasTop (θ ρ : K) (i j t : ℕ) :
    HasTop (dcoef (Polynomial K) i j X (C θ - X) (C ρ) t) 1
      ((i : K) - j) := by
  have heq : dcoef (Polynomial K) i j X (C θ - X) (C ρ) t =
      C ((i : K) - j) * X + C (dcoef K i j 0 θ ρ t) := by
    simp only [dcoef, map_add, map_mul, map_sub, map_natCast, zero_mul,
      add_zero]
    ring
  rw [heq]
  simpa using ((HasTop.C ((i : K) - j)).mul HasTop.X).add
    ((HasTop.C (dcoef K i j 0 θ ρ t)).raise (by omega : 0 < 1))

theorem E_diagonal_lambda (θ ρ : K) (k : ℕ) :
    E (Polynomial K) k k X (C θ - X) (C ρ) = C (ED k θ ρ) := by
  rw [E_eq_cont, ED, E_eq_cont, Analysis.Rescale.cont_map]
  congr 1
  · funext t
    simp only [dcoef, map_add, map_mul, map_natCast, zero_mul, add_zero]
    ring
  · funext t
    simp [bcoef, map_ofNat]
  · funext t
    simp [ccoef]

def lambdaBlockDegree (i j : ℕ) : ℕ := if i = j then 0 else min i j + 1
def lambdaBlockTop (θ ρ : K) (i j : ℕ) : K :=
  if i = j then ED i θ ρ else ((i : K) - j) ^ (min i j + 1)

theorem E_lambda_hasTop (θ ρ : K) (i j : ℕ) :
    HasTop (E (Polynomial K) i j X (C θ - X) (C ρ))
      (lambdaBlockDegree i j) (lambdaBlockTop θ ρ i j) := by
  by_cases hij : i = j
  · subst j
    simpa [lambdaBlockDegree, lambdaBlockTop, E_diagonal_lambda] using HasTop.C (ED i θ ρ)
  · simp only [lambdaBlockDegree, lambdaBlockTop, ite_eq_right hij]
    rw [E_eq_cont]
    apply cont_linear_hasTop _ _ _ _ (dcoef_lambda_hasTop θ ρ i j)
    · intro t
      have heq : bcoef (Polynomial K) i j t = C (bcoef K i j t) :=
        by simp [bcoef, map_ofNat]
      rw [heq]
      simp
    · intro t
      have heq : ccoef (Polynomial K) (C ρ) t = C (ccoef K ρ t) := by simp [ccoef]
      rw [heq]
      simp

theorem poch_X_hasTop (n : ℕ) : HasTop (poch (X : Polynomial K) n) (n - 1) 1 := by
  have h := hasTop_prod (Finset.Ico 1 n) (fun k => (X : Polynomial K) + C (k : K))
    (fun _ => 1) (fun _ => (1 : K)) (fun k _ =>
      by simpa using HasTop.X.add ((HasTop.C (k : K)).raise (by omega : 0 < 1)))
  simpa [poch, Finset.sum_const, Nat.card_Ico] using h

theorem poch_sub_X_hasTop (θ : K) (n : ℕ) :
    HasTop (poch (C θ - X) n) (n - 1) ((-1 : K) ^ (n - 1)) := by
  have h := hasTop_prod (Finset.Ico 1 n) (fun k => C θ - X + C (k : K))
    (fun _ => 1) (fun _ => (-1 : K)) (fun k _ => by
      simpa using (((HasTop.C θ).raise (by omega : 0 < 1)).sub HasTop.X).add
        ((HasTop.C (k : K)).raise (by omega : 0 < 1)))
  simpa [poch, Finset.sum_const, Nat.card_Ico] using h

def lambdaDenominatorDegree (m : ℕ) : ℕ :=
  (m - 1) + (m - 1) +
    ∑ i ∈ Finset.Ico 2 (m + 1), ∑ j ∈ Finset.Ico 2 (m + 1), lambdaBlockDegree i j

def lambdaDenominatorConstant (m : ℕ) : K :=
  (-1 : K) ^ (m - 1) * ∏ i ∈ Finset.Ico 2 (m + 1),
    ∏ j ∈ (Finset.Ico 2 (m + 1)).erase i, ((i : K) - j) ^ (min i j + 1)

theorem row_lambda_top (θ ρ : K) (m i : ℕ) (hi : i ∈ Finset.Ico 2 (m + 1)) :
    (∏ j ∈ Finset.Ico 2 (m + 1), lambdaBlockTop θ ρ i j) =
      ED i θ ρ * ∏ j ∈ (Finset.Ico 2 (m + 1)).erase i,
        ((i : K) - j) ^ (min i j + 1) := by
  classical
  rw [← Finset.mul_prod_erase _ _ hi]
  simp only [lambdaBlockTop]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Ne.symm (Finset.mem_erase.mp hj).1)]

theorem Dfull_lambda_hasTop (θ ρ : K) (m : ℕ) :
    HasTop (Dfull X (C θ - X) (C ρ) m m) (lambdaDenominatorDegree m)
      (lambdaDenominatorConstant m * frakE m θ ρ) := by
  have hrect := hasTop_prod (Finset.Ico 2 (m + 1))
    (fun i => ∏ j ∈ Finset.Ico 2 (m + 1), E (Polynomial K) i j X (C θ - X) (C ρ))
    (fun i => ∑ j ∈ Finset.Ico 2 (m + 1), lambdaBlockDegree i j)
    (fun i => ∏ j ∈ Finset.Ico 2 (m + 1), lambdaBlockTop θ ρ i j)
    (fun i _ => hasTop_prod _ _ _ _ (fun j _ => E_lambda_hasTop θ ρ i j))
  have h := ((poch_X_hasTop (K := K) m).mul (poch_sub_X_hasTop θ m)).mul hrect
  have hprod : (∏ i ∈ Finset.Ico 2 (m + 1),
      ∏ j ∈ Finset.Ico 2 (m + 1), lambdaBlockTop θ ρ i j) =
      frakE m θ ρ * ∏ i ∈ Finset.Ico 2 (m + 1),
        ∏ j ∈ (Finset.Ico 2 (m + 1)).erase i, ((i : K) - j) ^ (min i j + 1) := by
    have hs : Finset.Ico 2 (m + 1) = Finset.Icc 2 m := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [Finset.prod_congr rfl (fun i hi => row_lambda_top θ ρ m i hi),
      Finset.prod_mul_distrib, frakE, hs]
  simpa [Dfull, Erect, lambdaDenominatorDegree, lambdaDenominatorConstant, hprod,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem lambdaDenominatorConstant_ne_zero [IsDomain K] [CharZero K] (m : ℕ) :
    lambdaDenominatorConstant (K := K) m ≠ 0 := by
  unfold lambdaDenominatorConstant
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  exact_mod_cast Ne.symm (Finset.mem_erase.mp hj).1

theorem Dfull_lambda_ne_zero [IsDomain K] [CharZero K] (θ ρ : K) (m : ℕ)
    (hE : ∀ k ∈ Finset.Icc 2 m, ED k θ ρ ≠ 0) :
    Dfull (X : Polynomial K) (C θ - X) (C ρ) m m ≠ 0 := by
  have h := (Dfull_lambda_hasTop θ ρ m).2
  have hc : lambdaDenominatorConstant (K := K) m * frakE m θ ρ ≠ 0 :=
    mul_ne_zero (lambdaDenominatorConstant_ne_zero m) (Finset.prod_ne_zero_iff.mpr hE)
  intro hz
  rw [hz, coeff_zero] at h
  exact hc h.symm

theorem Dfull_lambda_natDegree [IsDomain K] [CharZero K] (θ ρ : K) (m : ℕ)
    (hE : ∀ k ∈ Finset.Icc 2 m, ED k θ ρ ≠ 0) :
    (Dfull (X : Polynomial K) (C θ - X) (C ρ) m m).natDegree =
      lambdaDenominatorDegree m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (Dfull_lambda_hasTop θ ρ m).1
  rw [(Dfull_lambda_hasTop θ ρ m).2]
  exact mul_ne_zero (lambdaDenominatorConstant_ne_zero m)
    (Finset.prod_ne_zero_iff.mpr hE)

theorem Dfull_lambda_leadingCoeff [IsDomain K] [CharZero K] (θ ρ : K) (m : ℕ)
    (hE : ∀ k ∈ Finset.Icc 2 m, ED k θ ρ ≠ 0) :
    (Dfull (X : Polynomial K) (C θ - X) (C ρ) m m).leadingCoeff =
      lambdaDenominatorConstant m * frakE m θ ρ := by
  rw [leadingCoeff, Dfull_lambda_natDegree θ ρ m hE]
  exact (Dfull_lambda_hasTop θ ρ m).2

end Rhone.Probability.SamplingUniform
