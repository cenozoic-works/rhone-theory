/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Duality
public import Rhone.MarkovChain.CanningsCountChain
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Sum

/-!
# Block-counting duality for a general neutral Cannings model

Source: mohle1999, Thm 1; etheridge2011, sec. 3.2. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Polynomial Matrix MarkovChain

noncomputable def familyPoly (a : ℕ) : ℕ[X] :=
  ∑ m ∈ range a, (a.choose (m + 1) : ℕ[X]) * X ^ (m + 1)

theorem X_add_one_pow_eq (a : ℕ) : (X + 1 : ℕ[X]) ^ a = 1 + familyPoly a := by
  rw [add_pow, sum_range_succ', familyPoly, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, mul_comm]

noncomputable def familyHit {N : ℕ} (v : Fin N → ℕ) (P : Finset (Fin N)) (n : ℕ) : ℕ :=
  (∏ k ∈ P, familyPoly (v k)).coeff n

theorem sum_powerset_familyHit {N : ℕ} (v : Fin N → ℕ) (I : Finset (Fin N)) (n : ℕ) :
    ∑ P ∈ I.powerset, familyHit v P n = (∑ k ∈ I, v k).choose n := by
  rw [← Nat.cast_id ((∑ k ∈ I, v k).choose n), ← coeff_X_add_one_pow ℕ, ← prod_pow_eq_pow_sum]
  simp only [X_add_one_pow_eq, prod_one_add, finsetSum_coeff, familyHit]

theorem familyHit_perm {N : ℕ} (v : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) (P : Finset (Fin N))
    (n : ℕ) : familyHit (fun k => v (σ k)) P n = familyHit v (P.map σ.toEmbedding) n := by
  simp only [familyHit, prod_map, Equiv.coe_toEmbedding]

theorem exists_perm_map_eq {N : ℕ} {P Q : Finset (Fin N)} (h : #P = #Q) :
    ∃ σ : Equiv.Perm (Fin N), P.map σ.toEmbedding = Q := by
  classical
  have h1 : Fintype.card {x // x ∈ P} = Fintype.card {x // x ∈ Q} := by simp [h]
  have h2 : Fintype.card {x // ¬ x ∈ P} = Fintype.card {x // ¬ x ∈ Q} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h]
  let e₁ := Fintype.equivOfCardEq h1
  let e₂ := Fintype.equivOfCardEq h2
  let σ : Equiv.Perm (Fin N) :=
    ((Equiv.sumCompl (fun x => x ∈ P)).symm.trans (Equiv.sumCongr e₁ e₂)).trans
      (Equiv.sumCompl (fun x => x ∈ Q))
  refine ⟨σ, eq_of_subset_of_card_le ?_ (by rw [card_map, h])⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
  have : σ x = (e₁ ⟨x, hx⟩ : Fin N) := by
    simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
  rw [Equiv.coe_toEmbedding, this]
  exact (e₁ ⟨x, hx⟩).2

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

noncomputable def sampleHit (M : CanningsModel N Ω) (n : ℕ) (P : Finset (Fin N)) : ℝ :=
  ∑ ω, M.w ω * (familyHit (M.ν ω) P n : ℝ)

theorem sampleHit_nonneg (M : CanningsModel N Ω) (n : ℕ) (P : Finset (Fin N)) :
    0 ≤ sampleHit M n P :=
  sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (Nat.cast_nonneg _)

/-- Source: cannings1974, sec. 3. -/
theorem sampleHit_map (M : CanningsModel N Ω) (n : ℕ) (σ : Equiv.Perm (Fin N))
    (P : Finset (Fin N)) : sampleHit M n (P.map σ.toEmbedding) = sampleHit M n P := by
  have h := M.exchangeable σ (fun v => (familyHit v P n : ℝ))
  unfold sampleHit
  rw [← h]
  refine sum_congr rfl fun ω _ => ?_
  rw [familyHit_perm (M.ν ω) σ P n]

/-- Source: cannings1974, sec. 3. -/
theorem sampleHit_eq_of_card_eq (M : CanningsModel N Ω) (n : ℕ) {P Q : Finset (Fin N)}
    (h : #P = #Q) : sampleHit M n P = sampleHit M n Q := by
  obtain ⟨σ, rfl⟩ := exists_perm_map_eq h
  exact (sampleHit_map M n σ P).symm

def firstParents (N m : ℕ) : Finset (Fin N) := univ.filter fun k : Fin N => k.val < m

theorem card_firstParents {m : ℕ} (hm : m ≤ N) : #(firstParents N m) = m := by
  rw [firstParents, Fin.card_filter_val_lt, min_eq_right hm]

/-- Source: cannings1974, sec. 3. -/
theorem sampleHit_eq_firstParents (M : CanningsModel N Ω) (n : ℕ) (P : Finset (Fin N)) :
    sampleHit M n P = sampleHit M n (firstParents N #P) := by
  refine sampleHit_eq_of_card_eq M n ?_
  rw [card_firstParents]
  simpa using card_le_univ P

theorem sum_powerset_sampleHit (M : CanningsModel N Ω) (n : ℕ) (I : Finset (Fin N)) :
    ∑ P ∈ I.powerset, sampleHit M n P = ∑ ω, M.w ω * ((∑ k ∈ I, M.ν ω k).choose n : ℝ) := by
  simp only [sampleHit]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [← mul_sum, ← sum_powerset_familyHit, Nat.cast_sum]

theorem sum_fin_sum_powersetCard (f : Finset (Fin N) → ℝ) :
    ∑ m : Fin (N + 1), ∑ P ∈ powersetCard (m : ℕ) (univ : Finset (Fin N)), f P
      = ∑ P ∈ (univ : Finset (Fin N)).powerset, f P := by
  calc ∑ m : Fin (N + 1), ∑ P ∈ powersetCard (m : ℕ) (univ : Finset (Fin N)), f P
      = ∑ m : Fin (N + 1), ∑ P ∈ (univ : Finset (Fin N)).powerset,
          if #P = (m : ℕ) then f P else 0 := by
        refine sum_congr rfl fun m _ => ?_
        rw [powersetCard_eq_filter, sum_filter]
    _ = ∑ P ∈ (univ : Finset (Fin N)).powerset, ∑ m : Fin (N + 1),
          if #P = (m : ℕ) then f P else 0 := sum_comm
    _ = ∑ P ∈ (univ : Finset (Fin N)).powerset, f P := by
        refine sum_congr rfl fun P _ => ?_
        have hP : #P < N + 1 := Nat.lt_succ_of_le (by simpa using card_le_univ P)
        rw [Fintype.sum_eq_single ⟨#P, hP⟩]
        · simp
        · intro m hm
          exact ite_eq_right_iff.2 fun h => absurd (Fin.ext h.symm) hm

theorem choose_pos_of_fin (n : Fin (N + 1)) : (0 : ℝ) < (N.choose n : ℝ) := by
  exact_mod_cast Nat.choose_pos (Fin.is_le n)

noncomputable def canningsAncestralChain (M : CanningsModel N Ω) : FinChain (Fin (N + 1)) where
  P n m := (∑ P ∈ powersetCard (m : ℕ) (univ : Finset (Fin N)), sampleHit M n P)
    / (N.choose n : ℝ)
  nonneg n m := div_nonneg (sum_nonneg fun P _ => sampleHit_nonneg M n P) (Nat.cast_nonneg _)
  row_sum n := by
    rw [← sum_div, sum_fin_sum_powersetCard, sum_powerset_sampleHit]
    simp only [M.sum_ν, ← sum_mul, M.sum_w, one_mul]
    exact div_self (choose_pos_of_fin n).ne'

theorem canningsAncestralChain_apply (M : CanningsModel N Ω) (n m : Fin (N + 1)) :
    (canningsAncestralChain M).P n m
      = (N.choose m : ℝ) * sampleHit M n (firstParents N m) / (N.choose n : ℝ) := by
  change (∑ P ∈ powersetCard (m : ℕ) (univ : Finset (Fin N)), sampleHit M n P) / _ = _
  have h : ∀ P ∈ powersetCard (m : ℕ) (univ : Finset (Fin N)),
      sampleHit M n P = sampleHit M n (firstParents N m) := by
    intro P hP
    rw [sampleHit_eq_firstParents, (mem_powersetCard.1 hP).2]
  rw [sum_congr rfl h, sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

noncomputable def canningsHypergeom (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i n => ((i : ℕ).choose n : ℝ) / (N.choose n : ℝ)

theorem sum_firstParents_lt (M : CanningsModel N Ω) (m : ℕ) (ω : Ω) :
    ∑ k ∈ firstParents N m, M.ν ω k < N + 1 := by
  have h : (∑ k ∈ firstParents N m, M.ν ω k) ≤ ∑ k : Fin N, M.ν ω k :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
  have := M.sum_ν ω
  omega

/-- Source: cannings1974, sec. 3. -/
theorem countKernel_mul_apply (M : CanningsModel N Ω) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    ∑ j, M.countKernel i j * f j
      = ∑ ω, M.w ω * f ⟨∑ k ∈ firstParents N i, M.ν ω k, sum_firstParents_lt M i ω⟩ := by
  classical
  simp only [CanningsModel.countKernel, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  let j0 : Fin (N + 1) := ⟨∑ k ∈ firstParents N i, M.ν ω k, sum_firstParents_lt M i ω⟩
  change (∑ j : Fin (N + 1), (if j0.val = j.val then M.w ω else 0) * f j) = M.w ω * f j0
  simp only [← Fin.ext_iff]
  simp [ite_mul]

/-- Source: mohle1999, Thm 1; etheridge2011, sec. 3.2. -/
theorem cannings_blockCount_duality (M : CanningsModel N Ω) :
    FinChain.MomentDuality M.countChain (canningsAncestralChain M) (canningsHypergeom N) := by
  refine FinChain.MomentDuality.of_step ?_
  ext i n
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hNn := (choose_pos_of_fin n).ne'
  have hL : ∑ j, M.countChain.P i j * canningsHypergeom N j n
      = (∑ P ∈ (firstParents N i).powerset, sampleHit M n P) / (N.choose n : ℝ) := by
    rw [CanningsModel.countChain_P, countKernel_mul_apply, sum_powerset_sampleHit, sum_div]
    refine sum_congr rfl fun ω _ => ?_
    simp only [canningsHypergeom]
    ring
  have hR : ∑ m, canningsHypergeom N i m * (canningsAncestralChain M).Pᵀ m n
      = (∑ m : Fin (N + 1), ((i : ℕ).choose m : ℝ) * sampleHit M n (firstParents N m))
          / (N.choose n : ℝ) := by
    rw [sum_div]
    refine sum_congr rfl fun m _ => ?_
    rw [Matrix.transpose_apply, canningsAncestralChain_apply, canningsHypergeom]
    have hNm := (choose_pos_of_fin m).ne'
    field_simp
  rw [hL, hR]
  congr 1
  have hcard : #(firstParents N i) = (i : ℕ) := card_firstParents (Fin.is_le i)
  have h1 : ∑ P ∈ (firstParents N i).powerset, sampleHit M n P
      = ∑ P ∈ (firstParents N i).powerset, sampleHit M n (firstParents N #P) :=
    sum_congr rfl fun P _ => sampleHit_eq_firstParents M n P
  have h2 := sum_powerset_apply_card (fun m : ℕ => sampleHit M n (firstParents N m))
    (x := firstParents N i)
  rw [h1, h2, hcard]
  simp only [nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun m => ((i : ℕ).choose m : ℝ) * sampleHit M n (firstParents N m))]
  refine sum_subset (range_subset_range.2 (by have := Fin.is_le i; omega)) fun m _ hm' => ?_
  rw [mem_range] at hm'
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

end Rhone.Coalescent
