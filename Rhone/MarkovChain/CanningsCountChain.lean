/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Cannings
public import Rhone.MarkovChain.CoreBridge
public import Mathlib.Data.Fintype.Fin

/-!
# Cannings forward allele-count chain

Source: cannings1974, sec. 3, eq. (4)–(5), p. 266; ewens2004, sec. 3.3. -/

@[expose] public section
namespace Rhone.MarkovChain.CanningsModel

open Finset

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

/-- Source: cannings1974, sec. 3, p. 266. -/
private theorem subset_count_le (M : CanningsModel N Ω) (S : Finset (Fin N)) (ω : Ω) :
    (∑ k ∈ S, M.ν ω k) ≤ N := by
  have h : (∑ k ∈ S, M.ν ω k) ≤ ∑ k : Fin N, M.ν ω k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => Nat.zero_le _)
  exact h.trans_eq (M.sum_ν ω)

/-- Source: cannings1974, sec. 3, eq. (4)–(5), p. 266. -/
noncomputable def countKernel (M : CanningsModel N Ω) : CountKernel N :=
  fun i j => ∑ ω : Ω,
    if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) = j.val
    then M.w ω else 0

/-- Source: cannings1974, sec. 3, p. 266. -/
private theorem countKernel_expect (M : CanningsModel N Ω) (f : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    M.countKernel.expect f i = ∑ ω : Ω, M.w ω *
      f ⟨(∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k),
        Nat.lt_succ_of_le (subset_count_le M _ ω)⟩ := by
  classical
  unfold CountKernel.expect countKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  let j0 : Fin (N + 1) :=
    ⟨(∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k),
      Nat.lt_succ_of_le (subset_count_le M _ ω)⟩
  change (∑ j : Fin (N + 1), (if j0.val = j.val then M.w ω else 0) * f j) =
    M.w ω * f j0
  simp only [← Fin.ext_iff]
  simp [ite_mul]

/-- Source: cannings1974, sec. 3, eq. (4)–(5), p. 266. -/
theorem countKernel_isStochastic (M : CanningsModel N Ω) : M.countKernel.IsStochastic := by
  constructor
  · intro i j
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · exact M.w_nonneg ω
    · exact le_rfl
  · intro i
    have h := countKernel_expect M (fun _ => 1) i
    simpa only [CountKernel.expect, mul_one, M.sum_w] using h

/-- Source: cannings1974, sec. 3, p. 266. -/
noncomputable def countChain (M : CanningsModel N Ω) : Rhone.MarkovChain.FinChain (Fin (N + 1)) :=
  M.countKernel.toFinChain M.countKernel_isStochastic

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem countChain_P (M : CanningsModel N Ω) : M.countChain.P = M.countKernel := rfl

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem countChain_expect_count (M : CanningsModel N Ω) (i : Fin (N + 1)) :
    M.countChain.expect (fun j => (j : ℝ)) i = i := by
  change M.countKernel.expect (fun j => (j : ℝ)) i = i
  rw [countKernel_expect]
  have h := M.expected_next_count
    (Finset.univ.filter (fun k : Fin N => k.val < i.val))
  have hc : (Finset.univ.filter (fun k : Fin N => k.val < i.val)).card = i.val := by
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]
  simpa only [Nat.cast_sum, hc] using h

end Rhone.MarkovChain.CanningsModel
