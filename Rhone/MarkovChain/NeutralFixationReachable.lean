/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.FixationCounted
public import Rhone.MarkovChain.CanningsCountChain

/-!
# Neutral fixation needs reachability: the martingale form and a counterexample

Source: cannings1974, sec. 3, eq. (4)–(5), p. 266; ewens2004, secs. 3.3, 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

variable {N : ℕ}

theorem isAbsorbing_zero_of_martingale (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) : C.IsAbsorbing 0 := by
  have h0 : ∑ j, C.P 0 j * (j : ℝ) = 0 := by
    have h := hm 0
    simpa [FinChain.expect_apply] using h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (C.nonneg 0 j) (Nat.cast_nonneg _))).1 h0
  have hz : ∀ j : Fin (N + 1), j ≠ 0 → C.P 0 j = 0 := by
    intro j hj
    have hpos : (0 : ℝ) < (j : ℕ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    rcases mul_eq_zero.1 (hterm j (mem_univ j)) with h | h
    · exact h
    · exact absurd h hpos.ne'
  have hrow := C.row_sum 0
  rw [Finset.sum_eq_single 0 (fun j _ hj => hz j hj) (fun h => absurd (mem_univ _) h)] at hrow
  exact hrow

theorem isAbsorbing_last_of_martingale (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) : C.IsAbsorbing (Fin.last N) := by
  have hN : ∑ j, C.P (Fin.last N) j * (j : ℝ) = N := by
    have h := hm (Fin.last N)
    simpa [FinChain.expect_apply] using h
  have h0 : ∑ j, C.P (Fin.last N) j * ((N : ℝ) - (j : ℝ)) = 0 := by
    have hsplit : ∀ j : Fin (N + 1), C.P (Fin.last N) j * ((N : ℝ) - (j : ℝ)) =
        (N : ℝ) * C.P (Fin.last N) j - C.P (Fin.last N) j * (j : ℝ) := fun j => by ring
    simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, C.row_sum, hN, mul_one,
      sub_self]
  have hle : ∀ j : Fin (N + 1), (0 : ℝ) ≤ (N : ℝ) - (j : ℝ) := fun j =>
    sub_nonneg.2 (by exact_mod_cast Nat.le_of_lt_succ j.isLt)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (C.nonneg (Fin.last N) j) (hle j))).1 h0
  have hz : ∀ j : Fin (N + 1), j ≠ Fin.last N → C.P (Fin.last N) j = 0 := by
    intro j hj
    have hlt : (j : ℕ) < N :=
      lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt) (fun h => hj (Fin.ext h))
    have hpos : (0 : ℝ) < (N : ℝ) - (j : ℝ) := sub_pos.2 (by exact_mod_cast hlt)
    rcases mul_eq_zero.1 (hterm j (mem_univ j)) with h | h
    · exact h
    · exact absurd h hpos.ne'
  have hrow := C.row_sum (Fin.last N)
  rw [Finset.sum_eq_single (Fin.last N) (fun j _ hj => hz j hj)
    (fun h => absurd (mem_univ _) h)] at hrow
  exact hrow

theorem countedId_isNeutral (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) : (CountedChain.mk C id).IsNeutral := by
  funext i
  have h := hm i
  rw [FinChain.expect_apply] at h ⊢
  have hterm : ∀ j : Fin (N + 1), C.P i j * (((id j : Fin (N + 1)) : ℕ) / (N : ℝ)) =
      C.P i j * (j : ℝ) / N := fun j => by simp [mul_div_assoc]
  change ∑ j, C.P i j * (((id j : Fin (N + 1)) : ℕ) / (N : ℝ)) =
    ((id i : Fin (N + 1)) : ℕ) / (N : ℝ)
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div, h]
  rfl

theorem countedId_hasAbsorbingBoundary (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) :
    (CountedChain.mk C id).HasAbsorbingBoundary :=
  CountedChain.hasAbsorbingBoundary_of_isAbsorbing fun s hs => by
    rcases hs with h | h
    · have hs0 : s = 0 := h
      rw [hs0]
      exact isAbsorbing_zero_of_martingale C hm
    · have hsN : s = Fin.last N := h
      rw [hsN]
      exact isAbsorbing_last_of_martingale C hm

theorem fixation_real_of_martingale (hN : 0 < N) (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) (hR : C.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (C.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CountedChain.fixation_real hN (countedId_isNeutral C hm) (countedId_hasAbsorbingBoundary C hm)
    (by rw [countedChain_id_boundary]; exact hR) i

theorem fixation_real_eventually_of_martingale (hN : 0 < N) (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) (hR : C.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (C.pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} = (i : ℝ) / N :=
  CountedChain.fixation_real_eventually hN (countedId_isNeutral C hm)
    (countedId_hasAbsorbingBoundary C hm) (by rw [countedChain_id_boundary]; exact hR) i

theorem loss_real_of_martingale (hN : 0 < N) (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) (hR : C.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (C.pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  CountedChain.loss_real hN (countedId_isNeutral C hm) (countedId_hasAbsorbingBoundary C hm)
    (by rw [countedChain_id_boundary]; exact hR) i

theorem CanningsModel.fixation_real_of_reaches {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hR : M.countChain.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  fixation_real_of_martingale hN M.countChain M.countChain_expect_count hR i

noncomputable def frozenChain (N : ℕ) : FinChain (Fin (N + 1)) where
  P := 1
  nonneg := fun x y => by
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  row_sum := fun x => by simp [Matrix.one_apply]

theorem frozenChain_isAbsorbing (N : ℕ) (i : Fin (N + 1)) : (frozenChain N).IsAbsorbing i := by
  change (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i i = 1
  simp

theorem frozenChain_martingale (N : ℕ) (i : Fin (N + 1)) :
    (frozenChain N).expect (fun j => (j : ℝ)) i = i := by
  change ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).mulVec fun j => (j : ℝ)) i = i
  rw [Matrix.one_mulVec]

theorem frozenChain_fixation_real (N : ℕ) {i : Fin (N + 1)} (hi : i ≠ Fin.last N) :
    ((frozenChain N).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = 0 := by
  rw [FinChain.pathLaw_hit_eq_absorbProb (frozenChain_isAbsorbing N (Fin.last N)) i,
    FinChain.absorbProb_of_isAbsorbing (frozenChain_isAbsorbing N i)]
  simp [hi]

theorem frozenChain_not_reaches (hN : 2 ≤ N) :
    ¬ (frozenChain N).Reaches (fixationBoundary N) := by
  intro hR
  obtain ⟨n, a, ha, hpos⟩ := hR ⟨1, by omega⟩
  rw [(frozenChain_isAbsorbing N ⟨1, by omega⟩).stepN_apply] at hpos
  have hne : (⟨1, by omega⟩ : Fin (N + 1)) ≠ a := by
    intro h
    rcases mem_fixationBoundary.1 ha with h0 | hl
    · have := congrArg Fin.val (h.trans h0)
      simp at this
    · have := congrArg Fin.val (h.trans hl)
      simp only [Fin.val_last] at this
      omega
  simp [hne] at hpos

theorem finChain_eq_of_P_eq {S : Type*} [Fintype S] {C D : FinChain S} (h : C.P = D.P) :
    C = D := by
  cases C
  cases D
  cases h
  rfl

noncomputable def oneOffspringModel (N : ℕ) : CanningsModel N Unit where
  w _ := 1
  ν _ _ := 1
  w_nonneg _ := zero_le_one
  sum_w := by simp
  sum_ν _ := by simp
  exchangeable _ _ := rfl

theorem oneOffspringModel_countChain (N : ℕ) :
    (oneOffspringModel N).countChain = frozenChain N := by
  apply finChain_eq_of_P_eq
  funext i j
  have hc : (Finset.univ.filter (fun k : Fin N => k.val < i.val)).card = i.val := by
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]
  have hs :
      (∑ _k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), (1 : ℕ)) = i.val := by
    rw [Finset.sum_const, hc, smul_eq_mul, mul_one]
  have hL : (oneOffspringModel N).countChain.P i j = ∑ _ω : Unit,
      if (∑ _k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), (1 : ℕ)) = j.val
      then (1 : ℝ) else 0 := rfl
  have hRhs : (frozenChain N).P i j = if i = j then 1 else 0 := Matrix.one_apply
  rw [hL, hRhs, hs]
  simp [Fin.ext_iff]

theorem cannings_fixation_ne_freq_without_reaches :
    ∃ M : CanningsModel 2 Unit,
      (M.countChain.pathLaw 1).real {ω | ∃ n, ω n = Fin.last 2} ≠ (1 : ℝ) / 2 := by
  refine ⟨oneOffspringModel 2, ?_⟩
  rw [oneOffspringModel_countChain, frozenChain_fixation_real 2 (by decide)]
  norm_num

end Rhone.MarkovChain
