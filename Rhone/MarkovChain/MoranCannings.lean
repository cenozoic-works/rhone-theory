/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.CanningsCountChain

/-!
# The neutral Moran step as a Cannings count chain

Source: moran1958; cannings1974, sec. 3.2, p. 269; cannings1974, sec. 3, eq. (4)–(5), p. 266. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

/-- Source: moran1958; cannings1974, sec. 3.2, p. 269; cannings1974, sec. 3, p. 266. -/
theorem moranModel_countKernel (N : ℕ) (hN : 0 < N) :
    (moranModel N hN).countKernel = moran N 1 := by
  classical
  funext i j
  have hiN : (i : ℕ) ≤ N := Nat.le_of_lt_succ i.isLt
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N),
      S = Finset.univ.filter (fun k : Fin N => k.val < i.val) := ⟨_, rfl⟩
  have hmem : ∀ p : Fin N, p ∈ S ↔ p.val < i.val := fun p => by
    rw [hS, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ p, h⟩⟩
  have hc : S.card = i.val := by
    rw [hS, Fin.card_filter_val_lt, min_eq_right hiN]
  have hcount : ∀ pd : Fin N × Fin N,
      (∑ k ∈ S, moranOffspring N pd k) + (if pd.2 ∈ S then 1 else 0) =
        i.val + (if pd.1 ∈ S then 1 else 0) := by
    intro pd
    have h1 : ∑ k ∈ S, (if k = pd.1 then 1 else 0) = if pd.1 ∈ S then 1 else 0 :=
      Finset.sum_ite_eq' S pd.1 (fun _ => 1)
    have h2 : ∑ k ∈ S, (if k = pd.2 then 1 else 0) = if pd.2 ∈ S then 1 else 0 :=
      Finset.sum_ite_eq' S pd.2 (fun _ => 1)
    have h3 : ∑ k ∈ S, ((if k = pd.2 then 0 else 1) + (if k = pd.2 then 1 else 0)) =
        i.val := by
      rw [← hc, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> rfl
    rw [Finset.sum_add_distrib, h2] at h3
    simp only [moranOffspring]
    rw [Finset.sum_add_distrib, h1]
    omega
  obtain ⟨A, hA⟩ : ∃ A : Fin N → ℝ, A = fun p => if p.val < i.val then 1 else 0 := ⟨_, rfl⟩
  have hA1 : ∀ p : Fin N, p ∈ S → A p = 1 := fun p h => by
    rw [hA]
    exact ite_eq_left ((hmem p).1 h)
  have hA0 : ∀ p : Fin N, p ∉ S → A p = 0 := fun p h => by
    rw [hA]
    exact ite_eq_right fun h' => h ((hmem p).2 h')
  have key : ∀ pd : Fin N × Fin N,
      (if (∑ k ∈ S, moranOffspring N pd k) = j.val then 1 / (N : ℝ) ^ 2 else 0) =
        1 / (N : ℝ) ^ 2 *
          ((if j.val = i.val + 1 then (1 : ℝ) else 0) * (A pd.1 * (1 - A pd.2)) +
            (if i.val = j.val + 1 then (1 : ℝ) else 0) * ((1 - A pd.1) * A pd.2) +
            (if j.val = i.val then (1 : ℝ) else 0) *
              (A pd.1 * A pd.2 + (1 - A pd.1) * (1 - A pd.2))) := by
    intro pd
    have h := hcount pd
    generalize (∑ k ∈ S, moranOffspring N pd k) = c at h ⊢
    by_cases hp : pd.1 ∈ S <;> by_cases hd : pd.2 ∈ S
    · rw [ite_eq_left hp, ite_eq_left hd] at h
      rw [hA1 _ hp, hA1 _ hd]
      split_ifs <;> first | omega | ring
    · rw [ite_eq_left hp, ite_eq_right hd] at h
      rw [hA1 _ hp, hA0 _ hd]
      split_ifs <;> first | omega | ring
    · rw [ite_eq_right hp, ite_eq_left hd] at h
      rw [hA0 _ hp, hA1 _ hd]
      split_ifs <;> first | omega | ring
    · rw [ite_eq_right hp, ite_eq_right hd] at h
      rw [hA0 _ hp, hA0 _ hd]
      split_ifs <;> first | omega | ring
  have hsumA : ∑ p : Fin N, A p = i.val := by
    rw [hA, Finset.sum_boole, ← hS, hc]
  have hsumA' : ∑ p : Fin N, (1 - A p) = (N : ℝ) - i.val := by
    rw [Finset.sum_sub_distrib, hsumA, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hprod : ∀ f g : Fin N → ℝ,
      ∑ pd : Fin N × Fin N, f pd.1 * g pd.2 = (∑ p, f p) * ∑ d, g d := fun f g => by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hUp : ∑ pd : Fin N × Fin N, A pd.1 * (1 - A pd.2) = i.val * ((N : ℝ) - i.val) :=
    (hprod A fun d => 1 - A d).trans (by rw [hsumA, hsumA'])
  have hDown : ∑ pd : Fin N × Fin N, (1 - A pd.1) * A pd.2 = ((N : ℝ) - i.val) * i.val :=
    (hprod (fun p => 1 - A p) A).trans (by rw [hsumA, hsumA'])
  have hBoth : ∑ pd : Fin N × Fin N, A pd.1 * A pd.2 = (i.val : ℝ) * i.val :=
    (hprod A A).trans (by rw [hsumA])
  have hNone : ∑ pd : Fin N × Fin N, (1 - A pd.1) * (1 - A pd.2) =
      ((N : ℝ) - i.val) * ((N : ℝ) - i.val) :=
    (hprod (fun p => 1 - A p) fun d => 1 - A d).trans (by rw [hsumA'])
  change (∑ pd : Fin N × Fin N,
    if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), moranOffspring N pd k) =
      j.val then 1 / (N : ℝ) ^ 2 else 0) = moranRow N 1 i j
  rw [← hS, Finset.sum_congr rfl fun pd _ => key pd, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hUp, hDown, hBoth, hNone]
  rw [moranRow, moranUp_one, moranDown_one]
  split_ifs <;> first | omega | (field_simp; ring)

/-- Source: moran1958; cannings1974, sec. 3.2, p. 269; cannings1974, sec. 3, p. 266. -/
theorem moranModel_countChain (N : ℕ) (hN : 0 < N) :
    (moranModel N hN).countChain = moranChain N 1 one_pos := by
  have hext : ∀ (C D : Rhone.MarkovChain.FinChain (Fin (N + 1))), C.P = D.P → C = D := by
    intro C D h
    cases C
    cases D
    cases h
    rfl
  apply hext
  exact moranModel_countKernel N hN

end Rhone.MarkovChain
