/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFibreEquiv
/-!
# Cardinality recurrences for ranked shapes of the history quotient

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem card_ranked_shape_first_merger_recurrence (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (Combinatorics.RankedShape n) =
      ∑ k ∈ Ico 2 n, (n - 3).choose (k - 2) * Fintype.card (Combinatorics.RankedShape k) *
        Fintype.card (Combinatorics.RankedShape (n - k)) := by
  classical
  have hf (k : {k : ℕ // k ∈ Ico 2 n}) :
      Fintype.card {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k} =
      (n - 3).choose (k.val - 2) * Fintype.card (Combinatorics.RankedShape k.val) *
        Fintype.card (Combinatorics.RankedShape (n - k.val)) := by
    rw [Fintype.card_congr (rankedShapeRootFibreEquiv n hn k), Fintype.card_prod,
      Fintype.card_prod, Combinatorics.card_firstHistoryInterleaving]
    · have hk := mem_Ico.mp k.2
      have hl : k.val - 1 + (n - k.val - 1) - 1 = n - 3 := by omega
      have hr : k.val - 1 - 1 = k.val - 2 := by omega
      rw [hl, hr]
      ring
    · have hk := mem_Ico.mp k.2
      omega
  calc
    Fintype.card (Combinatorics.RankedShape n) =
        ∑ k : {k : ℕ // k ∈ Ico 2 n},
          Fintype.card {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k} := by
      rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (rankedShapeRootSize n hn)),
        Fintype.card_sigma]
    _ = ∑ k : {k : ℕ // k ∈ Ico 2 n},
        (n - 3).choose (k.val - 2) * Fintype.card (Combinatorics.RankedShape k.val) *
          Fintype.card (Combinatorics.RankedShape (n - k.val)) := by
      apply sum_congr rfl
      intro k hk
      exact hf k
    _ = ∑ k ∈ Ico 2 n, (n - 3).choose (k - 2) * Fintype.card (Combinatorics.RankedShape k) *
        Fintype.card (Combinatorics.RankedShape (n - k)) :=
      (Finset.sum_subtype (Ico 2 n) (fun _ => Iff.rfl)
        (fun k => (n - 3).choose (k - 2) * Fintype.card (Combinatorics.RankedShape k) *
          Fintype.card (Combinatorics.RankedShape (n - k)))).symm

/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem shape_root_convolution (n : ℕ) (hn : 3 ≤ n) (c : ℕ → ℕ) :
    (∑ k ∈ Ico 1 n, (n - 2).choose (k - 1) * c k * c (n - k)) =
      2 * ∑ k ∈ Ico 2 n, (n - 3).choose (k - 2) * c k * c (n - k) := by
  let F := fun k => (n - 3).choose (k - 2) * c k * c (n - k)
  let R := fun k => (n - 3).choose (k - 1) * c k * c (n - k)
  let M := fun k => (n - 2).choose (k - 1) * c k * c (n - k)
  have hI : Ico 1 n = insert 1 (Ico 2 n) := by
    ext k
    simp only [mem_Ico, mem_insert]
    omega
  have hsplit : ∑ k ∈ Ico 1 n, M k = (∑ k ∈ Ico 2 n, F k) + ∑ k ∈ Ico 1 n, R k := by
    have hc (k : ℕ) (hk : k ∈ Ico 2 n) : M k = F k + R k := by
      have hk := mem_Ico.mp hk
      have hN : n - 3 + 1 = n - 2 := by omega
      have hK : k - 2 + 1 = k - 1 := by omega
      dsimp only [M, F, R]
      have hh := Nat.choose_succ_succ' (n - 3) (k - 2)
      rw [hN, hK] at hh
      rw [hh]
      ring
    have hs : ∑ k ∈ Ico 2 n, M k = (∑ k ∈ Ico 2 n, F k) + ∑ k ∈ Ico 2 n, R k := by
      rw [← sum_add_distrib]
      exact sum_congr rfl hc
    rw [hI, sum_insert (by simp), hs, sum_insert (by simp)]
    have hMR : M 1 = R 1 := by simp [M, R]
    rw [hMR]
    omega
  have hR : ∑ k ∈ Ico 1 n, R k = ∑ k ∈ Ico 1 (n - 1), R k := by
    have hN : n - 1 + 1 = n := by omega
    rw [← hN, sum_Ico_succ_top (by omega : 1 ≤ n - 1)]
    have hz : R (n - 1) = 0 := by
      dsimp only [R]
      rw [Nat.choose_eq_zero_of_lt (by omega : n - 3 < n - 1 - 1)]
      simp
    rw [hz, Nat.add_zero]
    simp only [Nat.add_sub_cancel]
  have hrev : ∑ k ∈ Ico 2 n, F k = ∑ k ∈ Ico 1 (n - 1), R k := by
    apply sum_bij (fun k _ => n - k)
    · intro k hk
      have hk := mem_Ico.mp hk
      apply mem_Ico.mpr
      omega
    · intro k hk l hl he
      have hk := mem_Ico.mp hk
      have hl := mem_Ico.mp hl
      omega
    · intro k hk
      have hk := mem_Ico.mp hk
      refine ⟨n - k, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      have hk := mem_Ico.mp hk
      dsimp only [F, R]
      have hchoose := Nat.choose_symm (show k - 2 ≤ n - 3 by omega)
      have hm : n - 3 - (k - 2) = n - k - 1 := by omega
      rw [hm] at hchoose
      rw [hchoose, show n-(n - k) = k by omega]
      ring
  change ∑ k ∈ Ico 1 n, M k = 2 * ∑ k ∈ Ico 2 n, F k
  rw [hsplit, hR, ← hrev]
  omega
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem card_ranked_shape_recurrence (n : ℕ) (hn : 3 ≤ n) :
    2 * Fintype.card (Combinatorics.RankedShape n) =
      ∑ k ∈ Ico 1 n, (n - 2).choose (k - 1) *
        Fintype.card (Combinatorics.RankedShape k) * Fintype.card
            (Combinatorics.RankedShape (n - k)) := by
  rw [shape_root_convolution n hn (fun k => Fintype.card (Combinatorics.RankedShape k)),
    ← card_ranked_shape_first_merger_recurrence n hn]
end Rhone.Coalescent
