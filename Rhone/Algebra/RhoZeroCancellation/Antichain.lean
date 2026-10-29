/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZeroCancellation.Poset
public import Rhone.Algebra.RhoZero.PartialFraction

/-! # The antichain case of the dependency-poset sum, against the sum over permutations -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open Finset

variable {F : Type*} [Field F]

def Antichain (ι : Type*) : ι → ι → Prop := fun _ _ => False

theorem antichain_irrefl (ι : Type*) : ∀ a : ι, ¬ Antichain ι a a := fun _ h => h

theorem pairwise_antichain {ι : Type*} (L : List ι) :
    L.Pairwise fun a b => ¬ Antichain ι b a := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons a L IH => exact List.Pairwise.cons (fun b _ h => h) IH

theorem mem_linExts_antichain {ι : Type*} {T : Finset ι} {L : List ι} :
    L ∈ linExts (Antichain ι) T ↔ (L : Multiset ι) = T.val := by
  rw [mem_linExts]
  exact ⟨fun h => h.1, fun h => ⟨h, pairwise_antichain L⟩⟩

theorem maximals_antichain {ι : Type*} (T : Finset ι) :
    maximals (Antichain ι) T = T := by
  ext v
  rw [mem_maximals]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ hh => hh⟩⟩

theorem Gsum_antichain {ι : Type*} (x : ι → F) :
    ∀ (n : ℕ) (T : Finset ι), T.card = n → (∀ U ⊆ T, U.Nonempty → ∑ i ∈ U, x i ≠ 0) →
      Gsum (Antichain ι) x T = ∏ i ∈ T, (x i)⁻¹ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hcard hne
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    have htot : ∑ i ∈ T, x i ≠ 0 := hne T (subset_refl T) hT
    have hstep : ∀ v ∈ T, Gsum (Antichain ι) x (T.erase v) = x v * ∏ i ∈ T, (x i)⁻¹ := by
      intro v hv
      have hxv : x v ≠ 0 := by
        have := hne {v} (Finset.singleton_subset_iff.mpr hv) ⟨v, Finset.mem_singleton_self v⟩
        rwa [Finset.sum_singleton] at this
      have hlt : (T.erase v).card < n := by
        rw [← hcard]; exact Finset.card_erase_lt_of_mem hv
      rw [IH _ hlt (T.erase v) rfl
        (fun U hU hUne => hne U (hU.trans (Finset.erase_subset _ _)) hUne)]
      have hprod : ∏ i ∈ T, (x i)⁻¹ = (∏ i ∈ T.erase v, (x i)⁻¹) * (x v)⁻¹ :=
        (Finset.prod_erase_mul T (fun i => (x i)⁻¹) hv).symm
      rw [hprod, mul_comm (x v), mul_assoc, inv_mul_cancel₀ hxv, mul_one]
    have hsum : ∑ v ∈ maximals (Antichain ι) T, Gsum (Antichain ι) x (T.erase v)
        = (∑ i ∈ T, x i) * ∏ i ∈ T, (x i)⁻¹ := by
      rw [maximals_antichain, Finset.sum_congr rfl hstep, ← Finset.sum_mul]
    rw [sum_maximals_erase (antichain_irrefl ι) x hT htot] at hsum
    exact mul_left_cancel₀ htot hsum

theorem Fsum_antichain {ι : Type*} (x : ι → F) {T : Finset ι} (hT : T.Nonempty)
    (hne : ∀ U ⊆ T, U.Nonempty → ∑ i ∈ U, x i ≠ 0) :
    Fsum (Antichain ι) x T = (∑ i ∈ T, x i) * ∏ i ∈ T, (x i)⁻¹ := by
  classical
  rw [Fsum_eq_total_mul_Gsum x hT (hne T (subset_refl T) hT),
    Gsum_antichain x T.card T rfl hne]

theorem prefixSum_ne_zero {N : ℕ} (x : Fin N → F)
    (hne : ∀ U : Finset (Fin N), U.Nonempty → ∑ i ∈ U, x i ≠ 0) (σ : Equiv.Perm (Fin N))
    {r : ℕ} (hr : 0 < r) (hrN : r < N) : RhoZero.prefixSum x σ r ≠ 0 := by
  classical
  have himg : RhoZero.prefixSum x σ r
      = ∑ i ∈ (Finset.univ.filter fun s : Fin N => (s : ℕ) < r).image σ, x i := by
    rw [Finset.sum_image fun a _ b _ h => σ.injective h]
    rw [RhoZero.prefixSum, ← Finset.sum_filter]
  rw [himg]
  refine hne _ ⟨σ ⟨0, by omega⟩, Finset.mem_image.mpr ⟨⟨0, by omega⟩, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩

theorem Fsum_antichain_eq_sum_perm {N : ℕ} (hN : N ≠ 0) (x : Fin N → F)
    (hne : ∀ U : Finset (Fin N), U.Nonempty → ∑ i ∈ U, x i ≠ 0) :
    Fsum (Antichain (Fin N)) x Finset.univ
      = ∑ σ : Equiv.Perm (Fin N), ∏ r ∈ Finset.Ico 1 N, (RhoZero.prefixSum x σ r)⁻¹ := by
  have hxne : ∀ i, x i ≠ 0 := by
    intro i
    have := hne {i} ⟨i, Finset.mem_singleton_self i⟩
    rwa [Finset.sum_singleton] at this
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty := by
    refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
    omega
  rw [Fsum_antichain x huniv fun U _ hU => hne U hU,
    RhoZero.sum_perm_inv_prefix N x hN hxne
      fun σ r hr hrN => prefixSum_ne_zero x hne σ hr hrN]

end Rhone.Algebra.RhoZeroCancellation
