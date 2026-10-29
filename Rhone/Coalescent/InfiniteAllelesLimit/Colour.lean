/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.InfiniteAllelesLimit.Refine
public import Rhone.Probability.InfiniteAlleles.Esf

/-! # The dummy-allele window: colouring by a partition, and the frequency vector `π(x)` -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset TwoLocusGenealogy EsfPair Probability.InfiniteAlleles

variable {n : ℕ} {ζ η : Blocks n} {x : ℝ}

noncomputable def ecol (n : ℕ) : Finset (Fin n) ≃ Fin (numCols n) :=
  Fintype.equivFin (Finset (Fin n))

theorem colourOf_eq (η : Blocks n) (k : Fin n) : colourOf η k = ecol n (blockOf η k) := rfl

noncomputable def cols (ζ : Blocks n) : Finset (Fin (numCols n)) := ζ.image (ecol n)

theorem mem_cols {i : Fin (numCols n)} : i ∈ cols ζ ↔ ∃ β ∈ ζ, ecol n β = i := by
  simp [cols]

theorem ecol_mem_cols {β : Finset (Fin n)} (hβ : β ∈ ζ) : ecol n β ∈ cols ζ :=
  mem_cols.2 ⟨β, hβ, rfl⟩

theorem symm_ecol_mem_of_mem_cols {i : Fin (numCols n)} (h : i ∈ cols ζ) :
    (ecol n).symm i ∈ ζ := by
  obtain ⟨β, hβ, rfl⟩ := mem_cols.1 h
  rwa [Equiv.symm_apply_apply]

theorem card_cols (ζ : Blocks n) : (cols ζ).card = ζ.card :=
  Finset.card_image_of_injective ζ (ecol n).injective

noncomputable def dummyCol (n : ℕ) : Fin (numCols n) := ecol n ∅

theorem dummyCol_notMem_cols (h : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    dummyCol n ∉ cols ζ := by
  intro hc
  exact h.empty_notMem (by simpa [dummyCol, Equiv.symm_apply_apply] using
    symm_ecol_mem_of_mem_cols hc)

noncomputable def piWin (ζ : Blocks n) (x : ℝ) : Fin (numCols n) → ℝ :=
  fun i => if i ∈ cols ζ then x else if i = dummyCol n then 1 - (ζ.card : ℝ) * x else 0

theorem piWin_of_mem_cols {i : Fin (numCols n)} (h : i ∈ cols ζ) : piWin ζ x i = x := by
  rw [piWin, ite_eq_left h]

theorem piWin_nonneg (hx : 0 ≤ x) (hxm : (ζ.card : ℝ) * x ≤ 1) : ∀ i, 0 ≤ piWin ζ x i := by
  intro i
  rw [piWin]
  split_ifs
  · exact hx
  · linarith
  · exact le_rfl

theorem piWin_sum_one (h : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    ∑ i, piWin ζ x i = 1 := by
  have hfil : (Finset.univ.filter fun i : Fin (numCols n) => i ∈ cols ζ) = cols ζ := by
    ext i; simp
  have hone : ∀ i ∈ Finset.univ.filter fun i : Fin (numCols n) => i ∉ cols ζ,
      piWin ζ x i = if i = dummyCol n then 1 - (ζ.card : ℝ) * x else 0 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [piWin, ite_eq_right hi.2]
  have hmem : dummyCol n ∈ Finset.univ.filter (fun i : Fin (numCols n) => i ∉ cols ζ) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, dummyCol_notMem_cols h⟩
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ cols ζ),
    Finset.sum_congr rfl (fun i hi => piWin_of_mem_cols (Finset.mem_filter.1 hi).2),
    hfil, Finset.sum_const, card_cols, nsmul_eq_mul, Finset.sum_congr rfl hone,
    Finset.sum_ite_eq', ite_eq_left hmem]
  ring

theorem matchA_colour_of_subset {π : Fin (numCols n) → ℝ} {β H : Finset (Fin n)}
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (hne : β.Nonempty) (hsub : β ⊆ H)
    (hH : H ∈ ζ) : matchA (colourOf ζ) π β = π (ecol n H) := by
  refine matchA_eq hne fun k hk => ?_
  rw [colourOf_eq, blockOf_eq hζ hH (hsub hk)]

theorem matchA_colour_of_not_subset {π : Fin (numCols n) → ℝ} {β : Finset (Fin n)}
    (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (hne : β.Nonempty)
    (h : ¬ ∃ H ∈ ζ, β ⊆ H) : matchA (colourOf ζ) π β = 0 := by
  obtain ⟨k, hk⟩ := hne
  have hH : blockOf ζ k ∈ ζ := blockOf_mem hζ (Finset.mem_univ k)
  have hnsub : ¬ β ⊆ blockOf ζ k := fun hc => h ⟨blockOf ζ k, hH, hc⟩
  obtain ⟨l, hl, hlnot⟩ := Finset.not_subset.1 hnsub
  refine matchA_eq_zero fun hmono => ?_
  have hkl : colourOf ζ k = colourOf ζ l := hmono k hk l hl
  have hb : blockOf ζ k = blockOf ζ l := (ecol n).injective hkl
  exact hlnot (hb ▸ mem_blockOf hζ (Finset.mem_univ l))

theorem wA_piWin (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ)
    (hη : IsPartOf (Finset.univ : Finset (Fin n)) η) :
    wA (colourOf ζ) (piWin ζ x) η = if Refines η ζ then x ^ η.card else 0 := by
  by_cases hr : Refines η ζ
  · have hval : ∀ β ∈ η, matchA (colourOf ζ) (piWin ζ x) β = x := by
      intro β hβ
      obtain ⟨H, hH, hsub⟩ := hr β hβ
      rw [matchA_colour_of_subset hζ (hη.ne β hβ) hsub hH,
        piWin_of_mem_cols (ecol_mem_cols hH)]
    rw [ite_eq_left hr, wA, Finset.prod_congr rfl hval, Finset.prod_const]
  · rw [ite_eq_right hr, wA]
    have h' : ∃ β ∈ η, ¬ ∃ H ∈ ζ, β ⊆ H := by
      by_contra hc
      refine hr fun β hβ => ?_
      by_contra hd
      exact hc ⟨β, hβ, hd⟩
    obtain ⟨β, hβ, hnot⟩ := h'
    exact Finset.prod_eq_zero hβ (matchA_colour_of_not_subset hζ (hη.ne β hβ) hnot)

noncomputable def mvec (ζ : Blocks n) : Fin (numCols n) → ℕ :=
  fun i => countIn (colourOf ζ) i (Finset.univ : Finset (Fin n))

theorem mvec_ecol (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) {β : Finset (Fin n)}
    (hβ : β ∈ ζ) : mvec ζ (ecol n β) = β.card := by
  have hfil : (Finset.univ.filter fun k : Fin n => colourOf ζ k = ecol n β) = β := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, colourOf_eq,
      Equiv.apply_eq_iff_eq]
    exact ⟨fun h => h ▸ mem_blockOf hζ (Finset.mem_univ k),
      fun h => blockOf_eq hζ hβ h⟩
  rw [mvec, countIn, hfil]

theorem mvec_eq_zero_of_notMem_cols (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ)
    {i : Fin (numCols n)} (hi : i ∉ cols ζ) : mvec ζ i = 0 := by
  rw [mvec, countIn, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 fun k _ => ?_
  intro hc
  exact hi (hc ▸ ecol_mem_cols (blockOf_mem hζ (Finset.mem_univ k)))

theorem filter_mvec_ne_zero (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) :
    (Finset.univ.filter fun i => mvec ζ i ≠ 0) = cols ζ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    exact h (mvec_eq_zero_of_notMem_cols hζ hc)
  · intro h
    obtain ⟨β, hβ, rfl⟩ := mem_cols.1 h
    rw [mvec_ecol hζ hβ]
    exact (Finset.card_pos.2 (hζ.ne β hβ)).ne'

theorem obs_mvec (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) : obs (mvec ζ) = ζ.card := by
  rw [obs, filter_mvec_ne_zero hζ, card_cols]

theorem sum_mvec (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) : ∑ i, mvec ζ i = n := by
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin (numCols n))), i ∉ cols ζ → mvec ζ i = 0 :=
    fun i _ hi => mvec_eq_zero_of_notMem_cols hζ hi
  rw [← Finset.sum_subset (Finset.subset_univ (cols ζ)) hsupp, cols,
    Finset.sum_image fun a _ b _ h => (ecol n).injective h,
    Finset.sum_congr rfl fun β hβ => mvec_ecol hζ hβ]
  exact sum_card_of_isPartOf hζ

theorem esfLab_mvec (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ) (θ : ℝ) :
    esfLab θ (mvec ζ) = esfPart n θ ζ := by
  have hprod : (∏ i ∈ Finset.univ.filter fun i => mvec ζ i ≠ 0,
      ((Nat.factorial (mvec ζ i - 1) : ℕ) : ℝ))
      = ∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ) := by
    rw [filter_mvec_ne_zero hζ, cols, Finset.prod_image fun a _ b _ h => (ecol n).injective h]
    exact Finset.prod_congr rfl fun β hβ => by rw [mvec_ecol hζ hβ]
  rw [esfLab, hprod, obs_mvec hζ, sum_mvec hζ, esfPart, ite_eq_left hζ]

end Rhone.Coalescent.InfiniteAllelesLimit
