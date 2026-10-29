/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.InfiniteAllelesLimit.Limit

/-! # Shape fibres of partitions, and decoupling of the shape-pair law -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset Filter Topology EsfPair

variable {n : ℕ} {θ θA θB : ℝ} {ζ ζ' : Blocks n} {lam mu : Multiset ℕ}

def shapeOf (ζ : Blocks n) : Multiset ℕ := ζ.val.map Finset.card

def shapeFib (n : ℕ) (lam : Multiset ℕ) : Finset (Blocks n) :=
  (partsOf (Finset.univ : Finset (Fin n))).filter fun ζ => shapeOf ζ = lam

theorem mem_shapeFib : ζ ∈ shapeFib n lam ↔
    IsPartOf (Finset.univ : Finset (Fin n)) ζ ∧ shapeOf ζ = lam := by
  simp [shapeFib]

theorem card_eq_card_shapeOf (ζ : Blocks n) : ζ.card = Multiset.card (shapeOf ζ) := by
  rw [shapeOf, Multiset.card_map]
  rfl

theorem esfPart_congr_shape (hζ : IsPartOf (Finset.univ : Finset (Fin n)) ζ)
    (hζ' : IsPartOf (Finset.univ : Finset (Fin n)) ζ') (h : shapeOf ζ = shapeOf ζ') (θ : ℝ) :
    esfPart n θ ζ = esfPart n θ ζ' := by
  have hcard : ζ.card = ζ'.card := by
    rw [card_eq_card_shapeOf, card_eq_card_shapeOf, h]
  have hprod : (∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ))
      = ∏ β ∈ ζ', ((Nat.factorial (β.card - 1) : ℕ) : ℝ) := by
    have hz : ∀ ξ : Blocks n, (∏ β ∈ ξ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ))
        = ((shapeOf ξ).map fun c => ((Nat.factorial (c - 1) : ℕ) : ℝ)).prod := by
      intro ξ
      rw [shapeOf, Multiset.map_map, Finset.prod_eq_multiset_prod]
      rfl
    rw [hz, hz, h]
  rw [esfPart, esfPart, ite_eq_left hζ, ite_eq_left hζ', hcard, hprod]

noncomputable def shapeSum (n : ℕ) (θA θB ρ : ℝ) (lam mu : Multiset ℕ) : ℝ :=
  ∑ ζA ∈ shapeFib n lam, ∑ ζB ∈ shapeFib n mu, esfKernel θA θB ρ ζA ζB

noncomputable def esfShape (n : ℕ) (θ : ℝ) (lam : Multiset ℕ) : ℝ :=
  ∑ ζ ∈ shapeFib n lam, esfPart n θ ζ

theorem esfShape_eq_card_mul (hζ : ζ ∈ shapeFib n lam) (θ : ℝ) :
    esfShape n θ lam = ((shapeFib n lam).card : ℝ) * esfPart n θ ζ := by
  obtain ⟨hp, hs⟩ := mem_shapeFib.1 hζ
  have hconst : ∀ ζ' ∈ shapeFib n lam, esfPart n θ ζ' = esfPart n θ ζ := by
    intro ζ' hζ'
    obtain ⟨hp', hs'⟩ := mem_shapeFib.1 hζ'
    exact esfPart_congr_shape hp' hp (by rw [hs, hs']) θ
  rw [esfShape, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

theorem tendsto_shapeSum (hθA : 0 < θA) (hθB : 0 < θB) (lam mu : Multiset ℕ) :
    Tendsto (fun ρ : ℝ => shapeSum n θA θB ρ lam mu) atTop
      (𝓝 (esfShape n θA lam * esfShape n θB mu)) := by
  have hfac : esfShape n θA lam * esfShape n θB mu
      = ∑ ζA ∈ shapeFib n lam, ∑ ζB ∈ shapeFib n mu,
          esfPart n θA ζA * esfPart n θB ζB := by
    rw [esfShape, esfShape, Finset.sum_mul_sum]
  rw [hfac]
  exact tendsto_finsetSum _ fun ζA _ => tendsto_finsetSum _ fun ζB _ =>
    tendsto_esfKernel_prod hθA hθB ζA ζB

theorem tendsto_shapeSum_rep (hθA : 0 < θA) (hθB : 0 < θB) {ζA ζB : Blocks n}
    (hA : ζA ∈ shapeFib n lam) (hB : ζB ∈ shapeFib n mu) :
    Tendsto (fun ρ : ℝ => shapeSum n θA θB ρ lam mu) atTop
      (𝓝 (((shapeFib n lam).card : ℝ) * esfPart n θA ζA
        * (((shapeFib n mu).card : ℝ) * esfPart n θB ζB))) := by
  have h := tendsto_shapeSum (n := n) hθA hθB lam mu
  rwa [esfShape_eq_card_mul hA θA, esfShape_eq_card_mul hB θB] at h

end Rhone.Coalescent.InfiniteAllelesLimit
