/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Esf

/-! # The marginals of `P` are the labelled Ewens sampling formulas -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n : ℕ} {θA θB ρ : ℝ}

noncomputable def esfPart (n : ℕ) (θ : ℝ) (ζ : Blocks n) : ℝ :=
  if IsPartOf (Finset.univ : Finset (Fin n)) ζ then
    (θ ^ ζ.card * ∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ)) / rising θ n
  else 0

theorem esfPart_eq_zero {ζ : Blocks n} (h : ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζ)
    (θ : ℝ) : esfPart n θ ζ = 0 := by rw [esfPart, ite_eq_right h]

theorem wB_eq_wA {K : ℕ} (σ : Fin n → Fin K) (π : Fin K → ℝ) (ζ : Blocks n) :
    wB σ π ζ = wA σ π ζ := rfl

theorem esfT_eq {K : ℕ} (θ : ℝ) (σ : Fin n → Fin K) (π : Fin K → ℝ) (ζ : Blocks n) :
    esfT θ σ π ζ = (θ ^ ζ.card * ∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ))
      * wA σ π ζ := by
  have hsplit : (∏ β ∈ ζ, tw σ π β)
      = (∏ β ∈ ζ, ((Nat.factorial (β.card - 1) : ℕ) : ℝ)) * ∏ β ∈ ζ, matchA σ π β := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ => rfl
  rw [esfT, wA, hsplit]
  ring

theorem sum_countIn_univ {K : ℕ} (σ : Fin n → Fin K) :
    (∑ i, countIn σ i (Finset.univ : Finset (Fin n))) = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := σ) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin K))) fun x _ => Finset.mem_univ (σ x)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (∑ i, countIn σ i (Finset.univ : Finset (Fin n)))
      = ∑ b, (Finset.univ.filter fun a => σ a = b).card := rfl
  rw [h2, ← h]

theorem sum_esfPart_wA {K : ℕ} (θ : ℝ) (σ : Fin n → Fin K) (π : Fin K → ℝ) :
    (∑ ζ : Blocks n, esfPart n θ ζ * wA σ π ζ)
      = qOne θ π fun i => countIn σ i (Finset.univ : Finset (Fin n)) := by
  have hsupp : ∀ ζ ∈ (Finset.univ : Finset (Blocks n)), ζ ∉ partsOf Finset.univ →
      esfPart n θ ζ * wA σ π ζ = 0 := by
    intro ζ _ hζ
    rw [esfPart_eq_zero (fun hc => hζ (mem_partsOf.2 hc)) θ, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (partsOf (Finset.univ : Finset (Fin n)))) hsupp]
  have hval : ∀ ζ ∈ partsOf (Finset.univ : Finset (Fin n)),
      esfPart n θ ζ * wA σ π ζ = esfT θ σ π ζ / rising θ n := by
    intro ζ hζ
    rw [esfPart, ite_eq_left (mem_partsOf.1 hζ), esfT_eq, div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_div, sum_esfT, qOne, sum_countIn_univ]

noncomputable def margB (θA θB ρ : ℝ) (ζB : Blocks n) : ℝ :=
  ∑ ζA : Blocks n, esfKernel θA θB ρ ζA ζB

theorem margB_eq_zero {ζB : Blocks n} (h : ¬ IsPartOf (Finset.univ : Finset (Fin n)) ζB) :
    margB θA θB ρ ζB = 0 :=
  Finset.sum_eq_zero fun _ _ => esfKernel_eq_zero_of_not_part fun hc => h hc.2

theorem sum_margB_wB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {KB : ℕ} (πB : Fin KB → ℝ)
    (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (σB : Fin n → Fin KB) :
    (∑ ζB : Blocks n, margB θA θB ρ ζB * wA σB πB ζB)
      = qOne θB πB fun j => countIn σB j (Finset.univ : Finset (Fin n)) := by
  have hπA : ∀ _i : Fin 1, (0 : ℝ) ≤ 1 := fun _ => zero_le_one
  have hsA : (∑ _i : Fin 1, (1 : ℝ)) = 1 := by simp
  have hdec := esf_pair_decomposition (πA := fun _ : Fin 1 => (1 : ℝ)) (πB := πB) hθA hθB hρ
    hπA hsA hπB hsB (fun _ : Fin n => (0 : Fin 1)) σB
  have hq := q_cSample_one_alleleA (πA := fun _ : Fin 1 => (1 : ℝ)) (πB := πB) hθA hθB hρ hsA
    (fun _ : Fin n => (0 : Fin 1)) σB
  rw [hq] at hdec
  have hcount : countB σB = fun j => countIn σB j (Finset.univ : Finset (Fin n)) := rfl
  rw [hcount] at hdec
  rw [hdec, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ζB _ => ?_
  rw [margB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ζA _ => ?_
  rw [wA_one_allele, mul_one, wB_eq_wA]

theorem margB_eq_esfPart (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζB : Blocks n) :
    margB θA θB ρ ζB = esfPart n θB ζB := by
  refine eq_of_transform_eq (fun _ h => margB_eq_zero h) (fun _ h => esfPart_eq_zero h θB)
    (fun K π hπ hsπ σ => ?_) ζB
  rw [sum_margB_wB hθA hθB hρ π hπ hsπ σ, sum_esfPart_wA]

theorem margA_eq_esfPart (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζA : Blocks n) :
    (∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB) = esfPart n θA ζA := by
  have h : (∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB)
      = ∑ ζB : Blocks n, esfKernel θB θA ρ ζB ζA :=
    Finset.sum_congr rfl fun ζB _ => (esfKernel_swap ζA ζB).symm
  rw [h]
  exact margB_eq_esfPart hθB hθA hρ ζA

end Rhone.Coalescent.EsfPair
