/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Parts
public import Rhone.Coalescent.EsfPair.OneAllele

/-! # The labelled Ewens sampling formula paints to the one-locus PIM marginal -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n K : ℕ}

noncomputable def tw (σ : Fin n → Fin K) (π : Fin K → ℝ) (β : Finset (Fin n)) : ℝ :=
  ((Nat.factorial (β.card - 1) : ℕ) : ℝ) * matchA σ π β

noncomputable def esfT (θ : ℝ) (σ : Fin n → Fin K) (π : Fin K → ℝ) (ζ : Blocks n) : ℝ :=
  θ ^ ζ.card * ∏ β ∈ ζ, tw σ π β

def countIn (σ : Fin n → Fin K) (i : Fin K) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun k => σ k = i).card

theorem tw_insert_empty (σ : Fin n → Fin K) (π : Fin K → ℝ) (a : Fin n) :
    tw σ π (insert a ∅) = π (σ a) := by
  have hcard : (insert a (∅ : Finset (Fin n))).card = 1 := by simp
  have hfac : ((Nat.factorial (1 - 1) : ℕ) : ℝ) = 1 := by norm_num
  rw [tw, hcard, hfac, one_mul]
  refine matchA_eq ⟨a, Finset.mem_insert_self a ∅⟩ fun k hk => ?_
  rcases Finset.mem_insert.1 hk with rfl | h
  · rfl
  · exact absurd h (Finset.notMem_empty k)

theorem matchA_insert {σ : Fin n → Fin K} {π : Fin K → ℝ} {a : Fin n} {β : Finset (Fin n)}
    (hP : ∀ k ∈ β, σ k = σ a) : matchA σ π (insert a β) = π (σ a) :=
  matchA_eq ⟨a, Finset.mem_insert_self a β⟩ fun k hk => by
    rcases Finset.mem_insert.1 hk with rfl | h
    · rfl
    · exact hP k h

theorem tw_insert {σ : Fin n → Fin K} {π : Fin K → ℝ} {a : Fin n} {β : Finset (Fin n)}
    (ha : a ∉ β) (hne : β.Nonempty) :
    tw σ π (insert a β) = (if ∀ k ∈ β, σ k = σ a then (β.card : ℝ) else 0) * tw σ π β := by
  have hcard : (insert a β).card = β.card + 1 := Finset.card_insert_of_notMem ha
  by_cases hP : ∀ k ∈ β, σ k = σ a
  · have hfac : ((Nat.factorial ((insert a β).card - 1) : ℕ) : ℝ)
        = (β.card : ℝ) * ((Nat.factorial (β.card - 1) : ℕ) : ℝ) := by
      obtain ⟨m, hm⟩ : ∃ m, β.card = m + 1 := ⟨β.card - 1, by
        have := Finset.card_pos.2 hne
        omega⟩
      rw [hcard, hm]
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      ring
    rw [ite_eq_left hP, tw, tw, hfac, matchA_insert hP, matchA_eq hne hP]
    ring
  · have hzero : matchA σ π (insert a β) = 0 := by
      refine matchA_eq_zero fun hmono => hP fun k hk => ?_
      exact hmono k (Finset.mem_insert_of_mem hk) a (Finset.mem_insert_self a β)
    rw [ite_eq_right hP, tw, hzero, mul_zero, zero_mul]

noncomputable def cw (θ : ℝ) (σ : Fin n → Fin K) (π : Fin K → ℝ) (a : Fin n)
    (β : Finset (Fin n)) : ℝ :=
  if β = ∅ then θ * π (σ a) else if ∀ k ∈ β, σ k = σ a then (β.card : ℝ) else 0

theorem esfT_extend {θ : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {a : Fin n}
    {S : Finset (Fin n)} (ha : a ∉ S) {ζ : Blocks n} (hζ : IsPartOf S ζ)
    {β : Finset (Fin n)} (hβ : β ∈ insert (∅ : Finset (Fin n)) ζ) :
    esfT θ σ π (extend a ζ β) = cw θ σ π a β * esfT θ σ π ζ := by
  have hnew : insert a β ∉ ζ.erase β := extend_notMem ha hζ
  have hcard : (extend a ζ β).card = (ζ.erase β).card + 1 := by
    rw [extend, Finset.card_insert_of_notMem hnew]
  have hprod : (∏ γ ∈ extend a ζ β, tw σ π γ)
      = tw σ π (insert a β) * ∏ γ ∈ ζ.erase β, tw σ π γ := by
    rw [extend, Finset.prod_insert hnew]
  rcases Finset.mem_insert.1 hβ with rfl | hmem
  · have herase : ζ.erase (∅ : Finset (Fin n)) = ζ :=
      Finset.erase_eq_of_notMem hζ.empty_notMem
    rw [esfT, esfT, hcard, hprod, herase, cw, ite_eq_left rfl, tw_insert_empty]
    ring
  · have hane : β ≠ ∅ := fun hc => hζ.empty_notMem (hc ▸ hmem)
    have haβ : a ∉ β := fun hc => ha (hζ.block_subset hmem hc)
    have hne : β.Nonempty := Finset.nonempty_iff_ne_empty.2 hane
    have hcz : ζ.card = (ζ.erase β).card + 1 := by
      rw [Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.2 ⟨β, hmem⟩
      omega
    have hpz : (∏ γ ∈ ζ, tw σ π γ) = tw σ π β * ∏ γ ∈ ζ.erase β, tw σ π γ :=
      (Finset.mul_prod_erase ζ _ hmem).symm
    rw [esfT, esfT, hcard, hprod, hcz, hpz, tw_insert haβ hne, cw, ite_eq_right hane]
    ring

theorem sum_cw_of_ne_zero {θ : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {a : Fin n}
    {S : Finset (Fin n)} {ζ : Blocks n} (hζ : IsPartOf S ζ)
    (hmono : ∀ β ∈ ζ, ∀ k ∈ β, ∀ l ∈ β, σ k = σ l) :
    (∑ β ∈ ζ, cw θ σ π a β) = ((countIn σ (σ a) S : ℕ) : ℝ) := by
  have hcw : ∀ β ∈ ζ, cw θ σ π a β = if (∀ k ∈ β, σ k = σ a) then (β.card : ℝ) else 0 := by
    intro β hβ
    have hane : β ≠ ∅ := fun hc => hζ.empty_notMem (by rw [← hc]; exact hβ)
    rw [cw, ite_eq_right hane]
  have hbi : (ζ.filter fun β => ∀ k ∈ β, σ k = σ a).biUnion id = S.filter fun k => σ k = σ a := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_filter, id]
    constructor
    · rintro ⟨β, ⟨hβ, hP⟩, hk⟩
      exact ⟨hζ.block_subset hβ hk, hP k hk⟩
    · rintro ⟨hkS, hkc⟩
      obtain ⟨β, hβ, hkβ⟩ := hζ.exists_block hkS
      exact ⟨β, ⟨hβ, fun l hl => by rw [hmono β hβ l hl k hkβ, hkc]⟩, hkβ⟩
  have hcard : ((ζ.filter fun β => ∀ k ∈ β, σ k = σ a).biUnion id).card
      = ∑ β ∈ ζ.filter fun β => ∀ k ∈ β, σ k = σ a, β.card := by
    refine Finset.card_biUnion fun β hβ γ hγ hne => ?_
    exact hζ.pd β (Finset.mem_of_mem_filter _ hβ) γ (Finset.mem_of_mem_filter _ hγ) hne
  rw [Finset.sum_congr rfl hcw, ← Finset.sum_filter, countIn, ← hbi, hcard]
  push_cast
  rfl

theorem esfT_mul_sum_cw {θ : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {a : Fin n}
    {S : Finset (Fin n)} {ζ : Blocks n} (hζ : IsPartOf S ζ) :
    esfT θ σ π ζ * (∑ β ∈ insert (∅ : Finset (Fin n)) ζ, cw θ σ π a β)
      = esfT θ σ π ζ * (θ * π (σ a) + ((countIn σ (σ a) S : ℕ) : ℝ)) := by
  rw [Finset.sum_insert hζ.empty_notMem, cw, ite_eq_left rfl]
  by_cases hz : esfT θ σ π ζ = 0
  · rw [hz, zero_mul, zero_mul]
  · have hprod : (∏ β ∈ ζ, tw σ π β) ≠ 0 := by
      intro hc
      exact hz (by rw [esfT, hc, mul_zero])
    have hmono : ∀ β ∈ ζ, ∀ k ∈ β, ∀ l ∈ β, σ k = σ l := by
      intro β hβ
      have hne : tw σ π β ≠ 0 := fun hc => hprod (Finset.prod_eq_zero hβ hc)
      have hm : matchA σ π β ≠ 0 := fun hc => hne (by rw [tw, hc, mul_zero])
      by_contra hc
      refine hm (matchA_eq_zero fun hmono => hc ?_)
      exact fun k hk l hl => hmono k hk l hl
    rw [sum_cw_of_ne_zero hζ hmono]

theorem sum_esfT (θ : ℝ) (σ : Fin n → Fin K) (π : Fin K → ℝ) (S : Finset (Fin n)) :
    (∑ ζ ∈ partsOf S, esfT θ σ π ζ) = ∏ i, rising (θ * π i) (countIn σ i S) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [partsOf_empty, Finset.sum_singleton, esfT]
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, one_mul]
    refine (Finset.prod_eq_one fun i _ => ?_).symm
    rw [countIn]
    simp [rising]
  | insert a S ha IH =>
    rw [sum_partsOf_insert (esfT θ σ π) ha]
    have hterm : ∀ ζ ∈ partsOf S,
        (∑ β ∈ insert (∅ : Finset (Fin n)) ζ, esfT θ σ π (extend a ζ β))
          = esfT θ σ π ζ * (θ * π (σ a) + ((countIn σ (σ a) S : ℕ) : ℝ)) := by
      intro ζ hζ
      have hp : IsPartOf S ζ := mem_partsOf.1 hζ
      rw [Finset.sum_congr rfl fun β hβ => esfT_extend ha hp hβ, ← Finset.sum_mul,
        mul_comm (∑ β ∈ insert (∅ : Finset (Fin n)) ζ, cw θ σ π a β) (esfT θ σ π ζ),
        esfT_mul_sum_cw hp]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, IH]
    have hcount : ∀ i : Fin K, countIn σ i (insert a S)
        = if i = σ a then countIn σ i S + 1 else countIn σ i S := by
      intro i
      rw [countIn, countIn, Finset.filter_insert]
      by_cases hi : σ a = i
      · rw [ite_eq_left hi,
          Finset.card_insert_of_notMem (fun hc => ha (Finset.mem_of_mem_filter _ hc)),
          ite_eq_left hi.symm]
      · rw [ite_eq_right hi, ite_eq_right fun hc => hi hc.symm]
    have hs1 : (∏ i, rising (θ * π i) (countIn σ i (insert a S)))
        = rising (θ * π (σ a)) (countIn σ (σ a) (insert a S))
          * ∏ i ∈ Finset.univ.erase (σ a), rising (θ * π i) (countIn σ i (insert a S)) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (σ a))).symm
    have hs2 : (∏ i, rising (θ * π i) (countIn σ i S))
        = rising (θ * π (σ a)) (countIn σ (σ a) S)
          * ∏ i ∈ Finset.univ.erase (σ a), rising (θ * π i) (countIn σ i S) :=
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (σ a))).symm
    have hs3 : (∏ i ∈ Finset.univ.erase (σ a), rising (θ * π i) (countIn σ i (insert a S)))
        = ∏ i ∈ Finset.univ.erase (σ a), rising (θ * π i) (countIn σ i S) :=
      Finset.prod_congr rfl fun i hi => by rw [hcount i, ite_eq_right (Finset.ne_of_mem_erase hi)]
    rw [hs1, hs2, hs3, hcount (σ a), ite_eq_left rfl, rising_succ]
    ring

end Rhone.Coalescent.EsfPair
