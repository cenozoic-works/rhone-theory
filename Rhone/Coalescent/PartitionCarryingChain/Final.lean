/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Balance

/-! # The `ρ = 0` meet law, distributional half: `meetLaw(ρ = 0) = ESF(θ_A + θ_B)` -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair
open LinearAlgebra.Recursion

variable {n K : ℕ} {θA θB : ℝ}

theorem uStar_singleton (σ : Fin n → Fin K) (k : Fin n) (i : Fin K) :
    uStar σ (({k}, {k}) : Lin n) i = if σ k = i then 1 else 0 := by
  have hst : (({k}, {k}) : Lin n).1 ∩ (({k}, {k}) : Lin n).2 = {k} := by
    change ({k} : Finset (Fin n)) ∩ {k} = {k}
    rw [Finset.inter_self]
  rw [uStar, hst]
  by_cases hc : σ k = i
  · rw [ite_eq_left ⟨⟨k, Finset.mem_singleton_self k⟩, fun l hl => by
      rw [Finset.mem_singleton.1 hl]; exact hc⟩, ite_eq_left hc]
  · rw [ite_eq_right, ite_eq_right hc]
    rintro ⟨-, hall⟩
    exact hc (hall k (Finset.mem_singleton_self k))

theorem monoStars_fullState (σ : Fin n → Fin K) : MonoStars σ (fullState n) := by
  intro p hp
  obtain ⟨k, rfl⟩ := mem_fullState.1 hp
  have hst : (({k}, {k}) : Lin n).1 ∩ (({k}, {k}) : Lin n).2 = {k} := by
    change ({k} : Finset (Fin n)) ∩ {k} = {k}
    rw [Finset.inter_self]
  rw [hst]
  intro l hl m hm
  rw [Finset.mem_singleton.1 hl, Finset.mem_singleton.1 hm]

theorem scount_fullState (σ : Fin n → Fin K) (i : Fin K) :
    scount σ (fullState n) i = countIn σ i (Finset.univ : Finset (Fin n)) := by
  have hinj : ∀ k ∈ (Finset.univ : Finset (Fin n)), ∀ l ∈ (Finset.univ : Finset (Fin n)),
      (({k}, {k}) : Lin n) = (({l}, {l}) : Lin n) → k = l := by
    intro k _ l _ h
    exact Finset.singleton_injective (congrArg Prod.fst h)
  rw [scount, fullState, Finset.sum_image hinj,
    Finset.sum_congr rfl fun k _ => uStar_singleton σ k i, countIn, Finset.card_filter]

theorem Vst_fullState (σ : Fin n → Fin K) (π : Fin K → ℝ) :
    Vst σ π θA θB (fullState n)
      = qOne (θA + θB) π fun i => countIn σ i (Finset.univ : Finset (Fin n)) := by
  rw [Vst_of_mono (monoStars_fullState σ)]
  congr 1
  funext i
  exact scount_fullState σ i

theorem sum_meet_esfKernel (hθA : 0 < θA) (hθB : 0 < θB) (σ : Fin n → Fin K) (π : Fin K → ℝ) :
    (∑ x : Blocks n × Blocks n, wA σ π (meet x.1 x.2) * esfKernel θA θB 0 x.1 x.2)
      = qOne (θA + θB) π fun i => countIn σ i (Finset.univ : Finset (Fin n)) := by
  have hker : ∀ x : Blocks n × Blocks n, esfKernel θA θB 0 x.1 x.2
      = hitNP x.1 x.2 θA θB 0 (Phi (fullState n)) (initP n) :=
    fun x => esfKernel_eq_hitNP hθA hθB le_rfl
  rw [Finset.sum_congr rfl fun x _ => by rw [hker x],
    meet_hitNP_weighted σ π θA θB (Phi (fullState n)) inv_initP, emitStar_initP, wA_empty,
    one_mul]
  have hfst : (initP n).1 = fullState n := rfl
  rw [hfst, swN_eq_Vst hθA hθB σ π (Phi (fullState n)) (fullState n) fullState_wf
    aligned_fullState le_rfl, Vst_fullState σ π]

theorem meetLaw_rho_zero_eq_esfPart (hθA : 0 < θA) (hθB : 0 < θB) (ζ : Blocks n) :
    meetLaw n θA θB 0 ζ = esfPart n (θA + θB) ζ := by
  refine eq_of_transform_eq (fun _ h => meetLaw_eq_zero h)
    (fun _ h => esfPart_eq_zero h (θA + θB)) (fun _ π _ _ σ => ?_) ζ
  have hL : (∑ ζ' : Blocks n, meetLaw n θA θB 0 ζ' * wA σ π ζ')
      = ∑ x : Blocks n × Blocks n, wA σ π (meet x.1 x.2) * esfKernel θA θB 0 x.1 x.2 := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Blocks n × Blocks n))
      (fun x => meet x.1 x.2) (fun x => wA σ π (meet x.1 x.2) * esfKernel θA θB 0 x.1 x.2)]
    refine Finset.sum_congr rfl fun ζ' _ => ?_
    rw [meetLaw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
    ring
  rw [hL, sum_meet_esfKernel hθA hθB σ π, sum_esfPart_wA]

theorem meetLaw_rho_zero_eq_esfPart_and_sum_eq_one (hθA : 0 < θA) (hθB : 0 < θB) (n : ℕ) :
    (∀ ζ : Blocks n, meetLaw n θA θB 0 ζ = esfPart n (θA + θB) ζ)
      ∧ (∑ ζ : Blocks n, esfPart n (θA + θB) ζ) = 1 :=
  ⟨fun ζ => meetLaw_rho_zero_eq_esfPart hθA hθB ζ, sum_esfPart_eq_one (by linarith)⟩

/-- Source: golding1984, p. 264. -/
theorem meetLaw_rho_zero_oneBlock (hθA : 0 < θA) (hθB : 0 < θB) (n : ℕ) :
    meetLaw n θA θB 0 {(Finset.univ : Finset (Fin n))}
      = esfPart n (θA + θB) {(Finset.univ : Finset (Fin n))} :=
  meetLaw_rho_zero_eq_esfPart hθA hθB _

end Rhone.Coalescent.PartitionCarryingChain
