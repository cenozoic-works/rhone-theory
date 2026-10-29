/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Blocks
public import Rhone.Probability.InfiniteAlleles.Limit

/-! # Parent-independent-mutation limit with a growing allele alphabet -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset Filter Topology LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB K L : ℕ} (e : Fin KA ↪ Fin K) (f : Fin KB ↪ Fin L) (ξ : Config KA KB)

theorem mA_push_off {i' : Fin K} (h : ∀ i, e i ≠ i') : (push e f ξ).mA i' = 0 := by
  rw [Config.mA, push_a_off e f ξ h, cRow_push_off e f ξ h]

theorem mB_push_off {j' : Fin L} (h : ∀ j, f j ≠ j') : (push e f ξ).mB j' = 0 := by
  rw [Config.mB, push_b_off e f ξ h, cCol_push_off e f ξ h]

theorem obsA_push : obsA (push e f ξ) = obsA ξ := by
  have hset : (Finset.univ.filter fun i' : Fin K => (push e f ξ).mA i' ≠ 0)
      = (Finset.univ.filter fun i => ξ.mA i ≠ 0).map e := by
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      by_cases hi' : ∀ i, e i ≠ i'
      · exact absurd (mA_push_off e f ξ hi') h
      · obtain ⟨i, rfl⟩ : ∃ i, e i = i' := by
          by_contra hc; exact hi' fun i hi => hc ⟨i, hi⟩
        exact ⟨i, by rwa [mA_push] at h, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rwa [mA_push]
  change (Finset.univ.filter fun i' : Fin K => (push e f ξ).mA i' ≠ 0).card = _
  rw [hset, Finset.card_map]
  rfl

theorem obsB_push : obsB (push e f ξ) = obsB ξ := by
  have hset : (Finset.univ.filter fun j' : Fin L => (push e f ξ).mB j' ≠ 0)
      = (Finset.univ.filter fun j => ξ.mB j ≠ 0).map f := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h
      by_cases hj' : ∀ j, f j ≠ j'
      · exact absurd (mB_push_off e f ξ hj') h
      · obtain ⟨j, rfl⟩ : ∃ j, f j = j' := by
          by_contra hc; exact hj' fun j hj => hc ⟨j, hj⟩
        exact ⟨j, by rwa [mB_push] at h, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rwa [mB_push]
  change (Finset.univ.filter fun j' : Fin L => (push e f ξ).mB j' ≠ 0).card = _
  rw [hset, Finset.card_map]
  rfl

theorem obsTot_push : obsTot (push e f ξ) = obsTot ξ := by
  rw [obsTot, obsTot, obsA_push, obsB_push]

section Real

variable {θA θB ρ : ℝ}

theorem Qresc_push (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (x : ℝ) :
    Qresc (KA := K) (KB := L) hθA hθB hρ x (push e f ξ) = Qresc hθA hθB hρ x ξ := by
  rw [Qresc, Qresc, resc, resc, obsTot_push, q_push]

theorem tendsto_Qresc_grow (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    Tendsto (fun m : ℕ => Qresc (KA := m + (KA + KB)) (KB := m + (KA + KB)) hθA hθB hρ
        (((m + (KA + KB) : ℕ) : ℝ)⁻¹)
        (push (Fin.castLEEmb (by omega)) (Fin.castLEEmb (by omega)) ξ))
      atTop (𝓝 (PIA hθA hθB hρ ξ)) := by
  have hEq : ∀ m : ℕ, Qresc (KA := m + (KA + KB)) (KB := m + (KA + KB)) hθA hθB hρ
      (((m + (KA + KB) : ℕ) : ℝ)⁻¹)
      (push (Fin.castLEEmb (by omega)) (Fin.castLEEmb (by omega)) ξ)
      = Qresc hθA hθB hρ (((m + (KA + KB) : ℕ) : ℝ)⁻¹) ξ :=
    fun m => Qresc_push _ _ ξ hθA hθB hρ _
  simp only [hEq]
  exact (tendsto_Qresc_nat hθA hθB hρ ξ).comp (Filter.tendsto_add_atTop_nat (KA + KB))

theorem tendsto_Qresc_grow_of_isSolutionIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → ℝ} (hq : IsSolutionIA θA θB ρ q) :
    Tendsto (fun m : ℕ => Qresc (KA := m + (KA + KB)) (KB := m + (KA + KB)) hθA hθB hρ
        (((m + (KA + KB) : ℕ) : ℝ)⁻¹)
        (push (Fin.castLEEmb (by omega)) (Fin.castLEEmb (by omega)) ξ))
      atTop (𝓝 (q ξ)) := by
  rw [congrFun (PIA_unique hθA hθB hρ hq) ξ]
  exact tendsto_Qresc_grow ξ hθA hθB hρ

theorem tendsto_Qresc_Plab (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (S : Sample n)
    (α : Fin n → Fin KA) (β : Fin n → Fin KB) :
    Tendsto (fun m : ℕ => Qresc (KA := m + (KA + KB)) (KB := m + (KA + KB)) hθA hθB hρ
        (((m + (KA + KB) : ℕ) : ℝ)⁻¹)
        (cfgOf S (fun k => Fin.castLEEmb (by omega : KA ≤ m + (KA + KB)) (α k))
          fun k => Fin.castLEEmb (by omega : KB ≤ m + (KA + KB)) (β k)))
      atTop (𝓝 (Plab hθA hθB hρ S α β)) := by
  have hEq : ∀ m : ℕ, (cfgOf S (fun k => Fin.castLEEmb (by omega : KA ≤ m + (KA + KB)) (α k))
      fun k => Fin.castLEEmb (by omega : KB ≤ m + (KA + KB)) (β k))
      = push (Fin.castLEEmb (by omega)) (Fin.castLEEmb (by omega)) (cfgOf S α β) :=
    fun m => (push_cfgOf S α β _ _).symm
  simp only [hEq]
  exact tendsto_Qresc_grow (cfgOf S α β) hθA hθB hρ

end Real

end Rhone.Probability.InfiniteAlleles
