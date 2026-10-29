/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Matrix
public import Rhone.Probability.SlotDeletion.Restrict
public import Rhone.Probability.Multilinear.MultilinearRecursion
public import Rhone.Probability.Multilinear.Lump

/-! # Two A-slots at a general alphabet — the vocabulary -/

@[expose] public section

universe u v

namespace Rhone.Probability.GeneralAlphabet

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open SlotDeletion

variable {KA KB : ℕ}

section TwoSlots

variable {SA : Type u} [Fintype SA]

theorem eq_or_eq_of_card_two (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (z : SA) : z = u₁ ∨ z = u₂ := by
  classical
  have hc2 : ({u₁, u₂} : Finset SA).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have huniv : ({u₁, u₂} : Finset SA) = univ := Finset.eq_univ_of_card _ (by rw [hc2, hcard])
  have hz : z ∈ ({u₁, u₂} : Finset SA) := by rw [huniv]; exact Finset.mem_univ z
  simpa [Finset.mem_insert, Finset.mem_singleton] using hz

end TwoSlots

section Pair

variable {F : Type*} [CommRing F] {SA : Type u} [DecidableEq SA]

def sPair (u₁ : SA) (x y : Fin KA → F) : SA → Fin KA → F := fun u => if u = u₁ then x else y

omit [CommRing F] in
@[simp] theorem sPair_self (u₁ : SA) (x y : Fin KA → F) : sPair u₁ x y u₁ = x := by simp [sPair]

omit [CommRing F] in
theorem sPair_of_ne {u₁ u : SA} (h : u ≠ u₁) (x y : Fin KA → F) : sPair u₁ x y u = y := by
  simp [sPair, h]

theorem mean_sPair {π : Fin KA → F} {u₁ : SA} {x y : Fin KA → F}
    (hx : mean π x = 0) (hy : mean π y = 0) (u : SA) : mean π (sPair u₁ x y u) = 0 := by
  by_cases h : u = u₁
  · rw [h, sPair_self]; exact hx
  · rw [sPair_of_ne h]; exact hy

variable [Fintype SA]

theorem sPair_mul (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (x y : Fin KA → F) {k m : SA} (hkm : k ≠ m) :
    sPair u₁ x y k * sPair u₁ x y m = x * y := by
  have h2 : sPair u₁ x y u₂ = y := sPair_of_ne (Ne.symm hne) x y
  rcases eq_or_eq_of_card_two hcard hne k with hk | hk <;>
    rcases eq_or_eq_of_card_two hcard hne m with hm | hm
  · exact absurd (hk.trans hm.symm) hkm
  · rw [hk, hm, sPair_self, h2]
  · rw [hk, hm, h2, sPair_self, mul_comm]
  · exact absurd (hk.trans hm.symm) hkm

end Pair

section Delete

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Q_eq_zero_of_two_slots (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {M : Finset (SA × SB)} (hM : IsMatching M) {v : SA} (s : SA → Fin KA → F) (hs : s v = 1)
    (hcen : ∀ z : SA, z ≠ v → mean πA (s z) = 0) (w : SB → Fin KB → F) :
    Q q M s w = 0 := by
  have hcard1 : Fintype.card {x : SA // x ≠ v} = 1 := by
    have h := card_sub_ne (SA := SA) v
    omega
  by_cases hfree : v ∈ freeA M
  · rw [Q_restrA hθA hθB hρ hq hπA hfree s hs w]
    exact Q_eq_zero_of_one_A_slot hθA hθB hρ hq _ (isMatching_restrA hM) hcard1 _ _
      fun z => hcen (z : SA) z.2
  · obtain ⟨v', hv'⟩ := mem_domA.mp (by simpa [freeA, Finset.mem_sdiff] using hfree)
    have hfree' : v ∈ freeA (M.erase (v, v')) := fst_freeA_erase hM hv'
    rw [Q_eraseA hθA hθB hρ hq hπA hM hv' s hs w, Q_restrA hθA hθB hρ hq hπA hfree' s hs w]
    exact Q_eq_zero_of_one_A_slot hθA hθB hρ hq _
      (isMatching_restrA (isMatching_erase hM _)) hcard1 _ _ fun z => hcen (z : SA) z.2

theorem Q_two_slots_update (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u v : SA} (hne : u ≠ v) {M : Finset (SA × SB)} (hM : IsMatching M)
    (z : Fin KA → F) (w : SB → Fin KB → F) :
    Q q M (Function.update (fun _ => (1 : Fin KA → F)) u z) w
      = mean πA z * Q q M (fun _ => (1 : Fin KA → F)) w := by
  have hone : Function.update (fun _ => (1 : Fin KA → F)) u 1 = fun _ => (1 : Fin KA → F) := by
    funext t; by_cases ht : t = u <;> simp [ht]
  have hz : centre πA z + mean πA z • (1 : Fin KA → F) = z := centre_add_mean πA z
  have hadd := (Q_isMultiA q M w).add (fun _ => (1 : Fin KA → F)) u
    (centre πA z) (mean πA z • (1 : Fin KA → F))
  have hsm := (Q_isMultiA q M w).smul (fun _ => (1 : Fin KA → F)) u (mean πA z)
    (1 : Fin KA → F)
  have hzero : Q q M (Function.update (fun _ => (1 : Fin KA → F)) u (centre πA z)) w = 0 := by
    refine Q_eq_zero_of_two_slots hθA hθB hρ hq hπA hcard hM (v := v) _ ?_ ?_ w
    · rw [Function.update_of_ne (Ne.symm hne)]
    · intro t ht
      rcases eq_or_eq_of_card_two hcard hne t with h | h
      · rw [h, Function.update_self]; exact mean_centre πA z hπA
      · exact absurd h ht
  calc Q q M (Function.update (fun _ => (1 : Fin KA → F)) u z) w
      = Q q M (Function.update (fun _ => (1 : Fin KA → F)) u
          (centre πA z + mean πA z • (1 : Fin KA → F))) w := by rw [hz]
    _ = Q q M (Function.update (fun _ => (1 : Fin KA → F)) u (centre πA z)) w
        + Q q M (Function.update (fun _ => (1 : Fin KA → F)) u
            (mean πA z • (1 : Fin KA → F))) w := hadd
    _ = mean πA z * Q q M (fun _ => (1 : Fin KA → F)) w := by rw [hzero, hsm, hone, zero_add]

theorem Q_two_slots_one (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u v : SA} (hne : u ≠ v) {M : Finset (SA × SB)} (hM : IsMatching M)
    (s : SA → Fin KA → F) (hs : s v = 1) (w : SB → Fin KB → F) :
    Q q M s w = mean πA (s u) * Q q M (fun _ => (1 : Fin KA → F)) w := by
  have hsplit : Function.update (fun _ => (1 : Fin KA → F)) u (s u) = s := by
    funext t
    by_cases ht : t = u
    · rw [ht, Function.update_self]
    · rw [Function.update_of_ne ht]
      rcases eq_or_eq_of_card_two hcard hne t with h | h
      · exact absurd h ht
      · rw [h, hs]
  calc Q q M s w
      = Q q M (Function.update (fun _ => (1 : Fin KA → F)) u (s u)) w := by rw [hsplit]
    _ = mean πA (s u) * Q q M (fun _ => (1 : Fin KA → F)) w :=
        Q_two_slots_update hθA hθB hρ hq hπA hcard hne hM (s u) w

theorem Q_hadA_sPair (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂) {M : Finset (SA × SB)} (hM : IsMatching M)
    (x y : Fin KA → F) {k m : SA} (hkm : k ≠ m) (w : SB → Fin KB → F) :
    Q q M (hadA k m (sPair u₁ x y)) w
      = mean πA (x * y) * Q q M (fun _ => (1 : Fin KA → F)) w := by
  have hm1 : hadA k m (sPair u₁ x y) m = 1 := by rw [hadA, Function.update_self]
  have hk1 : hadA k m (sPair u₁ x y) k = sPair u₁ x y k * sPair u₁ x y m := by
    rw [hadA, Function.update_of_ne hkm, Function.update_self]
  rw [Q_two_slots_one hθA hθB hρ hq hπA hcard hkm hM _ hm1 w, hk1,
    sPair_mul hcard hne x y hkm]

end Delete

section ConstOne

variable {SB : Type v} [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Q_const_one_empty {SA : Type u} [Fintype SA] [DecidableEq SA]
    (hcard : Fintype.card SA = 0) (M : Finset (SA × SB)) (hM : IsMatching M)
    (w : SB → Fin KB → F) :
    Q q M (fun _ => (1 : Fin KA → F)) w
      = ∑ β : SB → Fin KB, (∏ v, w v (β v)) * qOne θB πB (mBof β) := by
  have hu : (univ : Finset SA) = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_univ, hcard])
  have hterm : ∀ α : SA → Fin KA,
      (∏ u : SA, (1 : Fin KA → F) (α u)) * qOne θA πA (mAof α) = 1 := by
    intro α
    have hm : mAof α = fun _ => 0 := by
      funext i
      rw [mAof, hu, Finset.filter_empty, Finset.card_empty]
    rw [hm, qOne_zero, mul_one]
    simp
  have hcardfun : Fintype.card (SA → Fin KA) = 1 := by
    rw [Fintype.card_fun, hcard]
    simp
  rw [Q_factor hθA hθB hρ hq M hM (Or.inl (by omega)) _ w,
    Finset.sum_congr rfl fun α (_ : α ∈ univ) => hterm α, Finset.sum_const, Finset.card_univ,
    hcardfun, one_smul, one_mul]

theorem Q_const_one_aux (hπA : ∑ i, πA i = 1) :
    ∀ (n : ℕ) {SA : Type u} [Fintype SA] [DecidableEq SA] (M : Finset (SA × SB))
      (w : SB → Fin KB → F), IsMatching M → Fintype.card SA + M.card ≤ n →
      Q q M (fun _ => (1 : Fin KA → F)) w
        = ∑ β : SB → Fin KB, (∏ v, w v (β v)) * qOne θB πB (mBof β) := by
  intro n
  induction n with
  | zero =>
      intro SA _ _ M w hM hle
      exact Q_const_one_empty hθA hθB hρ hq (by omega) M hM w
  | succ n ih =>
      intro SA _ _ M w hM hle
      rcases isEmpty_or_nonempty SA with _ | ⟨⟨u₀⟩⟩
      · exact Q_const_one_empty hθA hθB hρ hq Fintype.card_eq_zero M hM w
      · by_cases hfree : u₀ ∈ freeA M
        · rw [Q_restrA hθA hθB hρ hq hπA hfree _ rfl w]
          have hcard : Fintype.card {x : SA // x ≠ u₀} + 1 = Fintype.card SA := card_sub_ne u₀
          exact ih (restrA u₀ M) w (isMatching_restrA hM) (by rw [card_restrA hfree]; omega)
        · obtain ⟨v, hv⟩ := mem_domA.mp (by simpa [freeA, Finset.mem_sdiff] using hfree)
          rw [Q_eraseA hθA hθB hρ hq hπA hM hv _ rfl w]
          have hMp : 1 ≤ M.card := Finset.card_pos.mpr ⟨(u₀, v), hv⟩
          exact ih (M.erase (u₀, v)) w (isMatching_erase hM _)
            (by rw [Finset.card_erase_of_mem hv]; omega)

variable {SA : Type u} [Fintype SA] [DecidableEq SA]

theorem Q_const_one (hπA : ∑ i, πA i = 1) (M : Finset (SA × SB)) (hM : IsMatching M)
    (w : SB → Fin KB → F) :
    Q q M (fun _ => (1 : Fin KA → F)) w
      = ∑ β : SB → Fin KB, (∏ v, w v (β v)) * qOne θB πB (mBof β) :=
  Q_const_one_aux hθA hθB hρ hq hπA _ M w hM le_rfl

theorem Q_const_one_basis (hπA : ∑ i, πA i = 1) (M : Finset (SA × SB)) (hM : IsMatching M)
    (β : SB → Fin KB) :
    Q q M (fun _ => (1 : Fin KA → F)) (fun v => Pi.single (β v) 1) = qOne θB πB (mBof β) := by
  rw [Q_const_one hθA hθB hρ hq hπA M hM]
  simp only [prod_single_apply]
  rw [Finset.sum_eq_single β (fun b _ hb => by simp [hb]) fun hb => absurd (Finset.mem_univ β) hb]
  simp

end ConstOne

end Rhone.Probability.GeneralAlphabet
