/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Restrict

/-! # Killing a set of slots lands in a smaller block -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section Defs

variable {SA SB : Type*} [DecidableEq SA] [DecidableEq SB]

def liveM (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) : Finset (SA × SB) :=
  M.filter fun p => p.1 ∉ S ∧ p.2 ∉ T

def restrS (u₀ : SA) (S : Finset SA) : Finset {x : SA // x ≠ u₀} := S.subtype fun x => x ≠ u₀

def restrT (v₀ : SB) (T : Finset SB) : Finset {y : SB // y ≠ v₀} := T.subtype fun y => y ≠ v₀

@[simp] theorem mem_restrS {u₀ : SA} {S : Finset SA} {x : {x : SA // x ≠ u₀}} :
    x ∈ restrS u₀ S ↔ (x : SA) ∈ S := Finset.mem_subtype

@[simp] theorem mem_restrT {v₀ : SB} {T : Finset SB} {y : {y : SB // y ≠ v₀}} :
    y ∈ restrT v₀ T ↔ (y : SB) ∈ T := Finset.mem_subtype

theorem card_restrS {u₀ : SA} {S : Finset SA} (h : u₀ ∈ S) :
    (restrS u₀ S).card = S.card - 1 := by
  rw [restrS, Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem h]

theorem card_restrT {v₀ : SB} {T : Finset SB} (h : v₀ ∈ T) :
    (restrT v₀ T).card = T.card - 1 := by
  rw [restrT, Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem h]

@[simp] theorem liveM_empty (M : Finset (SA × SB)) :
    liveM M (∅ : Finset SA) (∅ : Finset SB) = M := by simp [liveM]

theorem liveM_erase (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) {p : SA × SB}
    (h : p.1 ∈ S ∨ p.2 ∈ T) : liveM (M.erase p) S T = liveM M S T := by
  have hnot : p ∉ M.filter fun r => r.1 ∉ S ∧ r.2 ∉ T := by
    simp only [Finset.mem_filter, not_and]
    intro _
    tauto
  rw [liveM, liveM, Finset.filter_erase, Finset.erase_eq_of_notMem hnot]

end Defs

section KillAtEmpty

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {K : ℕ}

theorem killAt_empty (f : Fin K → F) : killAt f (∅ : Finset ι) = fun _ => f := by
  funext x; simp [killAt]

theorem killAt_of_mem (f : Fin K → F) {S : Finset ι} {x : ι} (h : x ∈ S) :
    killAt f S x = 1 := by simp [killAt, h]

end KillAtEmpty

section Master

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

omit [LinearOrder F] [IsStrictOrderedRing F] hθA hθB hρ hq in
theorem Q_killAt_base {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB]
    [DecidableEq SB] {M : Finset (SA × SB)} {S : Finset SA} {T : Finset SB}
    (hM : IsMatching M) (hS : S = ∅) (hT : T = ∅) :
    Q q M (killAt (fvec πA) S) (killAt (fvec πB) T)
      = Phi q πA πB (Fintype.card SA - S.card) (Fintype.card SB - T.card)
          (liveM M S T).card := by
  subst hS; subst hT
  rw [killAt_empty, killAt_empty, liveM_empty]
  simp only [Finset.card_empty, Nat.sub_zero]
  exact Phi_eq q πA πB hM rfl rfl rfl (by have := card_freeA hM; omega)
    (by have := card_freeB hM; omega)

theorem Q_killAt_aux (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    ∀ (n : ℕ) {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
      (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB), IsMatching M →
      S.card + T.card + M.card ≤ n →
      Q q M (killAt (fvec πA) S) (killAt (fvec πB) T)
        = Phi q πA πB (Fintype.card SA - S.card) (Fintype.card SB - T.card)
            (liveM M S T).card := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hπB' : ∑ j, πB j = 1 := by rw [Fin.sum_univ_two]; exact hπB
  intro n
  induction n with
  | zero =>
      intro SA SB _ _ _ _ M S T hM hle
      exact Q_killAt_base hM (Finset.card_eq_zero.mp (by omega))
        (Finset.card_eq_zero.mp (by omega))
  | succ n ih =>
      intro SA SB _ _ _ _ M S T hM hle
      rcases Finset.eq_empty_or_nonempty S with hS | ⟨u₀, hu₀⟩
      · rcases Finset.eq_empty_or_nonempty T with hT | ⟨v₀, hv₀⟩
        · exact Q_killAt_base hM hS hT
        · have hkill : killAt (fvec πB) T v₀ = 1 := killAt_of_mem _ hv₀
          have hTpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
          by_cases hfree : v₀ ∈ freeB M
          · rw [Q_restrB hθA hθB hρ hq hπB' hfree _ _ hkill]
            have hres : (fun (y : {y : SB // y ≠ v₀}) => killAt (fvec πB) T (y : SB))
                = killAt (fvec πB) (restrT v₀ T) := by
              funext y
              simp only [killAt, mem_restrT]
            rw [hres, ih (restrB v₀ M) S (restrT v₀ T) (isMatching_restrB hM)
              (by rw [card_restrT hv₀, card_restrB hfree]; omega)]
            have h1 : Fintype.card {y : SB // y ≠ v₀} - (restrT v₀ T).card
                = Fintype.card SB - T.card := by
              have ha := card_sub_ne (SA := SB) v₀
              have hb := card_restrT hv₀
              have hc : T.card ≤ Fintype.card SB := by
                simpa using Finset.card_le_card (Finset.subset_univ T)
              omega
            have h2 : (liveM (restrB v₀ M) S (restrT v₀ T)).card = (liveM M S T).card := by
              rw [liveM, liveM,
                ← card_filter_restrB (M := M) hfree (fun r => r.1 ∉ S ∧ r.2 ∉ T)]
              refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
              simp only [mem_restrT]
            rw [h1, h2]
          · obtain ⟨u, hu⟩ := mem_domB.mp (by
              simpa [freeB, Finset.mem_sdiff] using hfree)
            rw [Q_eraseB hθA hθB hρ hq hπB' hM hu _ _ hkill,
              ih (M.erase (u, v₀)) S T (isMatching_erase hM _)
                (by
                  have hMp : 1 ≤ M.card := Finset.card_pos.mpr ⟨(u, v₀), hu⟩
                  rw [Finset.card_erase_of_mem hu]; omega),
              liveM_erase (p := (u, v₀)) M S T (Or.inr hv₀)]
      · have hkill : killAt (fvec πA) S u₀ = 1 := killAt_of_mem _ hu₀
        have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨u₀, hu₀⟩
        by_cases hfree : u₀ ∈ freeA M
        · rw [Q_restrA hθA hθB hρ hq hπA' hfree _ hkill]
          have hres : (fun (x : {x : SA // x ≠ u₀}) => killAt (fvec πA) S (x : SA))
              = killAt (fvec πA) (restrS u₀ S) := by
            funext x
            simp only [killAt, mem_restrS]
          rw [hres, ih (restrA u₀ M) (restrS u₀ S) T (isMatching_restrA hM)
            (by rw [card_restrS hu₀, card_restrA hfree]; omega)]
          have h1 : Fintype.card {x : SA // x ≠ u₀} - (restrS u₀ S).card
              = Fintype.card SA - S.card := by
            have ha := card_sub_ne (SA := SA) u₀
            have hb := card_restrS hu₀
            have hc : S.card ≤ Fintype.card SA := by
              simpa using Finset.card_le_card (Finset.subset_univ S)
            omega
          have h2 : (liveM (restrA u₀ M) (restrS u₀ S) T).card = (liveM M S T).card := by
            rw [liveM, liveM,
              ← card_filter_restrA (M := M) hfree (fun r => r.1 ∉ S ∧ r.2 ∉ T)]
            refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
            simp only [mem_restrS]
          rw [h1, h2]
        · obtain ⟨v, hv⟩ := mem_domA.mp (by
            simpa [freeA, Finset.mem_sdiff] using hfree)
          rw [Q_eraseA hθA hθB hρ hq hπA' hM hv _ hkill,
            ih (M.erase (u₀, v)) S T (isMatching_erase hM _)
              (by
                have hMp : 1 ≤ M.card := Finset.card_pos.mpr ⟨(u₀, v), hv⟩
                rw [Finset.card_erase_of_mem hv]; omega),
            liveM_erase (p := (u₀, v)) M S T (Or.inl hu₀)]

theorem Q_killAt_eq_Phi (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
    (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) (hM : IsMatching M) :
    Q q M (killAt (fvec πA) S) (killAt (fvec πB) T)
      = Phi q πA πB (Fintype.card SA - S.card) (Fintype.card SB - T.card)
          (liveM M S T).card :=
  Q_killAt_aux hθA hθB hρ hq hπA hπB _ M S T hM le_rfl

end Master

end Rhone.Probability.SlotDeletion
