/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.SamplingDefs
public import Rhone.Probability.SlotDeletion.Restrict

/-! # Deleting slots: the forms used by the explicit biallelic-`B` sampling formula -/

@[expose] public section

universe u

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {KA KB : ℕ}

section PullM

variable {SB : Type*} [Fintype SB] [DecidableEq SB] {n : ℕ}

def pullM (x : Fin (n + 1)) (M : Finset (Fin (n + 1) × SB)) : Finset (Fin n × SB) :=
  univ.filter fun p => (x.succAbove p.1, p.2) ∈ M

@[simp] theorem mem_pullM {x : Fin (n + 1)} {M : Finset (Fin (n + 1) × SB)} {p : Fin n × SB} :
    p ∈ pullM x M ↔ (x.succAbove p.1, p.2) ∈ M := by simp [pullM]

theorem isMatching_pullM {x : Fin (n + 1)} {M : Finset (Fin (n + 1) × SB)} (hM : IsMatching M) :
    IsMatching (pullM x M) := by
  refine ⟨fun p hp p' hp' h => ?_, fun p hp p' hp' h => ?_⟩
  · rw [mem_pullM] at hp hp'
    have he := hM.fst _ hp _ hp' (by simpa using congrArg x.succAbove h)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (Fin.succAbove_right_injective he.1) he.2
  · rw [mem_pullM] at hp hp'
    have he := hM.snd _ hp _ hp' h
    simp only [Prod.mk.injEq] at he
    exact Prod.ext (Fin.succAbove_right_injective he.1) h

theorem domA_pullM (x : Fin (n + 1)) (M : Finset (Fin (n + 1) × SB)) :
    domA (pullM x M) = LinearAlgebra.BooleanLatticeInverse.pull x (domA M) := by
  ext y
  simp [mem_domA, LinearAlgebra.BooleanLatticeInverse.pull]

end PullM

section RestrB

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem domA_restrB_of_free {M : Finset (SA × SB)} {v₀ : SB} (h0 : v₀ ∈ freeB M) :
    domA (restrB v₀ M) = domA M := by
  ext u
  rw [mem_domA, mem_domA]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    exact ⟨v, mem_restrB.mp h⟩
  · rintro ⟨v, h⟩
    exact ⟨⟨v, fun hc => mem_freeB.mp h0 u (hc ▸ h)⟩, mem_restrB.mpr h⟩

theorem domA_restrB_of_mem {M : Finset (SA × SB)} (hM : IsMatching M) {p : SA × SB}
    (hp : p ∈ M) : domA (restrB p.2 M) = (domA M).erase p.1 := by
  ext u
  rw [mem_domA, Finset.mem_erase, mem_domA]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    have h := mem_restrB.mp h
    refine ⟨fun hu => hv ?_, v, h⟩
    exact congrArg Prod.snd (hM.fst _ h _ hp hu)
  · rintro ⟨hne, v, h⟩
    refine ⟨⟨v, fun hv => hne ?_⟩, mem_restrB.mpr h⟩
    exact congrArg Prod.fst (hM.snd _ h _ hp hv)

theorem card_restrB_slots (v₀ : SB) :
    Fintype.card {y : SB // y ≠ v₀} = Fintype.card SB - 1 := by
  have := card_sub_ne v₀
  omega

omit [Fintype SA] [DecidableEq SB] in
theorem exists_matching_domA (S : Finset SA) (h : S.card ≤ Fintype.card SB) :
    ∃ M : Finset (SA × SB), IsMatching M ∧ domA M = S := by
  classical
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le
    (α := {x // x ∈ S}) (β := SB) (by simpa using h)
  refine ⟨univ.image fun x : {x // x ∈ S} => (x.1, ι x), ⟨?_, ?_⟩, ?_⟩
  · intro p hp p' hp' he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hp'
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hp'
    rw [Subtype.ext he]
  · intro p hp p' hp' he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hp'
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hp'
    rw [ι.injective he]
  · ext u
    rw [mem_domA]
    constructor
    · rintro ⟨v, hv⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hv
      obtain ⟨a, rfl, _⟩ := hv
      exact a.2
    · intro hu
      refine ⟨ι ⟨u, hu⟩, ?_⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
      exact ⟨⟨u, hu⟩, rfl, rfl⟩

theorem Q_congr_domA {F : Type*} [CommRing F] (q : Config KA KB → F) {M M' : Finset (SA × SB)}
    (hM : IsMatching M) (hM' : IsMatching M') (h : domA M = domA M')
    (s : SA → Fin KA → F) (g : Fin KB → F) :
    Q q M s (fun _ => g) = Q q M' s (fun _ => g) := by
  classical
  have hcard : M.card = M'.card := by
    rw [← card_domA hM, ← card_domA hM', h]
  set φ : {p // p ∈ M} ≃ {p // p ∈ M'} :=
    (pairEquivDomA hM).trans ((Equiv.subtypeEquivRight (by intro u; rw [h])).trans
      (pairEquivDomA hM').symm) with hφ
  have hφA : ∀ p : {p // p ∈ M}, (φ p).1.1 = p.1.1 := by
    intro p
    exact congrArg Subtype.val ((pairEquivDomA hM').apply_symm_apply
      (Equiv.subtypeEquivRight (by intro u; rw [h]) (pairEquivDomA hM p)))
  have hdomB : Fintype.card {v : SB // v ∈ domB M} = Fintype.card {v : SB // v ∈ domB M'} := by
    simpa only [Fintype.card_coe, card_domB hM, card_domB hM'] using hcard
  have hfreeB : Fintype.card {v : SB // v ∉ domB M} = Fintype.card {v : SB // v ∉ domB M'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hdomB]
  set eB : SB ≃ SB :=
    ((Equiv.sumCompl (· ∈ domB M)).symm.trans
      (Equiv.sumCongr ((pairEquivDomB hM).symm.trans (φ.trans (pairEquivDomB hM')))
        (Fintype.equivOfCardEq hfreeB))).trans (Equiv.sumCompl (· ∈ domB M')) with heB
  have hpairB : ∀ p : {p // p ∈ M}, eB p.1.2 = (φ p).1.2 := by
    intro p
    have h1 : (Equiv.sumCompl (· ∈ domB M)).symm p.1.2
        = Sum.inl (pairEquivDomB hM p) :=
      Equiv.sumCompl_symm_apply_of_pos (pairEquivDomB hM p).2
    rw [heB]
    simp only [Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hmap : mapM (Equiv.refl SA) eB M = M' := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [card_mapM, hcard])
    intro r hr
    simp only [mapM, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.prodCongr_apply] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    have h1 := hφA ⟨p, hp⟩
    have h2 := hpairB ⟨p, hp⟩
    change (p.1, eB p.2) ∈ M'
    rw [h2]
    have := (φ ⟨p, hp⟩).2
    rw [show p.1 = (φ ⟨p, hp⟩).1.1 from h1.symm]
    exact this
  rw [← hmap, Q_mapM]
  rfl

end RestrB

section Delete

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

private theorem Q_delA_free (hπA : ∑ i, πA i = 1) {n : ℕ} {M : Finset (Fin (n + 1) × SB)}
    (x : Fin (n + 1)) (hx : x ∈ freeA M) (s : Fin (n + 1) → Fin KA → F) (hs : s x = 1)
    (w : SB → Fin KB → F) :
    Q q M s w = Q q (pullM x M) (fun y => s (x.succAbove y)) w := by
  rw [Q_restrA hθA hθB hρ hq hπA hx s hs w]
  have hE : restrA x M
      = mapM (finSuccAboveEquiv x) (Equiv.refl SB) (pullM x M) := by
    ext ⟨y, b⟩
    rw [mem_restrA, mem_mapM, mem_pullM]
    have : x.succAbove ((finSuccAboveEquiv x).symm y) = y.1 :=
      congrArg Subtype.val ((finSuccAboveEquiv x).apply_symm_apply y)
    simp only [Equiv.refl_symm, Equiv.refl_apply, this]
  rw [hE, Q_mapM]
  rfl

theorem Q_delA (hπA : ∑ i, πA i = 1) {n : ℕ} {M : Finset (Fin (n + 1) × SB)}
    (hM : IsMatching M) (x : Fin (n + 1)) (s : Fin (n + 1) → Fin KA → F) (hs : s x = 1)
    (w : SB → Fin KB → F) :
    Q q M s w = Q q (pullM x M) (fun y => s (x.succAbove y)) w := by
  by_cases hx : x ∈ freeA M
  · exact Q_delA_free hθA hθB hρ hq hπA x hx s hs w
  · have : ∃ v, (x, v) ∈ M := by
      by_contra hc
      push Not at hc
      exact hx (mem_freeA.mpr hc)
    obtain ⟨v, hv⟩ := this
    rw [Q_eraseA hθA hθB hρ hq hπA hM (p := (x, v)) hv s hs w]
    have hfree : x ∈ freeA (M.erase (x, v)) := by
      rw [freeA_erase hM hv]
      exact Finset.mem_insert_self _ _
    rw [Q_delA_free hθA hθB hρ hq hπA x hfree s hs w]
    have hpull : pullM x (M.erase (x, v)) = pullM x M := by
      ext ⟨y, b⟩
      rw [mem_pullM, mem_pullM, Finset.mem_erase]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun he => Fin.succAbove_ne x y (congrArg Prod.fst he), h⟩
    rw [hpull]

theorem Q_delB (hπB : ∑ j, πB j = 1) {M : Finset (SA × SB)} (hM : IsMatching M) (v₀ : SB)
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) (hw : w v₀ = 1) :
    Q q M s w = Q q (restrB v₀ M) s (fun y => w (y : SB)) := by
  by_cases hv : v₀ ∈ freeB M
  · exact Q_restrB hθA hθB hρ hq hπB hv s w hw
  · have : ∃ u, (u, v₀) ∈ M := by
      by_contra hc
      push Not at hc
      exact hv (mem_freeB.mpr hc)
    obtain ⟨u, hu⟩ := this
    rw [Q_eraseB hθA hθB hρ hq hπB hM (p := (u, v₀)) hu s w hw]
    have hfree : v₀ ∈ freeB (M.erase (u, v₀)) := by
      rw [freeB_erase hM hu]
      exact Finset.mem_insert_self _ _
    rw [Q_restrB hθA hθB hρ hq hπB hfree s w hw]
    have hr : restrB v₀ (M.erase (u, v₀)) = restrB v₀ M := by
      ext ⟨a, b⟩
      rw [mem_restrB, mem_restrB, Finset.mem_erase]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun he => b.2 (congrArg Prod.snd he), h⟩
    rw [hr]

end Delete

end Rhone.Probability.BooleanLatticeInverse
