/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Transport

/-! # Lumping: `Q` at constant test vectors depends only on `(n_A, n_B, t)` -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {SA SB SA' SB' : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable [Fintype SA'] [DecidableEq SA'] [Fintype SB'] [DecidableEq SB']

noncomputable def pairEquivDomA {M : Finset (SA × SB)} (hM : IsMatching M) :
    {p // p ∈ M} ≃ {u // u ∈ domA M} :=
  Equiv.ofBijective (fun p => ⟨p.1.1, mem_domA_of_mem p.2⟩)
    ⟨fun p p' h => Subtype.ext (hM.fst _ p.2 _ p'.2 (congrArg Subtype.val h)),
      fun u => by
        obtain ⟨v, hv⟩ := mem_domA.mp u.2
        exact ⟨⟨(u.1, v), hv⟩, Subtype.ext rfl⟩⟩

noncomputable def pairEquivDomB {M : Finset (SA × SB)} (hM : IsMatching M) :
    {p // p ∈ M} ≃ {v // v ∈ domB M} :=
  Equiv.ofBijective (fun p => ⟨p.1.2, mem_domB_of_mem p.2⟩)
    ⟨fun p p' h => Subtype.ext (hM.snd _ p.2 _ p'.2 (congrArg Subtype.val h)),
      fun v => by
        obtain ⟨u, hu⟩ := mem_domB.mp v.2
        exact ⟨⟨(u, v.1), hu⟩, Subtype.ext rfl⟩⟩

omit [Fintype SA] [Fintype SB] [DecidableEq SB] in
theorem pairEquivDomA_apply {M : Finset (SA × SB)} (hM : IsMatching M) (p : {p // p ∈ M}) :
    (pairEquivDomA hM p : SA) = p.1.1 := rfl

omit [Fintype SA] [DecidableEq SA] [Fintype SB] in
theorem pairEquivDomB_apply {M : Finset (SA × SB)} (hM : IsMatching M) (p : {p // p ∈ M}) :
    (pairEquivDomB hM p : SB) = p.1.2 := rfl

omit [DecidableEq SA] [DecidableEq SB] [DecidableEq SA'] [DecidableEq SB'] in
theorem exists_mapM_eq {M : Finset (SA × SB)} {M' : Finset (SA' × SB')}
    (hM : IsMatching M) (hM' : IsMatching M')
    (hA : Fintype.card SA = Fintype.card SA') (hB : Fintype.card SB = Fintype.card SB')
    (hcard : M.card = M'.card) :
    ∃ (e : SA ≃ SA') (d : SB ≃ SB'), mapM e d M = M' := by
  classical
  have hcardM : Fintype.card {p // p ∈ M} = Fintype.card {p // p ∈ M'} := by
    simpa only [Fintype.card_coe] using hcard
  set φ : {p // p ∈ M} ≃ {p // p ∈ M'} := Fintype.equivOfCardEq hcardM with hφ
  have hdomA : Fintype.card {u : SA // u ∈ domA M} = Fintype.card {u : SA' // u ∈ domA M'} := by
    simpa only [Fintype.card_coe, card_domA hM, card_domA hM'] using hcard
  have hdomB : Fintype.card {v : SB // v ∈ domB M} = Fintype.card {v : SB' // v ∈ domB M'} := by
    simpa only [Fintype.card_coe, card_domB hM, card_domB hM'] using hcard
  have hfreeA : Fintype.card {u : SA // u ∉ domA M} = Fintype.card {u : SA' // u ∉ domA M'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hA, hdomA]
  have hfreeB : Fintype.card {v : SB // v ∉ domB M} = Fintype.card {v : SB' // v ∉ domB M'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hB, hdomB]
  set eA : SA ≃ SA' :=
    ((Equiv.sumCompl (· ∈ domA M)).symm.trans
      (Equiv.sumCongr ((pairEquivDomA hM).symm.trans (φ.trans (pairEquivDomA hM')))
        (Fintype.equivOfCardEq hfreeA))).trans (Equiv.sumCompl (· ∈ domA M')) with heA
  set eB : SB ≃ SB' :=
    ((Equiv.sumCompl (· ∈ domB M)).symm.trans
      (Equiv.sumCongr ((pairEquivDomB hM).symm.trans (φ.trans (pairEquivDomB hM')))
        (Fintype.equivOfCardEq hfreeB))).trans (Equiv.sumCompl (· ∈ domB M')) with heB
  have hpairA : ∀ p : {p // p ∈ M}, eA p.1.1 = (φ p).1.1 := by
    intro p
    have h1 : (Equiv.sumCompl (· ∈ domA M)).symm p.1.1
        = Sum.inl (pairEquivDomA hM p) :=
      Equiv.sumCompl_symm_apply_of_pos (pairEquivDomA hM p).2
    rw [heA]
    simp only [Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hpairB : ∀ p : {p // p ∈ M}, eB p.1.2 = (φ p).1.2 := by
    intro p
    have h1 : (Equiv.sumCompl (· ∈ domB M)).symm p.1.2
        = Sum.inl (pairEquivDomB hM p) :=
      Equiv.sumCompl_symm_apply_of_pos (pairEquivDomB hM p).2
    rw [heB]
    simp only [Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  refine ⟨eA, eB, Finset.eq_of_subset_of_card_le ?_ (by rw [card_mapM, hcard])⟩
  intro r hr
  simp only [mapM, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.prodCongr_apply] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have h := hpairA ⟨p, hp⟩
  have h' := hpairB ⟨p, hp⟩
  change (eA p.1, eB p.2) ∈ M'
  rw [h, h']
  exact (φ ⟨p, hp⟩).2

variable {F : Type*} [CommRing F]

theorem Q_const_congr (q : Config KA KB → F) {M : Finset (SA × SB)} {M' : Finset (SA' × SB')}
    (hM : IsMatching M) (hM' : IsMatching M')
    (hA : Fintype.card SA = Fintype.card SA') (hB : Fintype.card SB = Fintype.card SB')
    (hcard : M.card = M'.card) (f : Fin KA → F) (g : Fin KB → F) :
    Q q M (fun _ => f) (fun _ => g) = Q q M' (fun _ => f) (fun _ => g) := by
  obtain ⟨e, d, he⟩ := exists_mapM_eq hM hM' hA hB hcard
  rw [← he, Q_mapM]

end Rhone.Probability.Multilinear
