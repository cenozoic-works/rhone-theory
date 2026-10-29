/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Basic

/-! # Relabelling the slots -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {SA SB SA' SB' : Type*}

def mapM (e : SA ≃ SA') (d : SB ≃ SB') (M : Finset (SA × SB)) : Finset (SA' × SB') :=
  M.map (e.prodCongr d).toEmbedding

section Plain

variable (e : SA ≃ SA') (d : SB ≃ SB') (M : Finset (SA × SB))

theorem mem_mapM {p : SA' × SB'} : p ∈ mapM e d M ↔ (e.symm p.1, d.symm p.2) ∈ M :=
  Finset.mem_map_equiv

@[simp] theorem card_mapM : (mapM e d M).card = M.card := Finset.card_map _

end Plain

section Slots

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable [Fintype SA'] [DecidableEq SA'] [Fintype SB'] [DecidableEq SB']
variable (e : SA ≃ SA') (d : SB ≃ SB') (M : Finset (SA × SB))

omit [Fintype SB] [DecidableEq SB] [Fintype SB'] [DecidableEq SB'] in
theorem freeA_mapM : freeA (mapM e d M) = (freeA M).map e.toEmbedding := by
  ext u'
  rw [Finset.mem_map_equiv, mem_freeA, mem_freeA]
  constructor
  · intro h v hv
    refine h (d v) ?_
    rw [mem_mapM]
    simpa using hv
  · intro h v' hv'
    rw [mem_mapM] at hv'
    exact h (d.symm v') hv'

omit [Fintype SA] [DecidableEq SA] [Fintype SA'] [DecidableEq SA'] in
theorem freeB_mapM : freeB (mapM e d M) = (freeB M).map d.toEmbedding := by
  ext v'
  rw [Finset.mem_map_equiv, mem_freeB, mem_freeB]
  constructor
  · intro h u hu
    refine h (e u) ?_
    rw [mem_mapM]
    simpa using hu
  · intro h u' hu'
    rw [mem_mapM] at hu'
    exact h (e.symm u') hu'

omit [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB] [Fintype SA'] [DecidableEq SA']
  [Fintype SB'] [DecidableEq SB'] in
theorem isMatching_mapM (hM : IsMatching M) : IsMatching (mapM e d M) where
  fst p hp p' hp' hfst := by
    rw [mem_mapM] at hp hp'
    have h := hM.fst _ hp _ hp' (congrArg e.symm hfst)
    have h1 : e.symm p.1 = e.symm p'.1 := congrArg Prod.fst h
    have h2 : d.symm p.2 = d.symm p'.2 := congrArg Prod.snd h
    exact Prod.ext (e.symm.injective h1) (d.symm.injective h2)
  snd p hp p' hp' hsnd := by
    rw [mem_mapM] at hp hp'
    have h := hM.snd _ hp _ hp' (congrArg d.symm hsnd)
    have h1 : e.symm p.1 = e.symm p'.1 := congrArg Prod.fst h
    have h2 : d.symm p.2 = d.symm p'.2 := congrArg Prod.snd h
    exact Prod.ext (e.symm.injective h1) (d.symm.injective h2)

theorem xi_mapM (α' : SA' → Fin KA) (β' : SB' → Fin KB) :
    xi (mapM e d M) α' β' = xi M (fun u => α' (e u)) (fun v => β' (d v)) := by
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · simp only [xi_a, freeA_mapM, Finset.filter_map, Finset.card_map]
    rfl
  · simp only [xi_b, freeB_mapM, Finset.filter_map, Finset.card_map]
    rfl
  · simp only [xi_c, mapM, Finset.filter_map, Finset.card_map]
    rfl

variable {F : Type*} [CommRing F]

theorem Q_mapM (q : Config KA KB → F) (s' : SA' → Fin KA → F) (w' : SB' → Fin KB → F) :
    Q q (mapM e d M) s' w' = Q q M (fun u => s' (e u)) (fun v => w' (d v)) := by
  simp only [Q]
  rw [← Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl (Fin KA)))]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Equiv.sum_comp (Equiv.arrowCongr d (Equiv.refl (Fin KB)))]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hA : ∀ u : SA, (Equiv.arrowCongr e (Equiv.refl (Fin KA)) α) (e u) = α u := by
    intro u; simp
  have hB : ∀ v : SB, (Equiv.arrowCongr d (Equiv.refl (Fin KB)) β) (d v) = β v := by
    intro v; simp
  have hprodA : (∏ u' : SA', s' u' (Equiv.arrowCongr e (Equiv.refl (Fin KA)) α u'))
      = ∏ u : SA, s' (e u) (α u) :=
    (Fintype.prod_equiv e _ _ fun u => by rw [hA u]).symm
  have hprodB : (∏ v' : SB', w' v' (Equiv.arrowCongr d (Equiv.refl (Fin KB)) β v'))
      = ∏ v : SB, w' (d v) (β v) :=
    (Fintype.prod_equiv d _ _ fun v => by rw [hB v]).symm
  have hxi : xi (mapM e d M) (Equiv.arrowCongr e (Equiv.refl (Fin KA)) α)
      (Equiv.arrowCongr d (Equiv.refl (Fin KB)) β) = xi M α β := by
    rw [xi_mapM]
    congr 1 <;> funext x <;> simp
  rw [hprodA, hprodB, hxi]

end Slots

end Rhone.Probability.Multilinear
