/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Cfg

/-! # The counts of a state agree with the counts of its configuration -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

def onA (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.1.Nonempty ∧ p.2 = ∅

def onB (L : Finset (Lin n)) : Finset (Lin n) := L.filter fun p => p.1 = ∅ ∧ p.2.Nonempty

theorem sum_uA {p : Lin n} (hm : MonoA σA p) :
    ∑ i, uA σA p i = if p.1.Nonempty ∧ p.2 = ∅ then 1 else 0 := by
  split_ifs with h
  · obtain ⟨i₀, hi₀⟩ := exists_colourA hm h.1
    rw [uA_eq (show IsA σA i₀ p from ⟨h.1, h.2, hi₀⟩)]
    simp [eV]
  · rw [uA_eq_zero fun i hc => h ⟨hc.1, hc.2.1⟩]
    simp

theorem sum_uB {p : Lin n} (hm : MonoB σB p) :
    ∑ j, uB σB p j = if p.1 = ∅ ∧ p.2.Nonempty then 1 else 0 := by
  split_ifs with h
  · obtain ⟨j₀, hj₀⟩ := exists_colourB hm h.2
    rw [uB_eq (show IsB σB j₀ p from ⟨h.1, h.2, hj₀⟩)]
    simp [eV]
  · rw [uB_eq_zero fun j hc => h ⟨hc.1, hc.2.1⟩]
    simp

theorem sum_uC {p : Lin n} (hmA : MonoA σA p) (hmB : MonoB σB p) :
    ∑ i, ∑ j, uC σA σB p i j = if p.1.Nonempty ∧ p.2.Nonempty then 1 else 0 := by
  split_ifs with h
  · obtain ⟨i₀, hi₀⟩ := exists_colourA hmA h.1
    obtain ⟨j₀, hj₀⟩ := exists_colourB hmB h.2
    rw [uC_eq (show IsC σA σB i₀ j₀ p from ⟨h.1, h.2, hi₀, hj₀⟩)]
    simp [eM_apply]
  · rw [uC_eq_zero fun i j hc => h ⟨hc.1, hc.2.1⟩]
    simp

theorem sumA_cfg {L : Finset (Lin n)} (hcl : Clean σA σB L) :
    (cfg σA σB L).sumA = (onA L).card := by
  simp only [Config.sumA, cfg_a, cfgA, Finset.sum_apply]
  rw [Finset.sum_comm, onA, Finset.card_filter]
  exact Finset.sum_congr rfl fun p hp => sum_uA (hcl.monoA hp)

theorem sumB_cfg {L : Finset (Lin n)} (hcl : Clean σA σB L) :
    (cfg σA σB L).sumB = (onB L).card := by
  simp only [Config.sumB, cfg_b, cfgB, Finset.sum_apply]
  rw [Finset.sum_comm, onB, Finset.card_filter]
  exact Finset.sum_congr rfl fun p hp => sum_uB (hcl.monoB hp)

theorem t_cfg {L : Finset (Lin n)} (hcl : Clean σA σB L) :
    (cfg σA σB L).t = tt L := by
  have h1 : ∀ (i : Fin KA) (j : Fin KB), (cfg σA σB L).c i j = ∑ p ∈ L, uC σA σB p i j := by
    intro i j; simp [cfg_c, cfgC, Finset.sum_apply]
  simp only [Config.t, h1]
  calc ∑ i, ∑ j, ∑ p ∈ L, uC σA σB p i j
      = ∑ i, ∑ p ∈ L, ∑ j, uC σA σB p i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p ∈ L, ∑ i, ∑ j, uC σA σB p i j := Finset.sum_comm
    _ = tt L := by
        rw [tt, carC, Finset.card_filter]
        exact Finset.sum_congr rfl fun p hp => sum_uC (hcl.monoA hp) (hcl.monoB hp)

theorem card_carA {L : Finset (Lin n)} : na L = (onA L).card + tt L := by
  have h : (carA L).filter (fun p => p.2.Nonempty) = carC L := by
    ext p; simp [carA, carC, and_assoc]
  have h' : (carA L).filter (fun p => ¬ p.2.Nonempty) = onA L := by
    ext p
    simp only [carA, onA, Finset.mem_filter, Finset.not_nonempty_iff_eq_empty]
    tauto
  have := Finset.card_filter_add_card_filter_not (s := carA L) (p := fun p => p.2.Nonempty)
  rw [h, h'] at this
  unfold na tt
  omega

theorem card_carB {L : Finset (Lin n)} : nb L = (onB L).card + tt L := by
  have h : (carB L).filter (fun p => p.1.Nonempty) = carC L := by
    ext p; simp [carB, carC, and_assoc]; tauto
  have h' : (carB L).filter (fun p => ¬ p.1.Nonempty) = onB L := by
    ext p
    simp only [carB, onB, Finset.mem_filter, Finset.not_nonempty_iff_eq_empty]
    tauto
  have := Finset.card_filter_add_card_filter_not (s := carB L) (p := fun p => p.1.Nonempty)
  rw [h, h'] at this
  unfold nb tt
  omega

theorem card_partition {L : Finset (Lin n)} (hw : WF L) :
    L.card = (onA L).card + (onB L).card + tt L := by
  have h : L.filter (fun p => p.1.Nonempty) = carA L := rfl
  have h' : L.filter (fun p => ¬ p.1.Nonempty) = onB L := by
    ext p
    simp only [onB, Finset.mem_filter, Finset.not_nonempty_iff_eq_empty]
    constructor
    · rintro ⟨hp, he⟩
      exact ⟨hp, he, (hw.carries p hp).resolve_left
        (by rw [he]; simp)⟩
    · rintro ⟨hp, he, _⟩
      exact ⟨hp, he⟩
  have hc := Finset.card_filter_add_card_filter_not (s := L) (p := fun p => p.1.Nonempty)
  rw [h, h'] at hc
  have := card_carA (L := L)
  unfold na at this
  omega

theorem nA_cfg {L : Finset (Lin n)} (hcl : Clean σA σB L) : (cfg σA σB L).nA = na L := by
  rw [Config.nA, sumA_cfg hcl, t_cfg hcl, card_carA]

theorem nB_cfg {L : Finset (Lin n)} (hcl : Clean σA σB L) : (cfg σA σB L).nB = nb L := by
  rw [Config.nB, sumB_cfg hcl, t_cfg hcl, card_carB]

theorem n_cfg {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) :
    (cfg σA σB L).n = L.card := by
  rw [Config.n, sumA_cfg hcl, sumB_cfg hcl, t_cfg hcl, card_partition hw]

theorem n_cfg_eq_zero_iff {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) :
    (cfg σA σB L).n = 0 ↔ L = ∅ := by
  rw [n_cfg hw hcl, Finset.card_eq_zero]

end Rhone.Coalescent.TwoLocusGenealogy
