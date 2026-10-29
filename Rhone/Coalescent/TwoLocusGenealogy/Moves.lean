/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Counts

/-! # The moves of the ancestral chain realize the moves of the recursion -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

theorem uA_eq_zero_of_emptyA {p : Lin n} (h : p.1 = ∅) : uA σA p = 0 :=
  uA_eq_zero fun _ hc => (Finset.nonempty_iff_ne_empty.1 hc.1) h

theorem uB_eq_zero_of_emptyB {p : Lin n} (h : p.2 = ∅) : uB σB p = 0 :=
  uB_eq_zero fun _ hc => (Finset.nonempty_iff_ne_empty.1 hc.2.1) h

theorem clean_class {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n}
    (hp : p ∈ L) :
    (∃ i, IsA σA i p) ∨ (∃ j, IsB σB j p) ∨ (∃ i j, IsC σA σB i j p) := by
  have hmA := hcl.monoA hp
  have hmB := hcl.monoB hp
  rcases Finset.eq_empty_or_nonempty p.1 with h1 | h1
  · have h2 : p.2.Nonempty := (hw.carries p hp).resolve_left (by rw [h1]; simp)
    obtain ⟨j, hj⟩ := exists_colourB hmB h2
    exact Or.inr (Or.inl ⟨j, h1, h2, hj⟩)
  · obtain ⟨i, hi⟩ := exists_colourA hmA h1
    rcases Finset.eq_empty_or_nonempty p.2 with h2 | h2
    · exact Or.inl ⟨i, h1, h2, hi⟩
    · obtain ⟨j, hj⟩ := exists_colourB hmB h2
      exact Or.inr (Or.inr ⟨i, j, h1, h2, hi, hj⟩)

theorem cfgA_coal {L : Finset (Lin n)} (hw : WF L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L.erase p) :
    cfgA σA (coalL L p q)
      = uA σA (p.1 ∪ q.1, p.2 ∪ q.2) + cfgA σA ((L.erase p).erase q) :=
  cfgA_insert (coal_not_mem hw hp (Finset.mem_of_mem_erase hq))

theorem cfgB_coal {L : Finset (Lin n)} (hw : WF L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L.erase p) :
    cfgB σB (coalL L p q)
      = uB σB (p.1 ∪ q.1, p.2 ∪ q.2) + cfgB σB ((L.erase p).erase q) :=
  cfgB_insert (coal_not_mem hw hp (Finset.mem_of_mem_erase hq))

theorem cfgC_coal {L : Finset (Lin n)} (hw : WF L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L.erase p) :
    cfgC σA σB (coalL L p q)
      = uC σA σB (p.1 ∪ q.1, p.2 ∪ q.2) + cfgC σA σB ((L.erase p).erase q) :=
  cfgC_insert (coal_not_mem hw hp (Finset.mem_of_mem_erase hq))

theorem cfgA_two {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    cfgA σA L = uA σA p + (uA σA q + cfgA σA ((L.erase p).erase q)) := by
  rw [cfgA_erase hp, cfgA_erase hq]

theorem cfgB_two {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    cfgB σB L = uB σB p + (uB σB q + cfgB σB ((L.erase p).erase q)) := by
  rw [cfgB_erase hp, cfgB_erase hq]

theorem cfgC_two {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    cfgC σA σB L = uC σA σB p + (uC σA σB q + cfgC σA σB ((L.erase p).erase q)) := by
  rw [cfgC_erase hp, cfgC_erase hq]

theorem clean_coal_of {L : Finset (Lin n)} (hcl : Clean σA σB L) {p q : Lin n}
    (hmA : MonoA σA (p.1 ∪ q.1, p.2 ∪ q.2)) (hmB : MonoB σB (p.1 ∪ q.1, p.2 ∪ q.2)) :
    Clean σA σB (coalL L p q) := by
  intro r hr
  rcases Finset.mem_insert.1 hr with rfl | hr
  · exact ⟨hmA, hmB⟩
  · exact hcl r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))

theorem notClean_coal_A {L : Finset (Lin n)} {p q : Lin n} {k l : Fin n} (hk : k ∈ p.1)
    (hl : l ∈ q.1) (hne : σA k ≠ σA l) : ¬ Clean σA σB (coalL L p q) := by
  intro hcl
  have hm : (p.1 ∪ q.1, p.2 ∪ q.2) ∈ coalL L p q := Finset.mem_insert_self _ _
  exact hne ((hcl.monoA hm) k (Finset.mem_union_left _ hk) l (Finset.mem_union_right _ hl))

theorem notClean_coal_B {L : Finset (Lin n)} {p q : Lin n} {k l : Fin n} (hk : k ∈ p.2)
    (hl : l ∈ q.2) (hne : σB k ≠ σB l) : ¬ Clean σA σB (coalL L p q) := by
  intro hcl
  have hm : (p.1 ∪ q.1, p.2 ∪ q.2) ∈ coalL L p q := Finset.mem_insert_self _ _
  exact hne ((hcl.monoB hm) k (Finset.mem_union_left _ hk) l (Finset.mem_union_right _ hl))

theorem coal_AA {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {i : Fin KA} (hip : IsA σA i p) (hiq : IsA σA i q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).dropA i := by
  have hm : IsA σA i (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨hip.1.mono Finset.subset_union_left, by simp [hip.2.1, hiq.2.1], ?_⟩
    intro k hk
    rcases Finset.mem_union.1 hk with h | h
    · exact hip.2.2 k h
    · exact hiq.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_forall hm.2.2) (monoB_of_empty hm.2.1), Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = decf (cfgA σA L) i
    rw [cfgA_coal hw hp hq, uA_eq hm, cfgA_two hp hq, uA_eq hip, uA_eq hiq, decf_eV_add]
  · change cfgB σB (coalL L p q) = cfgB σB L
    rw [cfgB_coal hw hp hq, uB_eq_zero_of_carA hm.1, cfgB_two hp hq,
      uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hiq.1]
    simp
  · change cfgC σA σB (coalL L p q) = cfgC σA σB L
    rw [cfgC_coal hw hp hq, uC_eq_zero_of_emptyB hm.2.1, cfgC_two hp hq,
      uC_eq_zero_of_emptyB hip.2.1, uC_eq_zero_of_emptyB hiq.2.1]
    simp

theorem coal_AB {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {i : Fin KA} {j : Fin KB} (hip : IsA σA i p)
    (hjq : IsB σB j q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).mergeAB i j := by
  have hm : IsC σA σB i j (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨hip.1.mono Finset.subset_union_left, hjq.2.1.mono Finset.subset_union_right, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact hip.2.2 k h
      · exact absurd h (by rw [hjq.1]; simp)
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact absurd h (by rw [hip.2.1]; simp)
      · exact hjq.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_forall hm.2.2.1) (monoB_of_forall hm.2.2.2),
    Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = decf (cfgA σA L) i
    rw [cfgA_coal hw hp hq, uA_eq_zero_of_carB hm.2.1, cfgA_two hp hq, uA_eq hip,
      uA_eq_zero_of_emptyA hjq.1]
    simp only [zero_add, decf_eV_add]
  · change cfgB σB (coalL L p q) = decf (cfgB σB L) j
    rw [cfgB_coal hw hp hq, uB_eq_zero_of_carA hm.1, cfgB_two hp hq,
      uB_eq_zero_of_carA hip.1, uB_eq hjq]
    simp only [zero_add, decf_eV_add]
  · change cfgC σA σB (coalL L p q) = Config.incC (cfgC σA σB L) i j
    rw [cfgC_coal hw hp hq, uC_eq hm, cfgC_two hp hq, uC_eq_zero_of_emptyB hip.2.1,
      uC_eq_zero_of_emptyA hjq.1, incC_eq_add]
    simp

theorem coal_AC {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {i : Fin KA} {j : Fin KB} (hip : IsA σA i p)
    (hjq : IsC σA σB i j q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).dropA i := by
  have hm : IsC σA σB i j (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨hip.1.mono Finset.subset_union_left, hjq.2.1.mono Finset.subset_union_right, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact hip.2.2 k h
      · exact hjq.2.2.1 k h
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact absurd h (by rw [hip.2.1]; simp)
      · exact hjq.2.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_forall hm.2.2.1) (monoB_of_forall hm.2.2.2),
    Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = decf (cfgA σA L) i
    rw [cfgA_coal hw hp hq, uA_eq_zero_of_carB hm.2.1, cfgA_two hp hq, uA_eq hip,
      uA_eq_zero_of_carB hjq.2.1]
    simp only [zero_add, decf_eV_add]
  · change cfgB σB (coalL L p q) = cfgB σB L
    rw [cfgB_coal hw hp hq, uB_eq_zero_of_carA hm.1, cfgB_two hp hq,
      uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hjq.1]
    simp
  · change cfgC σA σB (coalL L p q) = cfgC σA σB L
    rw [cfgC_coal hw hp hq, uC_eq hm, cfgC_two hp hq, uC_eq_zero_of_emptyB hip.2.1, uC_eq hjq]
    simp

theorem coal_BB {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {j : Fin KB} (hjp : IsB σB j p) (hjq : IsB σB j q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).dropB j := by
  have hm : IsB σB j (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨by simp [hjp.1, hjq.1], hjp.2.1.mono Finset.subset_union_left, ?_⟩
    intro k hk
    rcases Finset.mem_union.1 hk with h | h
    · exact hjp.2.2 k h
    · exact hjq.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_empty hm.1) (monoB_of_forall hm.2.2), Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = cfgA σA L
    rw [cfgA_coal hw hp hq, uA_eq_zero_of_emptyA hm.1, cfgA_two hp hq,
      uA_eq_zero_of_emptyA hjp.1, uA_eq_zero_of_emptyA hjq.1]
    simp
  · change cfgB σB (coalL L p q) = decf (cfgB σB L) j
    rw [cfgB_coal hw hp hq, uB_eq hm, cfgB_two hp hq, uB_eq hjp, uB_eq hjq, decf_eV_add]
  · change cfgC σA σB (coalL L p q) = cfgC σA σB L
    rw [cfgC_coal hw hp hq, uC_eq_zero_of_emptyA hm.1, cfgC_two hp hq,
      uC_eq_zero_of_emptyA hjp.1, uC_eq_zero_of_emptyA hjq.1]
    simp

theorem coal_BC {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {i : Fin KA} {j : Fin KB} (hjp : IsB σB j p)
    (hjq : IsC σA σB i j q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).dropB j := by
  have hm : IsC σA σB i j (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨hjq.1.mono Finset.subset_union_right, hjp.2.1.mono Finset.subset_union_left, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact absurd h (by rw [hjp.1]; simp)
      · exact hjq.2.2.1 k h
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact hjp.2.2 k h
      · exact hjq.2.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_forall hm.2.2.1) (monoB_of_forall hm.2.2.2),
    Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = cfgA σA L
    rw [cfgA_coal hw hp hq, uA_eq_zero_of_carB hm.2.1, cfgA_two hp hq,
      uA_eq_zero_of_emptyA hjp.1, uA_eq_zero_of_carB hjq.2.1]
    simp
  · change cfgB σB (coalL L p q) = decf (cfgB σB L) j
    rw [cfgB_coal hw hp hq, uB_eq_zero_of_carA hm.1, cfgB_two hp hq, uB_eq hjp,
      uB_eq_zero_of_carA hjq.1]
    simp only [decf_eV_add]
  · change cfgC σA σB (coalL L p q) = cfgC σA σB L
    rw [cfgC_coal hw hp hq, uC_eq hm, cfgC_two hp hq, uC_eq_zero_of_emptyA hjp.1, uC_eq hjq]
    simp

theorem coal_CC {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) {i : Fin KA} {j : Fin KB} (hip : IsC σA σB i j p)
    (hjq : IsC σA σB i j q) :
    Clean σA σB (coalL L p q) ∧ cfg σA σB (coalL L p q) = (cfg σA σB L).dropC i j := by
  have hm : IsC σA σB i j (p.1 ∪ q.1, p.2 ∪ q.2) := by
    refine ⟨hip.1.mono Finset.subset_union_left, hip.2.1.mono Finset.subset_union_left, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact hip.2.2.1 k h
      · exact hjq.2.2.1 k h
    · intro k hk
      rcases Finset.mem_union.1 hk with h | h
      · exact hip.2.2.2 k h
      · exact hjq.2.2.2 k h
  refine ⟨clean_coal_of hcl (monoA_of_forall hm.2.2.1) (monoB_of_forall hm.2.2.2),
    Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (coalL L p q) = cfgA σA L
    rw [cfgA_coal hw hp hq, uA_eq_zero_of_carB hm.2.1, cfgA_two hp hq,
      uA_eq_zero_of_carB hip.2.1, uA_eq_zero_of_carB hjq.2.1]
    simp
  · change cfgB σB (coalL L p q) = cfgB σB L
    rw [cfgB_coal hw hp hq, uB_eq_zero_of_carA hm.1, cfgB_two hp hq,
      uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hjq.1]
    simp
  · change cfgC σA σB (coalL L p q) = Config.decC (cfgC σA σB L) i j
    rw [cfgC_coal hw hp hq, uC_eq hm, cfgC_two hp hq, uC_eq hip, uC_eq hjq, decC_eM_add]

theorem mutA_A {L : Finset (Lin n)} (hcl : Clean σA σB L) {p : Lin n} (hp : p ∈ L)
    {i : Fin KA} (hip : IsA σA i p) :
    Clean σA σB (mutAL L p) ∧ cfg σA σB (mutAL L p) = (cfg σA σB L).dropA i := by
  have hL : mutAL L p = L.erase p := by rw [mutAL, ite_eq_left hip.2.1]
  refine ⟨hL ▸ hcl.subset (Finset.erase_subset _ _), Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (mutAL L p) = decf (cfgA σA L) i
    rw [hL, cfgA_erase hp, uA_eq hip, decf_eV_add]
  · change cfgB σB (mutAL L p) = cfgB σB L
    rw [hL, cfgB_erase hp, uB_eq_zero_of_carA hip.1]
    simp
  · change cfgC σA σB (mutAL L p) = cfgC σA σB L
    rw [hL, cfgC_erase hp, uC_eq_zero_of_emptyB hip.2.1]
    simp

theorem mutA_C {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n} (hp : p ∈ L)
    {i : Fin KA} {j : Fin KB} (hip : IsC σA σB i j p) :
    Clean σA σB (mutAL L p) ∧ cfg σA σB (mutAL L p) = (cfg σA σB L).killA i j := by
  have hne : p.2 ≠ ∅ := Finset.nonempty_iff_ne_empty.1 hip.2.1
  have hL : mutAL L p = insert ((∅ : Finset (Fin n)), p.2) (L.erase p) := by
    rw [mutAL, ite_eq_right hne]
  have hnm : ((∅ : Finset (Fin n)), p.2) ∉ L.erase p := mutA_not_mem hw hp hip.2.1
  have hm : IsB σB j ((∅ : Finset (Fin n)), p.2) := ⟨rfl, hip.2.1, hip.2.2.2⟩
  refine ⟨?_, Config.ext ?_ ?_ ?_⟩
  · rw [hL]
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact ⟨monoA_of_empty rfl, monoB_of_forall hm.2.2⟩
    · exact hcl r (Finset.mem_of_mem_erase hr)
  · change cfgA σA (mutAL L p) = cfgA σA L
    rw [hL, cfgA_insert hnm, uA_eq_zero_of_emptyA hm.1, cfgA_erase hp,
      uA_eq_zero_of_carB hip.2.1]
  · change cfgB σB (mutAL L p) = incf (cfgB σB L) j
    rw [hL, cfgB_insert hnm, uB_eq hm, cfgB_erase hp, uB_eq_zero_of_carA hip.1, incf_eq_add]
    simp
  · change cfgC σA σB (mutAL L p) = Config.decC (cfgC σA σB L) i j
    rw [hL, cfgC_insert hnm, uC_eq_zero_of_emptyA hm.1, cfgC_erase hp, uC_eq hip, decC_eM_add]
    simp

theorem mutB_B {L : Finset (Lin n)} (hcl : Clean σA σB L) {p : Lin n} (hp : p ∈ L)
    {j : Fin KB} (hjp : IsB σB j p) :
    Clean σA σB (mutBL L p) ∧ cfg σA σB (mutBL L p) = (cfg σA σB L).dropB j := by
  have hL : mutBL L p = L.erase p := by rw [mutBL, ite_eq_left hjp.1]
  refine ⟨hL ▸ hcl.subset (Finset.erase_subset _ _), Config.ext ?_ ?_ ?_⟩
  · change cfgA σA (mutBL L p) = cfgA σA L
    rw [hL, cfgA_erase hp, uA_eq_zero_of_emptyA hjp.1]
    simp
  · change cfgB σB (mutBL L p) = decf (cfgB σB L) j
    rw [hL, cfgB_erase hp, uB_eq hjp, decf_eV_add]
  · change cfgC σA σB (mutBL L p) = cfgC σA σB L
    rw [hL, cfgC_erase hp, uC_eq_zero_of_emptyA hjp.1]
    simp

theorem mutB_C {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n} (hp : p ∈ L)
    {i : Fin KA} {j : Fin KB} (hip : IsC σA σB i j p) :
    Clean σA σB (mutBL L p) ∧ cfg σA σB (mutBL L p) = (cfg σA σB L).killB i j := by
  have hne : p.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.1 hip.1
  have hL : mutBL L p = insert (p.1, (∅ : Finset (Fin n))) (L.erase p) := by
    rw [mutBL, ite_eq_right hne]
  have hnm : (p.1, (∅ : Finset (Fin n))) ∉ L.erase p := mutB_not_mem hw hp hip.1
  have hm : IsA σA i (p.1, (∅ : Finset (Fin n))) := ⟨hip.1, rfl, hip.2.2.1⟩
  refine ⟨?_, Config.ext ?_ ?_ ?_⟩
  · rw [hL]
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact ⟨monoA_of_forall hm.2.2, monoB_of_empty rfl⟩
    · exact hcl r (Finset.mem_of_mem_erase hr)
  · change cfgA σA (mutBL L p) = incf (cfgA σA L) i
    rw [hL, cfgA_insert hnm, uA_eq hm, cfgA_erase hp, uA_eq_zero_of_carB hip.2.1, incf_eq_add]
    simp
  · change cfgB σB (mutBL L p) = cfgB σB L
    rw [hL, cfgB_insert hnm, uB_eq_zero_of_emptyB hm.2.1, cfgB_erase hp,
      uB_eq_zero_of_carA hip.1]
  · change cfgC σA σB (mutBL L p) = Config.decC (cfgC σA σB L) i j
    rw [hL, cfgC_insert hnm, uC_eq_zero_of_emptyB hm.2.1, cfgC_erase hp, uC_eq hip, decC_eM_add]
    simp

theorem rec_C {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n} (hp : p ∈ L)
    {i : Fin KA} {j : Fin KB} (hip : IsC σA σB i j p) :
    Clean σA σB (recL L p) ∧ cfg σA σB (recL L p) = (cfg σA σB L).split i j := by
  have hmA : IsA σA i (p.1, (∅ : Finset (Fin n))) := ⟨hip.1, rfl, hip.2.2.1⟩
  have hmB : IsB σB j ((∅ : Finset (Fin n)), p.2) := ⟨rfl, hip.2.1, hip.2.2.2⟩
  have hnB : ((∅ : Finset (Fin n)), p.2) ∉ L.erase p := mutA_not_mem hw hp hip.2.1
  have hnA : (p.1, (∅ : Finset (Fin n))) ∉ insert ((∅ : Finset (Fin n)), p.2) (L.erase p) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨rec_ne hip.1, mutB_not_mem hw hp hip.1⟩
  refine ⟨?_, Config.ext ?_ ?_ ?_⟩
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact ⟨monoA_of_forall hmA.2.2, monoB_of_empty rfl⟩
    · rcases Finset.mem_insert.1 hr with rfl | hr
      · exact ⟨monoA_of_empty rfl, monoB_of_forall hmB.2.2⟩
      · exact hcl r (Finset.mem_of_mem_erase hr)
  · change cfgA σA (recL L p) = incf (cfgA σA L) i
    rw [recL, cfgA_insert hnA, cfgA_insert hnB, uA_eq hmA, uA_eq_zero_of_emptyA hmB.1,
      cfgA_erase hp, uA_eq_zero_of_carB hip.2.1, incf_eq_add]
  · change cfgB σB (recL L p) = incf (cfgB σB L) j
    rw [recL, cfgB_insert hnA, cfgB_insert hnB, uB_eq_zero_of_emptyB hmA.2.1, uB_eq hmB,
      cfgB_erase hp, uB_eq_zero_of_carA hip.1, incf_eq_add]
    simp
  · change cfgC σA σB (recL L p) = Config.decC (cfgC σA σB L) i j
    rw [recL, cfgC_insert hnA, cfgC_insert hnB, uC_eq_zero_of_emptyB hmA.2.1,
      uC_eq_zero_of_emptyA hmB.1, cfgC_erase hp, uC_eq hip, decC_eM_add]
    simp

end Rhone.Coalescent.TwoLocusGenealogy
