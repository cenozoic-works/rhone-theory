/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitLeftInventory
public import Mathlib.Data.Finset.Option
/-! # Lineage counts of the ARG from the old and detached inventories -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess
private theorem same_partition_card {N : ℕ} (f g : Fin N → ℕ)
    (h : SameLeftPartition f g) :
    (Finset.univ.image f).card = (Finset.univ.image g).card := by
  classical
  let r (a : ℕ) (ha : a ∈ Finset.univ.image f) : Fin N :=
    (Finset.mem_image.mp ha).choose
  have hr (a : ℕ) (ha : a ∈ Finset.univ.image f) : f (r a ha) = a :=
    (Finset.mem_image.mp ha).choose_spec.2
  apply Finset.card_bij (fun a ha => g (r a ha))
  · intro a ha
    exact Finset.mem_image.mpr ⟨r a ha, Finset.mem_univ _, rfl⟩
  · intro a ha b hb he
    exact (hr a ha).symm.trans (((h _ _).mpr he).trans (hr b hb))
  · intro b hb
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    have ha : f j ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact ⟨f j, ha, ((h _ _).mp (hr (f j) ha)).trans hj⟩

theorem ExtractionInventory.arg_count {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (hs : Valid s) :
    s.2.2.1 = z.old.1.2.2.1 + z.detached.toFinset.card := by
  classical
  let P := Finset.univ.image (fun i : Fin s.2.2.1 => (s.2.2.2 i).1)
  let F := Finset.univ.image z.argLabels
  let G := Finset.univ.image z.oldLabels
  let O := Finset.univ.image (fun i : Fin z.old.1.2.2.1 => (z.old.1.2.2.2 i).1)
  have hO : O = G := by
    ext b
    constructor
    · rintro hb
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      obtain ⟨a, ha⟩ := h.2.2.2.1 i
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.trans hi⟩
    · rintro hb
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb
      obtain ⟨i, hi⟩ := h.2.2.1 a
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans ha⟩
  have hPc : P.card = s.2.2.1 := by
    simpa only [P, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ hs.2.2.2
  have hOc : O.card = z.old.1.2.2.1 := by
    simpa only [O, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ h.1.2.2.2
  have hFG : F.card = G.card := same_partition_card _ _ h.2.2.2.2
  have hdet (b : ℕ) : b ∈ z.detached.toFinset ↔ z.detached = some b := by
    cases z.detached <;> simp [eq_comm]
  have hPF : P = F ∪ z.detached.toFinset := by
    ext b
    constructor
    · intro hb
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      rcases h.2.1.2.1 i with ⟨a, ha⟩ | hd
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨a, Finset.mem_univ _, ha.trans hi⟩)
      · exact Finset.mem_union_right _ ((hdet b).mpr (hd.trans (congrArg some hi)))
    · intro hb
      rcases Finset.mem_union.mp hb with hf | hd
      · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hf
        obtain ⟨i, hi⟩ := h.2.1.1 a
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans ha⟩
      · obtain ⟨i, hi⟩ := (h.2.1.2.2 b ((hdet b).mp hd)).1
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hdis : Disjoint F z.detached.toFinset := by
    apply Finset.disjoint_left.mpr
    intro b hf hd
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hf
    exact (h.2.1.2.2 b ((hdet b).mp hd)).2 a ha
  rw [← hPc, hPF, Finset.card_union_of_disjoint hdis, hFG, ← hO, hOc]

theorem ExtractionInventory.arg_pair_rate {N : ℕ}
    {z : OneSplitExtractionState N} {s : State}
    (h : ExtractionInventory z s) (hs : Valid s) :
    (s.2.2.1 : ℝ) * ((s.2.2.1 : ℝ) - 1) / 2 =
      (z.old.1.2.2.1 : ℝ) * ((z.old.1.2.2.1 : ℝ) - 1) / 2 +
        (z.old.1.2.2.1 : ℝ) * z.detached.toFinset.card := by
  rw [h.arg_count hs]
  cases z.detached with
  | none => simp
  | some b =>
    simp only [Option.toFinset_some, Finset.card_singleton, Nat.cast_add, Nat.cast_one]
    ring
end Rhone.Coalescent.SmcPrime
