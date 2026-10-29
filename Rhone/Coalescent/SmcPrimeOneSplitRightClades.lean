/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightAncestry
public import Rhone.Coalescent.SmcPrimeRegraftCladeMap

/-! # Right sample clades after the single attachment -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionClade_route {N : ℕ} (f : Fin N → ℕ) (s : Finset (Fin N))
    (d a : ℕ) :
    extractionClade (fun j => if j ∈ s then d else f j) a =
      (extractionClade f a \ s) ∪ if d = a then s else ∅ := by
  classical
  ext j
  by_cases hjs : j ∈ s <;> by_cases hda : d = a <;>
    simp [extractionClade, hjs, hda]

theorem ancestorClade_single_split_right (N : ℕ) (ω : EventPath)
    (c i : ℕ) (x : ℝ) (hx : 0 < x) (hi : i < (ω c).1.2.2.1)
    (hev : (ω (c + 1)).2.2 = .inr (.inr (i, x)))
    (hbefore : ∀ l < c, CoalOrStop (ω (l + 1)).2.2)
    (hafter : ∀ l, c < l → CoalOrStop (ω (l + 1)).2.2)
    (q : GenomicProbe) (hq : x ≤ (q.val : ℝ)) (r : Fin N)
    (hr : ancestorLabel N ω leftBoundaryProbe r c = liveLabelAt (ω c).1 i)
    (k : ℕ) (hk : c + 1 ≤ k) (a : ℕ) :
    let s := extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j c)
      (liveLabelAt (ω c).1 i)
    extractionClade (fun j => ancestorLabel N ω q j k) a =
      (extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j k) a \ s) ∪
        if ancestorLabel N ω q r k = a then s else ∅ := by
  classical
  dsimp only
  let s := extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j c)
    (liveLabelAt (ω c).1 i)
  have hmap : (fun j => ancestorLabel N ω q j k) =
      (fun j => if j ∈ s then ancestorLabel N ω q r k
        else ancestorLabel N ω leftBoundaryProbe j k) := by
    funext j
    simpa only [s, extractionClade, Finset.mem_filter, Finset.mem_univ, true_and] using
      ancestorLabel_single_split_right N ω c i x hx hi hev hbefore hafter q hq r hr j k hk
  rw [hmap]
  exact extractionClade_route _ s _ a

theorem extractionClade_route_regraft {N : ℕ} (f : Fin N → ℕ)
    (s target : Finset (Fin N)) (d : Fin N) (hd : d ∈ target)
    (htarget : ∀ j ∈ target, f j = f d) (a : ℕ) :
    extractionClade (fun j => if j ∈ s then f d else f j) a =
      regraftClade s target (extractionClade f a) := by
  classical
  have hinter : ((extractionClade f a) ∩ target).Nonempty ↔ f d = a := by
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨hjc, hjt⟩ := Finset.mem_inter.mp hj
      have hja := (Finset.mem_filter.mp hjc).2
      exact (htarget j hjt).symm.trans hja
    · intro hda
      exact ⟨d, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ d, hda⟩, hd⟩⟩
  ext j
  change j ∈ extractionClade (fun j => if j ∈ s then f d else f j) a ↔
    j ∈ (extractionClade f a \ s) ∪
      if ((extractionClade f a) ∩ target).Nonempty then s else ∅
  simp only [hinter]
  by_cases hjs : j ∈ s <;> by_cases hda : f d = a <;>
    simp [extractionClade, hjs, hda]

theorem target_clade_persists (N : ℕ) (ω : EventPath)
    (l k : ℕ) (hlk : l ≤ k) (d j : Fin N)
    (hj : j ∈ extractionClade (fun u => ancestorLabel N ω leftBoundaryProbe u l)
      (ancestorLabel N ω leftBoundaryProbe d l)) :
    ancestorLabel N ω leftBoundaryProbe j k = ancestorLabel N ω leftBoundaryProbe d k := by
  exact ancestorLabel_equal_later N ω leftBoundaryProbe j d l k hlk
    ((Finset.mem_filter.mp hj).2)

theorem ancestorClade_single_split_after_attachment (N : ℕ) (ω : EventPath)
    (c i : ℕ) (x : ℝ) (hx : 0 < x) (hi : i < (ω c).1.2.2.1)
    (hev : (ω (c + 1)).2.2 = .inr (.inr (i, x)))
    (hbefore : ∀ l < c, CoalOrStop (ω (l + 1)).2.2)
    (hafter : ∀ l, c < l → CoalOrStop (ω (l + 1)).2.2)
    (q : GenomicProbe) (hq : x ≤ (q.val : ℝ)) (r d : Fin N)
    (hr : ancestorLabel N ω leftBoundaryProbe r c = liveLabelAt (ω c).1 i)
    (l : ℕ) (hcl : c < l) (ij : ℕ × ℕ)
    (hpair : (ω (l + 1)).2.2 = .inr (.inl ij))
    (hij : ij.1 < ij.2 ∧ ij.2 < (ω l).1.2.2.1)
    (hchildren :
      (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.1 ∧
        ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.2) ∨
      (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.2 ∧
        ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.1))
    (k : ℕ) (hk : l + 1 ≤ k) (a : ℕ) :
    extractionClade (fun j => ancestorLabel N ω q j k) a =
      regraftClade
        (extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j c)
          (liveLabelAt (ω c).1 i))
        (extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j l)
          (ancestorLabel N ω leftBoundaryProbe d l))
        (extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j k) a) := by
  classical
  let s := extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j c)
    (liveLabelAt (ω c).1 i)
  let target := extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j l)
    (ancestorLabel N ω leftBoundaryProbe d l)
  have hmap : (fun j => ancestorLabel N ω q j k) =
      (fun j => if j ∈ s then ancestorLabel N ω leftBoundaryProbe d k
        else ancestorLabel N ω leftBoundaryProbe j k) := by
    funext j
    simpa only [s, extractionClade, Finset.mem_filter, Finset.mem_univ, true_and] using
      ancestorLabel_single_split_after_attachment N ω c i x hx hi hev hbefore hafter
        q hq r d hr l hcl ij hpair hij hchildren j k hk
  rw [hmap]
  apply extractionClade_route_regraft
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, rfl⟩
  · intro j hj
    exact target_clade_persists N ω l k (by omega) d j hj

end Rhone.Coalescent.SmcPrime
