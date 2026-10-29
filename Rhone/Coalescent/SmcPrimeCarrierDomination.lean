/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction
public import Rhone.Coalescent.FiniteIntervalGenealogyLawSupport

/-! # Active branches and attachment rate are bounded by genomic carrier counts -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem active_branch_card_le_carriers {N : ℕ} (T : Tree N) (hu : TreeActiveUnique T)
    (t : ℝ) (ht : 0 ≤ t) (s : State) (q : ℝ) (f : Fin N → ℕ)
    (hcarried : ∀ j, ancestorCarried s q (f j))
    (hclade : ∀ i ∈ activeBranches T t, ∃ a, (T.2 i).1 = extractionClade f a) :
    (activeBranches T t).card ≤
      (Finset.univ.filter (fun k => materialContains (s.2.2.2 k).2 q)).card := by
  classical
  let A := {i : Fin T.1 // i ∈ activeBranches T t}
  let C := {k : Fin s.2.2.1 // materialContains (s.2.2.2 k).2 q}
  have hex : ∀ i : A, ∃ k : C, (T.2 i.val).1 = extractionClade f (s.2.2.2 k.val).1 := by
    intro i
    obtain ⟨a, ha⟩ := hclade i.val i.property
    have hp := (Finset.mem_filter.mp i.property).2.1
    have hne : (T.2 i.val).1 ≠ ∅ := by
      intro he
      simp [branchLength, he] at hp
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [ha] at hj
    have hja : f j = a := (Finset.mem_filter.mp hj).2
    obtain ⟨k, hkj, hkq⟩ := hcarried j
    exact ⟨⟨k, hkq⟩, by simpa only [hkj, hja] using ha⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply hu t ht i.val i.property j.val j.property
    rw [hg i, hg j, hij]
  have hc := Fintype.card_le_of_injective g hginj
  simpa [A, C, Fintype.card_subtype] using hc

theorem active_branch_count_le_carrier_sum {N : ℕ} (T : Tree N) (hu : TreeActiveUnique T)
    (t : ℝ) (ht : 0 ≤ t) (s : State) (q : ℝ) (f : Fin N → ℕ)
    (hcarried : ∀ j, ancestorCarried s q (f j))
    (hclade : ∀ i ∈ activeBranches T t, ∃ a, (T.2 i).1 = extractionClade f a) :
    ((activeBranches T t).card : ℝ) ≤
      ∑ k, if materialContains (s.2.2.2 k).2 q then (1 : ℝ) else 0 := by
  classical
  have hc := active_branch_card_le_carriers T hu t ht s q f hcarried hclade
  have he : (∑ k, if materialContains (s.2.2.2 k).2 q then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun k => materialContains (s.2.2.2 k).2 q)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  exact_mod_cast hc

theorem attachment_rate_le_carrier_sum {N : ℕ} (hN : 0 < N)
    (T : Tree N) (hu : TreeActiveUnique T) (t : ℝ) (ht : 0 ≤ t)
    (s : State) (q : ℝ) (f : Fin N → ℕ)
    (hcarried : ∀ j, ancestorCarried s q (f j))
    (hclade : ∀ i ∈ activeBranches T t, ∃ a, (T.2 i).1 = extractionClade f a) :
    attachmentRate T t ≤ ∑ k, if materialContains (s.2.2.2 k).2 q then (1 : ℝ) else 0 := by
  classical
  unfold attachmentRate
  split_ifs with hr
  · obtain ⟨k, _, hk⟩ := hcarried ⟨0, hN⟩
    have hle := Finset.single_le_sum
      (f := fun k : Fin s.2.2.1 => if materialContains (s.2.2.2 k).2 q then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    simpa only [hk, ↓reduceIte] using hle
  · exact active_branch_count_le_carrier_sum T hu t ht s q f hcarried hclade

theorem attachment_rate_le_carriers {N : ℕ} (hN : 0 < N)
    (T : Tree N) (hu : TreeActiveUnique T) (t : ℝ) (ht : 0 ≤ t)
    (ω : EventPath) (hω : ChronologicalAncestryPath N ω) (q : GenomicProbe) (k : ℕ)
    (hclade : ∀ i ∈ activeBranches T t, ∃ a,
      (T.2 i).1 = extractionClade (fun j => ancestorLabel N ω q j k) a) :
    attachmentRate T t ≤
      ∑ v, if materialContains ((ω k).1.2.2.2 v).2 (q.val : ℝ) then (1 : ℝ) else 0 := by
  exact attachment_rate_le_carrier_sum hN T hu t ht (ω k).1 (q.val : ℝ)
    (fun j => ancestorLabel N ω q j k) (fun j => hω.ancestorCarried q j k) hclade

end Rhone.Coalescent.SmcPrime
