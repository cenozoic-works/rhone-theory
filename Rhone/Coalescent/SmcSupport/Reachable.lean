/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Material

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess
open SmcSpan

inductive MaterialReachable (x : ℝ) : List (Span × Material) → Prop
  | initial (as : List Material) : (∀ a ∈ as, FullAtoms a) →
      MaterialReachable x (as.map (fun a => (Span.full, a)))
  | firstSplit (a : Material) (as : List Material) :
      FullAtoms a → (∀ b ∈ as, FullAtoms b) →
      MaterialReachable x ((Span.left, (splitMaterial a x).1) ::
        (Span.right, (splitMaterial a x).2) :: as.map (fun b => (Span.full, b)))
  | perm {s t} : MaterialReachable x s → s.Perm t → MaterialReachable x t
  | coalesce {a b : Span × Material} {s} : MaterialReachable x (a :: b :: s) →
      MaterialReachable x ((merge a.1 b.1, mergeMaterial a.2 b.2) :: s)

theorem materialReachable_labels (x : ℝ) {s : List (Span × Material)}
    (hs : MaterialReachable x s) : Reachable (s.map Prod.fst) := by
  induction hs with
  | initial as ha =>
    simpa using Reachable.initial as.length
  | firstSplit a as ha has =>
    simpa using Reachable.firstSplit as.length
  | perm hs hp ih => exact Reachable.perm ih (hp.map Prod.fst)
  | coalesce hs ih => exact Reachable.coalesce ih

theorem materialReachable_tagged (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : List (Span × Material)} (hs : MaterialReachable x s) :
    ∀ a ∈ s, Tagged x a.2 a.1 := by
  induction hs with
  | initial as ha =>
    intro a ha'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha'
    exact Tagged.full b (ha b hb)
  | firstSplit a as ha has =>
    obtain ⟨hl, hr⟩ := first_split_atoms a ha x hx0 hx1
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact Tagged.left _ hl
    · exact Tagged.right _ hr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact Tagged.full c (has c hc)
  | perm hs hp ih =>
    intro a ha
    exact ih a (hp.mem_iff.mpr ha)
  | @coalesce a b s hs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Tagged.merge (ih a (by simp)) (ih b (by simp))
    · exact ih c (by simp [hc])

theorem materialReachable_contacts (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : List (Span × Material)} (hs : MaterialReachable x s) :
    s.Pairwise (fun a b => touches a.2 b.2) := by
  have hv := reachable_valid _ (materialReachable_labels x hs)
  have ht := materialReachable_tagged x hx0 hx1 hs
  have hv' : s.Pairwise (fun a b => Compatible a.1 b.1) := by
    simpa only [Rhone.Coalescent.SmcSpan.Valid, List.pairwise_map] using hv
  exact hv'.imp_of_mem (fun ha hb huv =>
    tagged_contact x hx0 hx1 (ht _ ha) (ht _ hb) huv)

end Rhone.Coalescent.SmcSupport
