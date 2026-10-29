/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitLeftInventory
public import Rhone.Coalescent.SmcPrimeOneSplitSuccessorUIDs

/-! # Split and pair successors preserve the left-carrier inventory -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ARGLeftInventory.sample_lt_fresh {N : ℕ} {s : State} {f : Fin N → ℕ}
    {d : Option ℕ} (h : ARGLeftInventory s f d) (hs : Valid s) (a : Fin N) :
    f a < s.2.1 := by
  obtain ⟨i, hi⟩ := h.1 a
  rw [← hi]
  exact hs.2.2.1 i

theorem ARGLeftInventory.split {N : ℕ} {s : State} {f : Fin N → ℕ}
    (h : ARGLeftInventory s f none) (hs : Valid s) (i : Fin s.2.2.1) (x : ℝ) :
    ARGLeftInventory (splitSuccessor s i x)
      (fun a => if f a = (s.2.2.2 i).1 then s.2.1 else f a) (some (s.2.1 + 1)) := by
  classical
  let g := fun a => if f a = (s.2.2.2 i).1 then s.2.1 else f a
  have hparent : ∃ a, f a = (s.2.2.2 i).1 := by
    rcases h.2.1 i with ha | hn
    · exact ha
    · cases hn
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (splitSuccessor_uid_present s hs i x (g a)).mpr
    by_cases ha : f a = (s.2.2.2 i).1
    · exact Or.inl (ite_eq_left ha)
    · have hh : f a = s.2.1 ∨ f a = s.2.1 + 1 ∨
          ((∃ k, (s.2.2.2 k).1 = f a) ∧ f a ≠ (s.2.2.2 i).1) :=
        Or.inr (Or.inr ⟨h.1 a, ha⟩)
      simpa only [g, ite_eq_right ha] using hh
  · intro k
    rcases (splitSuccessor_uid_present s hs i x _).mp ⟨k, rfl⟩ with ha | ha | ⟨⟨v, hv⟩, hn⟩
    · obtain ⟨a, hap⟩ := hparent
      exact Or.inl ⟨a, by change g a = _; simp only [g, ite_eq_left hap]; exact ha.symm⟩
    · exact Or.inr (congrArg some ha.symm)
    · rcases h.2.1 v with ⟨a, hav⟩ | hd
      · have hna : f a ≠ (s.2.2.2 i).1 := by rw [hav, hv]; exact hn
        exact Or.inl ⟨a, by change g a = _; simp only [g, ite_eq_right hna, hav, hv]⟩
      · cases hd
  · intro b hb
    have hbe : b = s.2.1 + 1 := (Option.some.inj hb).symm
    subst b
    refine ⟨(splitSuccessor_uid_present s hs i x _).mpr (Or.inr (Or.inl rfl)), ?_⟩
    intro a
    change g a ≠ s.2.1 + 1
    have haf := h.sample_lt_fresh hs a
    by_cases ha : f a = (s.2.2.2 i).1 <;> simp only [g, ha, ite_true, ite_false] <;> omega

theorem ARGLeftInventory.coal {N : ℕ} {s : State} {f : Fin N → ℕ} {d : Option ℕ}
    (h : ARGLeftInventory s f d) (hs : Valid s)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) :
    ARGLeftInventory (coalSuccessor s i j)
      (fun a => if f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1 then s.2.1 else f a)
      (if d = some (s.2.2.2 i).1 ∨ d = some (s.2.2.2 j).1 then none else d) := by
  classical
  let g := fun a => if f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1 then s.2.1 else f a
  let d' := if d = some (s.2.2.2 i).1 ∨ d = some (s.2.2.2 j).1 then none else d
  have hpne : (s.2.2.2 i).1 ≠ (s.2.2.2 j).1 := by
    intro he
    exact (ne_of_lt hij) (congrArg Fin.val (hs.2.2.2 he))
  have hparent : ∃ a, f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1 := by
    rcases h.2.1 i with ⟨a, ha⟩ | hdi
    · exact ⟨a, Or.inl ha⟩
    · rcases h.2.1 j with ⟨a, ha⟩ | hdj
      · exact ⟨a, Or.inr ha⟩
      · exact False.elim (hpne (Option.some.inj (hdi.symm.trans hdj)))
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (coalSuccessor_uid_present s hs i j hij (g a)).mpr
    by_cases ha : f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1
    · exact Or.inl (ite_eq_left ha)
    · simpa only [g, ite_eq_right ha] using
        (Or.inr ⟨h.1 a, fun hi => ha (Or.inl hi), fun hj => ha (Or.inr hj)⟩ :
          g a = s.2.1 ∨ ((∃ k, (s.2.2.2 k).1 = f a) ∧
            f a ≠ (s.2.2.2 i).1 ∧ f a ≠ (s.2.2.2 j).1))
  · intro k
    rcases (coalSuccessor_uid_present s hs i j hij _).mp ⟨k, rfl⟩ with ha | ⟨⟨v, hv⟩, hni, hnj⟩
    · obtain ⟨a, hap⟩ := hparent
      exact Or.inl ⟨a, by change g a = _; simp only [g, ite_eq_left hap]; exact ha.symm⟩
    · rcases h.2.1 v with ⟨a, hav⟩ | hd
      · have hn : ¬ (f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1) := by
          rw [hav, hv]
          exact fun hh => hh.elim hni hnj
        exact Or.inl ⟨a, by change g a = _; simp only [g, ite_eq_right hn, hav, hv]⟩
      · have hn : ¬ (d = some (s.2.2.2 i).1 ∨ d = some (s.2.2.2 j).1) := by
          rw [hd, hv]
          simp only [Option.some.injEq]
          exact fun hh => hh.elim hni hnj
        exact Or.inr (by change d' = _; simp only [d', ite_eq_right hn, hd, hv])
  · intro b hb
    have hno : ¬ (d = some (s.2.2.2 i).1 ∨ d = some (s.2.2.2 j).1) := by
      intro hh
      change d' = some b at hb
      simp only [d', ite_eq_left hh] at hb
      cases hb
    have hd : d = some b := by
      change d' = some b at hb
      simpa only [d', ite_eq_right hno] using hb
    obtain ⟨hbpre, hn⟩ := h.2.2 b hd
    have hbi : b ≠ (s.2.2.2 i).1 := fun he => hno (Or.inl (hd.trans (congrArg some he)))
    have hbj : b ≠ (s.2.2.2 j).1 := fun he => hno (Or.inr (hd.trans (congrArg some he)))
    have hbf : b < s.2.1 := by
      obtain ⟨v, hv⟩ := hbpre
      rw [← hv]
      exact hs.2.2.1 v
    refine ⟨(coalSuccessor_uid_present s hs i j hij b).mpr (Or.inr ⟨hbpre, hbi, hbj⟩), ?_⟩
    intro a
    change g a ≠ b
    by_cases ha : f a = (s.2.2.2 i).1 ∨ f a = (s.2.2.2 j).1
    · simp only [g, ite_eq_left ha]
      omega
    · simp only [g, ite_eq_right ha]
      exact hn a

end Rhone.Coalescent.SmcPrime
