/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGOneWordLaw

/-! # Finite event words and their pair and split fibres in the ARG recursion -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

def argFiniteWord {n : ℕ} (w : Fin n → Action) (k : ℕ) : Action :=
  if hk : k < n then w ⟨k, hk⟩ else .inl (0, 0)

theorem argFiniteWord_eval {n : ℕ} (w : Fin n → Action) (j : Fin n) :
    argFiniteWord w j.val = w j := by simp only [argFiniteWord, dite_eq_left j.isLt]

def argDecodedWord {n : ℕ} (h : ARGPrefix n) (j : Fin n) : Action :=
  (argEventAction (h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2).getD (.inl (0, 0))

theorem argDecodedWord_eq {n : ℕ} (h : ARGPrefix n) (w : Fin n → Action)
    (hh : h ∈ argWordSet n (argFiniteWord w)) : argDecodedWord h = w := by
  funext j
  have he : argEventAction (h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 = some (w j) :=
    (argFiniteWord_eval w j) ▸ hh j
  simp only [argDecodedWord, he, Option.getD_some]

theorem argPairFiber_iff (z : AugmentedState) (ij : ℕ × ℕ) :
    z ∈ argActionFiber (.inl ij) ↔ z.2.2 = .inr (.inl ij) := by
  rcases z with ⟨s, t, e⟩
  cases e with
  | inl u => simp [argActionFiber, argEventAction]
  | inr a => cases a <;> simp [argActionFiber, argEventAction]

theorem argSplitFiber_iff (z : AugmentedState) (i : ℕ) :
    z ∈ argActionFiber (.inr i) ↔ ∃ x, z.2.2 = .inr (.inr (i, x)) := by
  rcases z with ⟨s, t, e⟩
  cases e with
  | inl u => simp [argActionFiber, argEventAction]
  | inr a =>
    cases a with
    | inl ij => simp [argActionFiber, argEventAction]
    | inr ix => simp [argActionFiber, argEventAction, Prod.ext_iff]

theorem argWordOneSplit_finite {n : ℕ} (w : Fin n → Action) :
    argWordOneSplit n (argFiniteWord w) ↔ argFlatWordOneSplit w := by
  constructor
  · rintro ⟨j, hj, ⟨i, hi⟩, hp⟩
    refine ⟨⟨j, hj⟩, ⟨i, ?_⟩, ?_⟩
    · exact (argFiniteWord_eval w ⟨j, hj⟩).symm.trans hi
    · intro k hk
      obtain ⟨ij, hij⟩ := hp k.val k.isLt (by intro he; apply hk; exact Fin.ext he)
      exact ⟨ij, (argFiniteWord_eval w k) ▸ hij⟩
  · rintro ⟨j, ⟨i, hi⟩, hp⟩
    refine ⟨j.val, j.isLt, ⟨i, ?_⟩, ?_⟩
    · rw [argFiniteWord_eval]; exact hi
    · intro k hk hkj
      obtain ⟨ij, hij⟩ := hp ⟨k, hk⟩ (by intro he; apply hkj; exact congrArg Fin.val he)
      exact ⟨ij, (argFiniteWord_eval w ⟨k, hk⟩).trans hij⟩

theorem argWordSector_implies_prefix (N : ℕ) (h : ARGPrefix (N + 1))
    (w : Fin (N + 1) → Action) (hw : argFlatWordOneSplit w)
    (hh : h ∈ argWordSet (N + 1) (argFiniteWord w))
    (hc : (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.2.2.1 = 1) :
    h ∈ oneSplitPrefixSector N := by
  obtain ⟨s, ⟨i, hi⟩, hp⟩ := hw
  refine ⟨⟨s, ?_, ?_⟩, hc⟩
  · have hs := hh s
    rw [argFiniteWord_eval, hi, argSplitFiber_iff] at hs
    obtain ⟨x, hx⟩ := hs
    simp only [hx, splitSet, Set.mem_ofPred_eq]
  · intro k hk
    obtain ⟨ij, hij⟩ := hp k hk
    have hs := hh k
    rw [argFiniteWord_eval, hij, argPairFiber_iff] at hs
    simp only [hs, coalSet, Set.mem_ofPred_eq]

theorem argPrefixSector_decoded (N : ℕ) (h : ARGPrefix (N + 1))
    (hh : h ∈ oneSplitPrefixSector N) :
    argFlatWordOneSplit (argDecodedWord h) ∧
      h ∈ argWordSet (N + 1) (argFiniteWord (argDecodedWord h)) := by
  obtain ⟨⟨s, hs, hp⟩, _⟩ := hh
  have hsplit : ∃ i x,
      (h ⟨s.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 = .inr (.inr (i, x)) := by
    cases he : (h ⟨s.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 with
    | inl u => simp [he, splitSet] at hs
    | inr a =>
      cases a with
      | inl ij => simp [he, splitSet] at hs
      | inr ix => exact ⟨ix.1, ix.2, rfl⟩
  have hpair (k : Fin (N + 1)) (hk : k ≠ s) : ∃ ij,
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 = .inr (.inl ij) := by
    have hc := hp k hk
    cases he : (h ⟨k.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 with
    | inl u => simp [he, coalSet] at hc
    | inr a =>
      cases a with
      | inl ij => exact ⟨ij, rfl⟩
      | inr ix => simp [he, coalSet] at hc
  obtain ⟨i, x, hx⟩ := hsplit
  constructor
  · refine ⟨s, ⟨i, ?_⟩, ?_⟩
    · simp only [argDecodedWord, hx, argEventAction, Option.getD_some]
    · intro k hk
      obtain ⟨ij, hij⟩ := hpair k hk
      exact ⟨ij, by simp only [argDecodedWord, hij, argEventAction, Option.getD_some]⟩
  · intro k
    rw [argFiniteWord_eval]
    by_cases hk : k = s
    · subst k
      simp only [argActionFiber, Set.mem_ofPred_eq, argDecodedWord, hx,
        argEventAction, Option.getD_some]
    · obtain ⟨ij, hij⟩ := hpair k hk
      simp only [argActionFiber, Set.mem_ofPred_eq, argDecodedWord, hij,
        argEventAction, Option.getD_some]
end Rhone.Coalescent.SmcPrime
