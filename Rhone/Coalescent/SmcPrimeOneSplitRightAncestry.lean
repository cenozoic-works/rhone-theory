/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction

/-! # Right-sample ancestry after the single split -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

def CoalOrStop (e : Event) : Prop :=
  e = .inl () ∨ ∃ ij : ℕ × ℕ, e = .inr (.inl ij)

theorem ancestorStep_coalOrStop (s : State) (e : Event) (he : CoalOrStop e)
    (q p : GenomicProbe) (a : ℕ) : ancestorStep s e q a = ancestorStep s e p a := by
  rcases he with rfl | ⟨ij, rfl⟩ <;> rfl

theorem ancestorLabel_no_split_prefix (N : ℕ) (ω : EventPath) (k : ℕ)
    (hstep : ∀ l < k, CoalOrStop (ω (l + 1)).2.2)
    (q p : GenomicProbe) (i : Fin N) :
    ancestorLabel N ω q i k = ancestorLabel N ω p i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q i k) =
      ancestorStep (ω k).1 (ω (k + 1)).2.2 p (ancestorLabel N ω p i k)
    rw [ancestorStep_coalOrStop _ _ (hstep k (by omega)) q p,
      ih (fun l hl => hstep l (by omega))]

theorem ancestorLabel_cross_probe_later (N : ℕ) (ω : EventPath)
    (q p : GenomicProbe) (i j : Fin N) (l k : ℕ) (hlk : l ≤ k)
    (hstep : ∀ m, l ≤ m → CoalOrStop (ω (m + 1)).2.2)
    (heq : ancestorLabel N ω q i l = ancestorLabel N ω p j l) :
    ancestorLabel N ω q i k = ancestorLabel N ω p j k := by
  induction k, hlk using Nat.le_induction with
  | base => exact heq
  | succ k hk ih =>
    change ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q i k) =
      ancestorStep (ω k).1 (ω (k + 1)).2.2 p (ancestorLabel N ω p j k)
    rw [ancestorStep_coalOrStop _ _ (hstep k hk) q p, ih]

theorem ancestorLabel_single_split_right (N : ℕ) (ω : EventPath)
    (c i : ℕ) (x : ℝ) (hx : 0 < x) (hi : i < (ω c).1.2.2.1)
    (hev : (ω (c + 1)).2.2 = .inr (.inr (i, x)))
    (hbefore : ∀ l < c, CoalOrStop (ω (l + 1)).2.2)
    (hafter : ∀ l, c < l → CoalOrStop (ω (l + 1)).2.2)
    (q : GenomicProbe) (hq : x ≤ (q.val : ℝ)) (r : Fin N)
    (hr : ancestorLabel N ω leftBoundaryProbe r c = liveLabelAt (ω c).1 i)
    (j : Fin N) (k : ℕ) (hk : c + 1 ≤ k) :
    ancestorLabel N ω q j k =
      if ancestorLabel N ω leftBoundaryProbe j c = liveLabelAt (ω c).1 i
      then ancestorLabel N ω q r k else ancestorLabel N ω leftBoundaryProbe j k := by
  classical
  induction k, hk using Nat.le_induction with
  | base =>
    have hqj := ancestorLabel_no_split_prefix N ω c hbefore q leftBoundaryProbe j
    have hqr := ancestorLabel_no_split_prefix N ω c hbefore q leftBoundaryProbe r
    have hl : (leftBoundaryProbe.val : ℝ) < x := by simpa [leftBoundaryProbe] using hx
    simp only [ancestorLabel, hev, ancestorStep, hi, true_and, hqj, hqr, hr,
      not_lt.mpr hq, hl, ↓reduceIte]
    split_ifs <;> rfl
  | succ k hk ih =>
    by_cases hj : ancestorLabel N ω leftBoundaryProbe j c = liveLabelAt (ω c).1 i
    · simp only [hj, ↓reduceIte] at ih ⊢
      change ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q j k) =
        ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q r k)
      rw [ih]
    · simp only [hj, ↓reduceIte] at ih ⊢
      change ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q j k) =
        ancestorStep (ω k).1 (ω (k + 1)).2.2 leftBoundaryProbe
          (ancestorLabel N ω leftBoundaryProbe j k)
      rw [ancestorStep_coalOrStop _ _ (hafter k (by omega)) q leftBoundaryProbe, ih]

theorem ancestorLabel_pair_links (N : ℕ) (ω : EventPath) (l : ℕ)
    (q p : GenomicProbe) (r d : Fin N) (ij : ℕ × ℕ)
    (hev : (ω (l + 1)).2.2 = .inr (.inl ij))
    (hij : ij.1 < ij.2 ∧ ij.2 < (ω l).1.2.2.1)
    (hchildren :
      (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.1 ∧
        ancestorLabel N ω p d l = liveLabelAt (ω l).1 ij.2) ∨
      (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.2 ∧
        ancestorLabel N ω p d l = liveLabelAt (ω l).1 ij.1)) :
    ancestorLabel N ω q r (l + 1) = ancestorLabel N ω p d (l + 1) := by
  rcases hchildren with ⟨hr, hd⟩ | ⟨hr, hd⟩ <;>
    simp only [ancestorLabel, hev, ancestorStep, hij, ↓reduceIte, hr, hd, true_or, or_true,
      and_self]

theorem ancestorLabel_single_split_after_attachment (N : ℕ) (ω : EventPath)
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
    (j : Fin N) (k : ℕ) (hk : l + 1 ≤ k) :
    ancestorLabel N ω q j k =
      if ancestorLabel N ω leftBoundaryProbe j c = liveLabelAt (ω c).1 i
      then ancestorLabel N ω leftBoundaryProbe d k
      else ancestorLabel N ω leftBoundaryProbe j k := by
  have heq := ancestorLabel_pair_links N ω l q leftBoundaryProbe r d ij hpair hij hchildren
  have hlater := ancestorLabel_cross_probe_later N ω q leftBoundaryProbe r d (l + 1) k hk
    (fun m hm => hafter m (by omega)) heq
  rw [ancestorLabel_single_split_right N ω c i x hx hi hev hbefore hafter q hq r hr j k
    (by omega), hlater]

end Rhone.Coalescent.SmcPrime
