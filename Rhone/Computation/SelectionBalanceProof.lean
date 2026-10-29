/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SelectionBalance
public import Rhone.Dynamics.MutationSelection
public import Rhone.Dynamics.IslandGenicSelection
public import Rhone.Dynamics.SelectionTwoDeme
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable selection balance equals the specification

Source: haldane1927, pp. 840–841, eq. (2.0); felsenstein_teg2019, sec. III.5, eq. (III-18), p. 147,
eq. (III-23), p. 150; crow_kimura1970, sec. 6.5; burger2013_migration_selection, sec. 4. -/

@[expose] public section
namespace Rhone.Computation.SelectionBalance

theorem hapMutSelStep_eq (s mu q : Rat) :
    hapMutSelStep s mu q = Rhone.Dynamics.hapMutSelStep s mu q := rfl

theorem dipMutSelStep_eq (h s mu q : Rat) :
    dipMutSelStep h s mu q = Rhone.Dynamics.dipMutSelStep h s mu q := rfl

theorem hapMutSelStep_cast (s mu q : Rat) :
    ((hapMutSelStep s mu q : Rat) : ℝ) =
      Rhone.Dynamics.hapMutSelStep (s : ℝ) (mu : ℝ) (q : ℝ) := by
  unfold hapMutSelStep Rhone.Dynamics.hapMutSelStep
  push_cast
  rfl

theorem dipMutSelStep_cast (h s mu q : Rat) :
    ((dipMutSelStep h s mu q : Rat) : ℝ) =
      Rhone.Dynamics.dipMutSelStep (h : ℝ) (s : ℝ) (mu : ℝ) (q : ℝ) := by
  unfold dipMutSelStep Rhone.Dynamics.dipMutSelStep
  push_cast
  rfl

theorem hapEquilibrium_fixed (s mu : Rat) (hs : s ≠ 0) (hmu : mu ≠ 1) :
    hapMutSelStep s mu (hapEquilibrium s mu) = hapEquilibrium s mu :=
  Rhone.Dynamics.hapMutSelStep_fixed hs hmu

theorem hapMutSelStep_eq_iff (s mu q : Rat) (hs : s ≠ 0) (h : 1 - s * q ≠ 0) :
    hapMutSelStep s mu q = q ↔ q = 1 ∨ q = hapEquilibrium s mu :=
  Rhone.Dynamics.hapMutSelStep_eq_iff hs h

theorem dipMutSelStep_fixed_iff (h s mu q : Rat) (hW : dipMeanFit h s q ≠ 0) :
    dipMutSelStep h s mu q = q ↔ dipFixedCandidate h s mu q = true := by
  have key := Rhone.Dynamics.dipMutSelStep_eq_iff h s mu q hW
  unfold dipFixedCandidate
  rw [decide_eq_true_iff, dipMutSelStep_eq, key]
  unfold dipFixedResidual
  constructor
  · rintro (h1 | h1)
    · exact Or.inl h1
    · exact Or.inr (by linear_combination -h1)
  · rintro (h1 | h1)
    · exact Or.inl h1
    · exact Or.inr (by linear_combination -h1)

theorem recessive_fixed_iff (s mu q : Rat) (hs : s ≠ 0) (hW : 1 - s * q ^ 2 ≠ 0) :
    dipMutSelStep 0 s mu q = q ↔ q = 1 ∨ q ^ 2 = recessiveEquilibriumSq s mu :=
  Rhone.Dynamics.recessive_mutSel_fixed_iff hs hW

theorem islandGenicStep_cast (s m p : Rat) :
    ((islandGenicStep s m p : Rat) : ℝ) =
      Rhone.Dynamics.islandGenicStep (s : ℝ) (m : ℝ) (p : ℝ) := by
  unfold islandGenicStep Rhone.Dynamics.islandGenicStep
  push_cast
  rfl

theorem islandGenicStep_fixed_iff (s m p : Rat) (hs0 : 0 < s) (hs1 : s < 1) (hm0 : 0 ≤ m)
    (hm1 : m < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    islandGenicStep s m p = p ↔ p = 0 ∨ p = 1 - m / s := by
  have key := Rhone.Dynamics.island_genic_fixed_iff (s := (s : ℝ)) (m := (m : ℝ)) (p := (p : ℝ))
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) (by exact_mod_cast hm0)
    (by exact_mod_cast hm1) ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  rw [← islandGenicStep_cast] at key
  constructor
  · intro h
    have h' := key.1 (by rw [h])
    rcases h' with h' | h'
    · exact Or.inl (by exact_mod_cast h')
    · exact Or.inr (by exact_mod_cast h')
  · intro h
    apply Rat.cast_injective (α := ℝ)
    apply key.2
    rcases h with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [h]; push_cast; rfl)

theorem islandPositiveEquilibrium_spec (s m : Rat) (hs0 : 0 < s) (hs1 : s < 1) (hm0 : 0 ≤ m)
    (hm1 : m < 1) :
    (m < s → ∃ q, islandPositiveEquilibrium s m = some q ∧ q = 1 - m / s ∧ 0 < q ∧ q ≤ 1 ∧
        islandGenicStep s m q = q) ∧
      (¬ m < s → islandPositiveEquilibrium s m = none ∧
        ∀ p : Rat, 0 < p → p ≤ 1 → islandGenicStep s m p ≠ p) := by
  refine ⟨fun hlt => ?_, fun hnl => ⟨by simp [islandPositiveEquilibrium, hnl], ?_⟩⟩
  · have hq1 : 1 - m / s ≤ 1 := by
      have : 0 ≤ m / s := div_nonneg hm0 hs0.le
      linarith
    have hq0 : 0 < 1 - m / s := by
      have : m / s < 1 := (div_lt_one hs0).2 hlt
      linarith
    refine ⟨1 - m / s, by simp [islandPositiveEquilibrium, hlt], rfl, hq0, hq1, ?_⟩
    exact (islandGenicStep_fixed_iff s m _ hs0 hs1 hm0 hm1 hq0.le hq1).2 (Or.inr rfl)
  · intro p hp0 hp1 hfix
    rcases (islandGenicStep_fixed_iff s m p hs0 hs1 hm0 hm1 hp0.le hp1).1 hfix with h | h
    · exact absurd h hp0.ne'
    · apply hnl
      have : m / s < 1 := by linarith
      exact (div_lt_one hs0).1 this

theorem twoDemeFirst_cast (s m p q : Rat) :
    ((twoDemeFirst s m p q : Rat) : ℝ) =
      Rhone.Dynamics.twoDemeFirst (s : ℝ) (m : ℝ) (p : ℝ) (q : ℝ) := by
  unfold twoDemeFirst Rhone.Dynamics.twoDemeFirst
  push_cast
  rfl

theorem twoDemeSecond_cast (s m p q : Rat) :
    ((twoDemeSecond s m p q : Rat) : ℝ) =
      Rhone.Dynamics.twoDemeSecond (s : ℝ) (m : ℝ) (p : ℝ) (q : ℝ) := by
  unfold twoDemeSecond Rhone.Dynamics.twoDemeSecond
  push_cast
  rfl

theorem twoDemeQuadratic_cast (s m p : Rat) :
    ((twoDemeQuadratic s m p : Rat) : ℝ) =
      (s : ℝ) * (p : ℝ) ^ 2 + (2 * (m : ℝ) + (m : ℝ) * (s : ℝ) - (s : ℝ)) * (p : ℝ) - (m : ℝ) := by
  unfold twoDemeQuadratic
  push_cast
  rfl

theorem twoDemeQuadratic_root_iff (s m p : Rat) (hs : 0 < s) (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hp : 0 ≤ p) :
    twoDemeQuadratic s m p = 0 ↔
      (p : ℝ) = Rhone.Dynamics.twoDemeEquilibrium (s : ℝ) (m : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm1' : (m : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 hm1
    simpa using this
  constructor
  · intro h
    have h' := twoDemeQuadratic_cast s m p
    rw [h, Rat.cast_zero] at h'
    exact Rhone.Dynamics.two_deme_equilibrium_unique_nonneg hs' hm0' hm1' (by exact_mod_cast hp)
      h'.symm
  · intro h
    apply Rat.cast_injective (α := ℝ)
    rw [twoDemeQuadratic_cast, h, Rat.cast_zero]
    exact Rhone.Dynamics.two_deme_equilibrium_polynomial hs' hm0' hm1'

end Rhone.Computation.SelectionBalance
