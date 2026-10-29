/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.GeiringerMarginal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
/-!
# Three-locus single-crossover cumulants

Source: geiringer1944, eq. (61)–(63), p. 53. -/
@[expose] public section
namespace Rhone.MarkovChain.ThreeLocus
open scoped BigOperators
/-- Source: geiringer1944, eq. (61)–(63), p. 53, eq. (31), p. 39. -/
noncomputable def singleCrossoverMask (r1 r2 : ℝ) (B : Finset (Fin 3)) : ℝ :=
  (if B = Finset.univ then 1 - r1 - r2 else 0)+
  (if B={0} then r1 else 0) + (if B={0, 1} then r2 else 0)
/-- Source: geiringer1944, eq. (61)–(63), p. 53, eq. (31), p. 39. -/
noncomputable def singleCrossoverStep (r1 r2 : ℝ)
  (p : (Fin 3 → Bool) → ℝ) : (Fin 3 → Bool) → ℝ :=
  Geiringer.recombination (singleCrossoverMask r1 r2) p
noncomputable def alleleMoment (p : (Fin 3 → Bool) → ℝ) (B : Finset (Fin 3)) : ℝ :=
  Geiringer.marginal p B (fun _ => true)
noncomputable def pairDisequilibrium (p : (Fin 3 → Bool) → ℝ) (i j : Fin 3) : ℝ :=
  alleleMoment p {i, j}-alleleMoment p {i}*alleleMoment p {j}
noncomputable def thirdCumulant (p : (Fin 3 → Bool) → ℝ) : ℝ :=
  alleleMoment p {0, 1, 2}-alleleMoment p {0}*alleleMoment p {1, 2}-
  alleleMoment p {1}*alleleMoment p {0, 2}-alleleMoment p {2}*alleleMoment p {0, 1}+
  2 * alleleMoment p {0}*alleleMoment p {1}*alleleMoment p {2}
/-- Source: geiringer1944, eq. (61)–(63), p. 53, eq. (31), p. 39. -/
noncomputable def singleCrossoverIter (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ) :
  ℕ → ((Fin 3 → Bool) → ℝ)
  | 0 => p
  | n + 1 => singleCrossoverStep r1 r2 (singleCrossoverIter r1 r2 p n)

/-- Source: geiringer1944, eq. (63), p. 53. -/
theorem single_crossover_mask_probability {r1 r2 : ℝ}
    (h1 : 0 ≤ r1) (h2 : 0 ≤ r2) (hs : r1 + r2 ≤ 1) :
    (∀ B, 0 ≤ singleCrossoverMask r1 r2 B) ∧ ∑ B, singleCrossoverMask r1 r2 B = 1 := by
  constructor
  · intro B
    unfold singleCrossoverMask
    split_ifs <;> linarith
  · simp [singleCrossoverMask, Finset.sum_add_distrib]
    ring

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem single_crossover_mass (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) : ∑ h, singleCrossoverStep r1 r2 p h = 1 := by
  have h := Geiringer.recombination_expectation (singleCrossoverMask r1 r2) p (fun _ => 1)
  simp only [mul_one, ← Finset.mul_sum, hp] at h
  unfold singleCrossoverStep
  rw [h]
  simp [singleCrossoverMask, Finset.sum_add_distrib]
  ring

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem single_crossover_probability {r1 r2 : ℝ} (p : (Fin 3 → Bool) → ℝ)
    (h1 : 0 ≤ r1) (h2 : 0 ≤ r2) (hs : r1 + r2 ≤ 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1) :
    (∀ h, 0 ≤ singleCrossoverStep r1 r2 p h) ∧ ∑ h, singleCrossoverStep r1 r2 p h = 1 := by
  obtain ⟨hρ0, hρ⟩ := single_crossover_mask_probability h1 h2 hs
  exact Geiringer.recombination_preserves_distribution _ _ hρ0 hρ hp0 hp

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem single_crossover_moment (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (B : Finset (Fin 3)) :
    alleleMoment (singleCrossoverStep r1 r2 p) B =
      (1 - r1 - r2) * alleleMoment p B * alleleMoment p ∅ +
      r1 * alleleMoment p (B ∩ {0}) * alleleMoment p (B \ {0}) +
      r2 * alleleMoment p (B ∩ {0, 1}) * alleleMoment p (B \ {0, 1}) := by
  unfold alleleMoment singleCrossoverStep
  rw [Geiringer.marginal_recombination_split]
  have hu : B \ Finset.univ = ∅ := by ext i; simp
  simp [singleCrossoverMask, add_mul, ite_mul, Finset.sum_add_distrib, hu]

/-- Source: geiringer1944, eq. (31), p. 39. -/
theorem single_crossover_singletons (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) (i : Fin 3) :
    alleleMoment (singleCrossoverStep r1 r2 p) {i} = alleleMoment p {i} := by
  have hempty : alleleMoment p ∅ = 1 := by simpa [alleleMoment, Geiringer.marginal] using hp
  rw [single_crossover_moment]
  fin_cases i <;> simp [Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, hempty] <;> ring

theorem single_crossover_pair_recurrence (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) :
    pairDisequilibrium (singleCrossoverStep r1 r2 p) 0 1 = (1 - r1) * pairDisequilibrium p 0 1 ∧
    pairDisequilibrium (singleCrossoverStep r1 r2 p) 1 2 = (1 - r2) * pairDisequilibrium p 1 2 ∧
    pairDisequilibrium (singleCrossoverStep r1 r2 p) 0 2 =
      (1 - r1 - r2) * pairDisequilibrium p 0 2 := by
  have hempty : alleleMoment p ∅ = 1 := by simpa [alleleMoment, Geiringer.marginal] using hp
  have hsingle := single_crossover_singletons r1 r2 p hp
  unfold pairDisequilibrium
  simp only [hsingle, single_crossover_moment]
  constructor
  · simp [Finset.sdiff_singleton_eq_erase, hempty]
    ring
  · constructor
    · simp [Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, hempty]
      ring
    · simp [Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, hempty]
      ring

theorem single_crossover_third_recurrence (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) :
    thirdCumulant (singleCrossoverStep r1 r2 p) = (1 - r1 - r2) * thirdCumulant p := by
  have hempty : alleleMoment p ∅ = 1 := by simpa [alleleMoment, Geiringer.marginal] using hp
  have hsingle := single_crossover_singletons r1 r2 p hp
  have he : (({0, 1, 2} : Finset (Fin 3)).erase 1).erase 0 = {2} := by decide
  unfold thirdCumulant
  simp only [hsingle, single_crossover_moment]
  simp [Finset.sdiff_insert, Finset.sdiff_singleton_eq_erase, hempty, he]
  ring

theorem single_crossover_third_iter (r1 r2 : ℝ) (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) (n : ℕ) :
    thirdCumulant (singleCrossoverIter r1 r2 p n) = (1 - r1 - r2) ^ n * thirdCumulant p := by
  have hmass (k : ℕ) : ∑ h, singleCrossoverIter r1 r2 p k h = 1 := by
    induction k with
    | zero => exact hp
    | succ k hk => exact single_crossover_mass r1 r2 _ hk
  induction n with
  | zero => simp [singleCrossoverIter]
  | succ n hn =>
    rw [singleCrossoverIter, single_crossover_third_recurrence r1 r2 _ (hmass n), hn]
    ring

/-- Source: geiringer1944, Thm. II, p. 42. -/
theorem single_crossover_disequilibrium_tendsto {r1 r2 : ℝ} (p : (Fin 3 → Bool) → ℝ)
    (hp : ∑ h, p h = 1) (h1 : 0 < r1) (h2 : 0 < r2) (hs : r1 + r2 ≤ 1) :
    Filter.Tendsto (fun n => pairDisequilibrium (singleCrossoverIter r1 r2 p n) 0 1)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => pairDisequilibrium (singleCrossoverIter r1 r2 p n) 1 2)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => pairDisequilibrium (singleCrossoverIter r1 r2 p n) 0 2)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => thirdCumulant (singleCrossoverIter r1 r2 p n))
      Filter.atTop (nhds 0) := by
  have hmass (k : ℕ) : ∑ h, singleCrossoverIter r1 r2 p k h = 1 := by
    induction k with
    | zero => exact hp
    | succ k hk => exact single_crossover_mass r1 r2 _ hk
  have hiter (f : ((Fin 3 → Bool) → ℝ) → ℝ) (c : ℝ)
      (hf : ∀ q, (∑ h, q h) = 1 → f (singleCrossoverStep r1 r2 q) = c * f q)
      (k : ℕ) : f (singleCrossoverIter r1 r2 p k) = c ^ k * f p := by
    induction k with
    | zero => simp [singleCrossoverIter]
    | succ k hk => rw [singleCrossoverIter, hf _ (hmass k), hk]; ring
  have hlim (f : ((Fin 3 → Bool) → ℝ) → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
      (hf : ∀ q, (∑ h, q h) = 1 → f (singleCrossoverStep r1 r2 q) = c * f q) :
      Filter.Tendsto (fun k => f (singleCrossoverIter r1 r2 p k)) Filter.atTop (nhds 0) := by
    simp only [hiter f c hf]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (f p)
  refine ⟨hlim (fun q => pairDisequilibrium q 0 1) (1 - r1)
    (by linarith) (by linarith) (fun q hq => (single_crossover_pair_recurrence r1 r2 q hq).1), ?_⟩
  refine ⟨hlim (fun q => pairDisequilibrium q 1 2) (1 - r2)
    (by linarith) (by linarith) (fun q hq => (single_crossover_pair_recurrence r1 r2 q hq).2.1), ?_⟩
  refine ⟨hlim (fun q => pairDisequilibrium q 0 2) (1 - r1 - r2)
    (by linarith) (by linarith) (fun q hq => (single_crossover_pair_recurrence r1 r2 q hq).2.2), ?_⟩
  exact hlim thirdCumulant (1 - r1 - r2) (by linarith) (by linarith)
    (single_crossover_third_recurrence r1 r2)

end Rhone.MarkovChain.ThreeLocus
