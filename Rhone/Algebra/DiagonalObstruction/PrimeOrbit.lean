/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.PrimeGaps
public import Rhone.Algebra.DiagonalObstruction.ReflectionOrbit
public import Rhone.Algebra.DiagonalObstruction.CollisionLabels

/-! # Collision-closed index sets and prime parameters for unbounded components -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

def CollisionClosed (m : ℕ) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → m < p → ∀ i ∈ S, i ≤ m → ∀ j ≤ m,
    (p : ℤ) ∣ coalDiag m i - coalDiag m j → j ∈ S

theorem exists_collision_parameters (D : ℕ) :
    ∃ m p q c h : ℕ, 2 ≤ m ∧ p.Prime ∧ q.Prime ∧ m < p ∧ p < q ∧
      0 < h ∧ c + 2 * q + 1 = 4 * m ∧
      c + h + 2 * p + 1 = 4 * m ∧ c + h ≤ m ∧ (D + 1) * h ≤ c + h := by
  obtain ⟨p, q, hp, hq, hpbig, hpq, hgap⟩ :=
    exists_prime_pair_mul_gap_lt (32 * (D + 1)) 280
  let δ := q - p
  have hδ : 0 < δ := by dsimp [δ]; omega
  have hqeq : q = p + δ := by dsimp [δ]; omega
  have hstrong : 32 * ((D + 1) * δ) < p := by
    simpa only [δ, Nat.mul_assoc] using hgap
  have hbasic : 32 * δ < p := by
    nlinarith [Nat.zero_le (D * δ)]
  let m := 4 * q / 7
  have hb : 7 * m ≤ 4 * q ∧ 4 * q < 7 * m + 7 := by dsimp [m]; omega
  have hm : 2 ≤ m := by omega
  have hmp : m < p := by omega
  have hcpos : 2 * q + 1 ≤ 4 * m := by omega
  let c := 4 * m - (2 * q + 1)
  have hceq : c + 2 * q + 1 = 4 * m := by dsimp [c]; omega
  refine ⟨m, p, q, c, 2 * δ, hm, hp, hq, hmp, hpq, by omega,
    hceq, by omega, by omega, ?_⟩
  nlinarith

theorem unbounded_collision_component (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ S : Finset ℕ, 0 ∈ S → CollisionClosed m S → D < S.card := by
  obtain ⟨m, p, q, c, h, hm, hp, hq, hmp, hpq, hh, hcq, hcp, hcm, hsize⟩ :=
    exists_collision_parameters D
  refine ⟨m, hm, ?_⟩
  intro S hzero hclosed
  have hleft : ∀ n ∈ S, n ≤ c → c - n ∈ S := by
    intro n hn hnc
    apply hclosed q hq (hmp.trans hpq) n hn (by omega) (c - n) (by omega)
    apply coalDiag_reflection_dvd
    omega
  have hright : ∀ n ∈ S, n ≤ c + h → c + h - n ∈ S := by
    intro n hn hnc
    apply hclosed p hp hmp n hn (by omega) (c + h - n) (by omega)
    apply coalDiag_reflection_dvd
    omega
  have hcard := reflection_orbit_card hh hzero hleft hright hsize
  omega

end Rhone.Algebra.DiagonalObstruction
