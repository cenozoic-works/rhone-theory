/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranMutationStationary
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Moran mutation–drift balance: stationary mean and heterozygosity

Source: ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

/-- Source: ewens2004, sec. 3.4. -/
theorem moranMutationRow_expect (N : ℕ) (u : ℝ) (f : ℕ → ℝ) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1), moranMutationRow N u i j * f j =
      f i + moranMutationUp N u i * (f (i + 1) - f i) +
        moranMutationDown N u i * (f (i - 1) - f i) := by
  have hzero : moranMutationDown N u 0 = 0 := by simp [moranMutationDown]
  have htop : moranMutationUp N u N = 0 := by simp [moranMutationUp]
  have hup : (∑ j : Fin (N + 1),
      if j.val = i.val + 1 then moranMutationUp N u i * f j else 0) =
        moranMutationUp N u i * f (i + 1) := by
    by_cases hi : i.val < N
    · let k : Fin (N + 1) := ⟨i.val + 1, by omega⟩
      rw [sum_eq_single k]
      · simp [k]
      · intro b _ hb
        have hne : b.val ≠ i.val + 1 := by
          intro he; apply hb; exact Fin.ext he
        simp [hne]
      · simp
    · have he : i.val = N := by omega
      simp [he, htop]
  have hdown : (∑ j : Fin (N + 1),
      if i.val = j.val + 1 then moranMutationDown N u i * f j else 0) =
        moranMutationDown N u i * f (i - 1) := by
    by_cases hi : i.val = 0
    · simp [hi, hzero]
    · let k : Fin (N + 1) := ⟨i.val - 1, by omega⟩
      rw [sum_eq_single k]
      · have hk : i.val = k.val + 1 := by dsimp [k]; omega
        simp [hk]
      · intro b _ hb
        have hne : i.val ≠ b.val + 1 := by
          intro he; apply hb; apply Fin.ext; dsimp [k]; omega
        simp [hne]
      · simp
  simp only [moranMutationRow, add_mul, ite_mul, zero_mul, sum_add_distrib]
  rw [hup, hdown]
  simp only [sum_ite_eq', mem_univ, ite_true]
  ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_stationary_drift {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (f : ℕ → ℝ) :
    ∑ i : Fin (N + 1), moranMutationLaw N u i *
      (moranMutationUp N u i * (f (i + 1) - f i) +
        moranMutationDown N u i * (f (i - 1) - f i)) = 0 := by
  have h1 : ∑ j : Fin (N + 1), moranMutationLaw N u j * f j =
      ∑ i : Fin (N + 1), moranMutationLaw N u i *
        (∑ j : Fin (N + 1), moranMutationRow N u i j * f j) := by
    calc ∑ j : Fin (N + 1), moranMutationLaw N u j * f j
        = ∑ j : Fin (N + 1),
            (∑ i : Fin (N + 1), moranMutationLaw N u i * moranMutationRow N u i j) * f j := by
          simp only [moran_mutation_stationary hN hu0 hu1]
      _ = ∑ j : Fin (N + 1), ∑ i : Fin (N + 1),
            moranMutationLaw N u i * (moranMutationRow N u i j * f j) := by
          simp only [sum_mul, mul_assoc]
      _ = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
            moranMutationLaw N u i * (moranMutationRow N u i j * f j) := sum_comm
      _ = _ := by simp only [mul_sum]
  have h3 : ∀ i : Fin (N + 1), moranMutationLaw N u i *
      (f i + moranMutationUp N u i * (f (i + 1) - f i) +
        moranMutationDown N u i * (f (i - 1) - f i)) =
      moranMutationLaw N u i * f i + moranMutationLaw N u i *
        (moranMutationUp N u i * (f (i + 1) - f i) +
          moranMutationDown N u i * (f (i - 1) - f i)) := fun i => by ring
  simp only [moranMutationRow_expect, h3, sum_add_distrib] at h1
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moranMutation_count_drift {N : ℕ} (hN : 0 < N) (u : ℝ) (i : ℕ) :
    moranMutationUp N u i * (((i + 1 : ℕ) : ℝ) - i) +
      moranMutationDown N u i * (((i - 1 : ℕ) : ℝ) - i) =
        u * ((N : ℝ) - 2 * i) / N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rcases i with _ | k
  · simp only [moranMutationUp, moranMutationDown, zero_add, Nat.zero_sub, Nat.cast_zero,
      Nat.cast_one]
    field_simp
    ring
  · simp only [moranMutationUp, moranMutationDown, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    field_simp
    ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moranMutation_product_drift {N : ℕ} (hN : 0 < N) (u : ℝ) (i : ℕ) :
    moranMutationUp N u i *
        (((i + 1 : ℕ) : ℝ) * ((N : ℝ) - ((i + 1 : ℕ) : ℝ)) - (i : ℝ) * ((N : ℝ) - i)) +
      moranMutationDown N u i *
        (((i - 1 : ℕ) : ℝ) * ((N : ℝ) - ((i - 1 : ℕ) : ℝ)) - (i : ℝ) * ((N : ℝ) - i)) =
      u * ((N : ℝ) - 1) -
        (i : ℝ) * ((N : ℝ) - i) * (4 * u * ((N : ℝ) - 1) + 2) / (N : ℝ) ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rcases i with _ | k
  · simp only [moranMutationUp, moranMutationDown, zero_add, Nat.zero_sub, Nat.cast_zero,
      Nat.cast_one]
    field_simp
    ring
  · simp only [moranMutationUp, moranMutationDown, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    field_simp
    ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_stationary_mean {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    ∑ i : Fin (N + 1), moranMutationLaw N u i * (i : ℝ) = (N : ℝ) / 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hone := (moran_mutation_probability hN hu0 hu1).2
  have h := moran_mutation_stationary_drift hN hu0 hu1 (fun k : ℕ => (k : ℝ))
  simp only [moranMutation_count_drift hN] at h
  have hh : ∑ i : Fin (N + 1), moranMutationLaw N u i * (u * ((N : ℝ) - 2 * i) / N) =
      u / N * ((N : ℝ) * ∑ i : Fin (N + 1), moranMutationLaw N u i -
        2 * ∑ i : Fin (N + 1), moranMutationLaw N u i * (i : ℝ)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl (fun i _ => by ring)
  rw [hh, hone, mul_one] at h
  have hc : u / (N : ℝ) ≠ 0 := (div_pos hu0 hn).ne'
  have h2 := (mul_eq_zero.mp h).resolve_left hc
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_stationary_heterozygosity {N : ℕ} {u : ℝ}
    (hN : 2 ≤ N) (hu0 : 0 < u) (hu1 : u < 1) :
    ∑ i : Fin (N + 1), moranMutationLaw N u i *
        (2 * (i : ℝ) * ((N : ℝ) - i) / ((N : ℝ) * ((N : ℝ) - 1))) =
      (N : ℝ) * u / (1 + 2 * ((N : ℝ) - 1) * u) := by
  have hN0 : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hN0
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hpos : (0 : ℝ) < 1 + 2 * ((N : ℝ) - 1) * u := by positivity
  have hone := (moran_mutation_probability hN0 hu0 hu1).2
  have h := moran_mutation_stationary_drift hN0 hu0 hu1
    (fun k : ℕ => (k : ℝ) * ((N : ℝ) - k))
  simp only [moranMutation_product_drift hN0] at h
  have hh : ∑ i : Fin (N + 1), moranMutationLaw N u i *
      (u * ((N : ℝ) - 1) -
        (i : ℝ) * ((N : ℝ) - i) * (4 * u * ((N : ℝ) - 1) + 2) / (N : ℝ) ^ 2) =
      u * ((N : ℝ) - 1) * ∑ i : Fin (N + 1), moranMutationLaw N u i -
        (4 * u * ((N : ℝ) - 1) + 2) / (N : ℝ) ^ 2 *
          ∑ i : Fin (N + 1), moranMutationLaw N u i * ((i : ℝ) * ((N : ℝ) - i)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by ring)
  have hg : ∑ i : Fin (N + 1), moranMutationLaw N u i *
      (2 * (i : ℝ) * ((N : ℝ) - i) / ((N : ℝ) * ((N : ℝ) - 1))) =
      2 / ((N : ℝ) * ((N : ℝ) - 1)) *
        ∑ i : Fin (N + 1), moranMutationLaw N u i * ((i : ℝ) * ((N : ℝ) - i)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun i _ => by ring)
  rw [hh, hone, mul_one] at h
  have hS : ∑ i : Fin (N + 1), moranMutationLaw N u i * ((i : ℝ) * ((N : ℝ) - i)) =
      u * ((N : ℝ) - 1) * (N : ℝ) ^ 2 / (2 * (1 + 2 * ((N : ℝ) - 1) * u)) := by
    have h' : u * ((N : ℝ) - 1) = (4 * u * ((N : ℝ) - 1) + 2) *
        (∑ i : Fin (N + 1), moranMutationLaw N u i * ((i : ℝ) * ((N : ℝ) - i))) /
          (N : ℝ) ^ 2 := by
      rw [← div_mul_eq_mul_div]
      linarith
    rw [eq_div_iff (pow_ne_zero 2 hn.ne')] at h'
    rw [eq_div_iff (by positivity)]
    linarith
  rw [hg, hS]
  field_simp

end Rhone.MarkovChain
