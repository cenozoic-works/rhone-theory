/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Moran
public import Rhone.MarkovChain.CoreBridge
public import Mathlib.Tactic.FieldSimp

/-!
# Moran mutation stationary count law

Source: ewens2004, sec. 3.4. -/

@[expose] public section
namespace Rhone.MarkovChain
open scoped BigOperators

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationUp (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ((1 - u) * (i : ℝ) + u * ((N : ℝ) - i)) * ((N : ℝ) - i) / (N : ℝ) ^ 2

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationDown (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ((1 - u) * ((N : ℝ) - i) + u * (i : ℝ)) * (i : ℝ) / (N : ℝ) ^ 2

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationRow (N : ℕ) (u : ℝ) (i j : Fin (N + 1)) : ℝ :=
  (if j = i then 1 - moranMutationUp N u i - moranMutationDown N u i else 0) +
  (if j.val = i.val + 1 then moranMutationUp N u i else 0) +
  (if i.val = j.val + 1 then moranMutationDown N u i else 0)

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationWeight (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ∏ k ∈ Finset.range i, moranMutationUp N u k / moranMutationDown N u (k + 1)

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationLaw (N : ℕ) (u : ℝ) (i : Fin (N + 1)) : ℝ :=
  moranMutationWeight N u i / (∑ j : Fin (N + 1), moranMutationWeight N u j)

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_rates_pos {N i : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (hi : i < N) :
    0 < moranMutationUp N u i ∧ 0 < moranMutationDown N u (i + 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (i : ℝ) < N := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hi1 : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  have hu : 0 < 1 - u := by linarith
  have ha : 0 < (1 - u) * (i : ℝ) + u * ((N : ℝ) - i) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hu.le hi0) (mul_pos hu0 (sub_pos.mpr hn'))
  have hb : 0 < (1 - u) * ((N : ℝ) - ((i : ℝ) + 1)) + u * ((i : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hu.le (sub_nonneg.mpr hi1))
      (mul_pos hu0 (by positivity))
  constructor
  · exact div_pos (mul_pos ha (sub_pos.mpr hn')) (sq_pos_of_pos hn)
  · unfold moranMutationDown
    push_cast
    exact div_pos (mul_pos hb (by positivity)) (sq_pos_of_pos hn)

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_weight_pos {N i : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (hi : i ≤ N) :
    0 < moranMutationWeight N u i := by
  unfold moranMutationWeight
  apply Finset.prod_pos
  intro k hk
  have hk' : k < N := lt_of_lt_of_le (Finset.mem_range.mp hk) hi
  exact div_pos (moran_mutation_rates_pos hN hu0 hu1 hk').1
    (moran_mutation_rates_pos hN hu0 hu1 hk').2

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_probability {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i, 0 ≤ moranMutationLaw N u i) ∧ ∑ i, moranMutationLaw N u i = 1 := by
  have hw (i : Fin (N + 1)) : 0 < moranMutationWeight N u i :=
    moran_mutation_weight_pos hN hu0 hu1 (Nat.le_of_lt_succ i.isLt)
  have hz : 0 < ∑ j : Fin (N + 1), moranMutationWeight N u j :=
    Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  constructor
  · intro i; exact (div_pos (hw i) hz).le
  · unfold moranMutationLaw
    rw [← Finset.sum_div, div_self hz.ne']

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_markov {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i j, 0 ≤ moranMutationRow N u i j) ∧
    (∀ i, ∑ j, moranMutationRow N u i j = 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hzero : moranMutationDown N u 0 = 0 := by simp [moranMutationDown]
  have htop : moranMutationUp N u N = 0 := by simp [moranMutationUp]
  have hbounds (i : Fin (N + 1)) : 0 ≤ moranMutationUp N u i ∧
      0 ≤ moranMutationDown N u i ∧ moranMutationUp N u i + moranMutationDown N u i ≤ 1 := by
    have hi : (i : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have hu : 0 ≤ 1 - u := by linarith
    have hc : 0 ≤ (N : ℝ) - i := sub_nonneg.mpr hi
    have ha0 : 0 ≤ (1 - u) * (i : ℝ) + u * ((N : ℝ) - i) := by positivity
    have hb0 : 0 ≤ (1 - u) * ((N : ℝ) - i) + u * (i : ℝ) := by positivity
    have ha1 : (1 - u) * (i : ℝ) + u * ((N : ℝ) - i) ≤ N := by
      nlinarith [mul_nonneg hu hc, mul_nonneg hu0.le hi0]
    have hb1 : (1 - u) * ((N : ℝ) - i) + u * (i : ℝ) ≤ N := by
      nlinarith [mul_nonneg hu hi0, mul_nonneg hu0.le hc]
    refine ⟨div_nonneg (mul_nonneg ha0 hc) (sq_nonneg _),
      div_nonneg (mul_nonneg hb0 hi0) (sq_nonneg _), ?_⟩
    unfold moranMutationUp moranMutationDown
    rw [← add_div, div_le_one (sq_pos_of_pos hn)]
    nlinarith [mul_le_mul_of_nonneg_right ha1 hc, mul_le_mul_of_nonneg_right hb1 hi0]
  constructor
  · intro i j
    obtain ⟨ha,hb,hc⟩ := hbounds i
    unfold moranMutationRow
    split_ifs <;> linarith
  · intro i
    have hup : (∑ j : Fin (N + 1),
        if j.val = i.val + 1 then moranMutationUp N u i else 0) = moranMutationUp N u i := by
      by_cases hi : i.val < N
      · let k : Fin (N + 1) := ⟨i.val + 1, by omega⟩
        rw [Finset.sum_eq_single k]
        · simp [k]
        · intro b _ hb
          have hne : b.val ≠ i.val + 1 := by
            intro he; apply hb; exact Fin.ext he
          simp [hne]
        · simp
      · have he : i.val = N := by omega
        simp [he,htop]
    have hdown : (∑ j : Fin (N + 1),
        if i.val = j.val + 1 then moranMutationDown N u i else 0) = moranMutationDown N u i := by
      by_cases hi : i.val = 0
      · simp [hi,hzero]
      · let k : Fin (N + 1) := ⟨i.val - 1, by omega⟩
        rw [Finset.sum_eq_single k]
        · have hk : i.val = k.val + 1 := by dsimp [k]; omega
          simp [hk]
        · intro b _ hb
          have hne : i.val ≠ b.val + 1 := by
            intro he; apply hb; apply Fin.ext; dsimp [k]; omega
          simp [hne]
        · simp
    simp only [moranMutationRow,Finset.sum_add_distrib]
    rw [hup,hdown]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_reversible {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (i j : Fin (N + 1)) :
    moranMutationLaw N u i * moranMutationRow N u i j =
      moranMutationLaw N u j * moranMutationRow N u j i := by
  have hrec (k : ℕ) (hk : k < N) :
      moranMutationWeight N u (k + 1) * moranMutationDown N u (k + 1) =
        moranMutationWeight N u k * moranMutationUp N u k := by
    have hd := (moran_mutation_rates_pos hN hu0 hu1 hk).2.ne'
    unfold moranMutationWeight
    rw [Finset.prod_range_succ]
    field_simp [hd]
  have hnat (k : ℕ) : k ≠ k + 1 + 1 := by omega
  by_cases he : i = j
  · subst j; rfl
  have he' : j ≠ i := Ne.symm he
  by_cases hj : j.val = i.val + 1
  · have hi : i.val < N := by omega
    simp only [moranMutationRow, he, he', ite_false, hj, ite_true, zero_add]
    unfold moranMutationLaw
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    congr 1
    rw [hj]
    simp only [hnat, ite_false, add_zero, zero_add]
    exact (hrec i hi).symm
  · by_cases hi : i.val = j.val + 1
    · have hj' : j.val < N := by omega
      simp only [moranMutationRow, he, he', ite_false, hi, ite_true, zero_add]
      unfold moranMutationLaw
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      congr 1
      rw [hi]
      simp only [hnat, ite_false, add_zero, zero_add]
      exact hrec j hj'
    · simp [moranMutationRow, he, he', hj, hi]

/-- Source: ewens2004, sec. 3.4. -/
theorem moran_mutation_stationary {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (j : Fin (N + 1)) :
    ∑ i, moranMutationLaw N u i * moranMutationRow N u i j = moranMutationLaw N u j := by
  simp_rw [moran_mutation_reversible hN hu0 hu1]
  rw [← Finset.mul_sum,(moran_mutation_markov hN hu0 hu1).2 j,mul_one]

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranMutationChain (N : ℕ) (u : ℝ) (hN : 0 < N)
    (hu0 : 0 < u) (hu1 : u < 1) : Rhone.MarkovChain.FinChain (Fin (N + 1)) :=
  Rhone.MarkovChain.CountKernel.toFinChain (moranMutationRow N u)
    (moran_mutation_markov hN hu0 hu1)

end Rhone.MarkovChain
