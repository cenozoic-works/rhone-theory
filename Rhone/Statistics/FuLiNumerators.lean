/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsSegregatingIdentification
public import Rhone.Statistics.TajimaVariance

/-!
# Means and variances of the Fu and Li D and F numerators under the marked Kingman law

Source: fu1995, eq. (1)–(3), (10), (12), pp. 174–176; durrett2008, Thm 2.2; fu_li1993, p. 697,
p. 701. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter
open scoped NNReal

/-- Source: fu_li1993, p. 697. -/
noncomputable def fuLiDNumerator (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) : ℝ :=
  markedKingmanSegregating n x - (tajimaA1 n : ℝ) * markedKingmanSfs n 1 x

/-- Source: fu_li1993, p. 701. -/
noncomputable def fuLiFNumerator (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) : ℝ :=
  markedKingmanPi n x - markedKingmanSfs n 1 x

private theorem sum_Icc_two_half_diff (β : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Icc 2 (k + 1), (β (j + 1) - β j) / 2 = (β (k + 2) - β 2) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

private theorem sum_Icc_one_split (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Icc 1 (m + 1), f j = f 1 + ∑ j ∈ Icc 2 (m + 1), f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := m + 1) (by omega), ih,
      Finset.sum_Icc_succ_top (a := 2) (b := m + 1) (by omega)]
    ring

theorem fuSigma_one_one {n : ℕ} (hn : 3 ≤ n) :
    fuSigma n 1 1 = 2 * ((n : ℝ) * (tajimaA1 n : ℝ) - 2 * ((n : ℝ) - 1)) /
      (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [fuSigma_self]
  unfold fuSigmaDiag fuBeta tajimaA1
  rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  have e1 : m + 3 - 1 = m + 2 := by omega
  have hh1 : (harmonic 1 : ℚ) = 1 := by simp [harmonic]
  rw [e1, show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show m + 3 = (m + 2) + 1 from rfl, harmonic_succ, hh1]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : ((m : ℝ) + 2 + 1 - 2 + 1) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
  have h2 : ((m : ℝ) + 2 + 1 - 2) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
  have h5 : ((m : ℝ) + 2 + 1 - 1) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
  have h3 : ((m : ℝ) + 2 + 1) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
  field_simp
  ring

theorem sum_fuSigma_one {n : ℕ} (hn : 3 ≤ n) :
    ∑ j ∈ Icc 1 (n - 1), fuSigma n 1 j = (tajimaA1 n : ℝ) / ((n : ℝ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have hfirst : fuSigma (m + 3) 1 1 = fuBeta (m + 3) 2 := by
    rw [fuSigma_self]
    unfold fuSigmaDiag
    rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  have hmid : ∑ j ∈ Icc 2 (m + 1), fuSigma (m + 3) 1 j =
      ∑ j ∈ Icc 2 (m + 1), (fuBeta (m + 3) (j + 1) - fuBeta (m + 3) j) / 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h1 : ¬ (1 = j) := by omega
    have h2 : 1 + j < m + 3 := by omega
    unfold fuSigma
    rw [ite_eq_right h1, ite_eq_left_iff.mpr (fun h => absurd h2 h),
      max_eq_right (by omega : 1 ≤ j)]
  have hlast : fuSigma (m + 3) 1 (m + 2) =
      ((harmonic (m + 2) : ℚ) : ℝ) / ((m : ℝ) + 2) + 1 / ((m : ℝ) + 2) -
        (fuBeta (m + 3) (m + 2) + fuBeta (m + 3) 2) / 2 - 1 / ((m : ℝ) + 2) := by
    unfold fuSigma
    have h1 : ¬ (1 = m + 2) := by omega
    have h2 : ¬ (1 + (m + 2) < m + 3) := by omega
    have h3 : (1 + (m + 2) = m + 3) := by omega
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left_iff.mpr (fun h => absurd h3 h),
      max_eq_right (by omega : 1 ≤ m + 2), min_eq_left (by omega : 1 ≤ m + 2)]
    have e3 : m + 3 - 1 = m + 2 := by omega
    have hh : (harmonic (m + 2) : ℚ) = harmonic (m + 1) + ((m + 2 : ℕ) : ℚ)⁻¹ :=
      harmonic_succ (m + 1)
    rw [e3, show m + 2 - 1 = m + 1 by omega, show (1 : ℕ) - 1 = 0 from rfl, harmonic_zero, hh]
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h4 : ((m : ℝ) + 2) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
    have h5 : ((m : ℝ) + 3 - (m + 2)) = 1 := by ring
    have h6 : ((m : ℝ) + 3 - 1) = m + 2 := by ring
    rw [h5, h6]
    field_simp
    ring
  rw [e1, Finset.sum_Icc_succ_top (by omega), sum_Icc_one_split _ m, hfirst, hmid, hlast,
    sum_Icc_two_half_diff]
  unfold tajimaA1
  rw [e1]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h4 : ((m : ℝ) + 2) ≠ 0 := (by linarith : (0 : ℝ) < _).ne'
  have h6 : ((m : ℝ) + 3 - 1) = m + 2 := by ring
  push_cast
  rw [h6]
  field_simp
  ring

private theorem sum_sum_sub_delta {n : ℕ} (hn : 2 ≤ n) (p : ℕ → ℝ) (a : ℝ) :
    ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
        (p i - a * (if i = 1 then 1 else 0)) * (p j - a * (if j = 1 then 1 else 0)) *
          fuSigma n i j =
      ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1), p i * p j * fuSigma n i j -
        2 * a * ∑ j ∈ Icc 1 (n - 1), p j * fuSigma n 1 j + a ^ 2 * fuSigma n 1 1 := by
  have h1 : 1 ∈ Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hterm : ∀ i j : ℕ, (p i - a * (if i = 1 then 1 else 0)) *
        (p j - a * (if j = 1 then 1 else 0)) * fuSigma n i j =
      p i * p j * fuSigma n i j - a * (if j = 1 then p i * fuSigma n i j else 0) -
        a * (if i = 1 then p j * fuSigma n i j else 0) +
        a ^ 2 * (if i = 1 then (if j = 1 then fuSigma n i j else 0) else 0) := by
    intro i j
    by_cases hi : i = 1 <;> by_cases hj : j = 1 <;> simp [hi, hj] <;> ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hr1 : ∀ g : ℕ → ℕ → ℝ, ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
      (if i = 1 then g i j else 0) = ∑ j ∈ Icc 1 (n - 1), g 1 j := by
    intro g
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp
    · intro i _ hi
      simp [hi]
  have hr2 : ∀ g : ℕ → ℕ → ℝ, ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
      (if i = 1 then (if j = 1 then g i j else 0) else 0) = g 1 1 := by
    intro g
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp [h1]
    · intro i _ hi
      simp [hi]
  rw [hr1, hr2]
  simp only [Finset.sum_ite_eq', h1, ↓reduceIte]
  have hc : ∑ i ∈ Icc 1 (n - 1), p i * fuSigma n i 1 =
      ∑ j ∈ Icc 1 (n - 1), p j * fuSigma n 1 j :=
    Finset.sum_congr rfl fun i _ => by rw [fuSigma_comm]
  rw [hc]
  ring

private theorem sum_Icc_one_mul_sub_sq' (m : ℕ) (N : ℝ) :
    ∑ i ∈ Icc 1 m, (i : ℝ) * (N - (i : ℝ)) ^ 2 =
      N ^ 2 * (m : ℝ) * ((m : ℝ) + 1) / 2 -
        N * (m : ℝ) * ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) / 3 +
        (m : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 / 4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem tajimaA1_real (n : ℕ) :
    (tajimaA1 n : ℝ) = ∑ i ∈ Icc 1 (n - 1), 1 / (i : ℝ) := by
  unfold tajimaA1
  rw [harmonic_eq_sum_Icc_inv]
  push_cast
  simp

/-- Source: fu_li1993, p. 696, eq. (20), (22). -/
theorem markedKingman_fuLiDNumerator_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, fuLiDNumerator n x ∂markedKingmanLaw n θ = 0 := by
  unfold fuLiDNumerator
  rw [integral_sub (integrable_markedKingmanSegregating n θ)
    ((integrable_markedKingmanSfs n 1 θ).const_mul _), integral_const_mul,
    markedKingmanSegregating_mean hn, markedKingmanSfs_mean le_rfl (by omega)]
  simp only [Nat.cast_one, div_one]
  ring

/-- Source: fu_li1993, p. 697, eq. (31). -/
theorem markedKingman_fuLiDNumerator_variance {n : ℕ} (hn : 3 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (fuLiDNumerator n) (markedKingmanLaw n θ) =
      (tajimaA1 n : ℝ) * ((tajimaA1 n : ℝ) - 1) * (θ : ℝ) +
        ((tajimaA1 n : ℝ) ^ 2 + (tajimaA2 n : ℝ) +
          (tajimaA1 n : ℝ) ^ 2 * (2 * ((n : ℝ) * (tajimaA1 n : ℝ) - 2 * ((n : ℝ) - 1)) /
            (((n : ℝ) - 1) * ((n : ℝ) - 2)) - ((n : ℝ) + 1) / ((n : ℝ) - 1))) * (θ : ℝ) ^ 2 := by
  have h1 : 1 ∈ Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hae : fuLiDNumerator n =ᵐ[markedKingmanLaw n θ] fun x =>
      ∑ i ∈ Icc 1 (n - 1), (1 - (tajimaA1 n : ℝ) * (if i = 1 then 1 else 0)) *
        markedKingmanSfs n i x := by
    filter_upwards [markedKingmanSegregating_ae_eq_sum_sfs n θ] with x hx
    unfold fuLiDNumerator
    rw [hx]
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
    simp [h1]
  rw [variance_congr hae, markedKingman_linear_sfs_variance n
    (fun i : ℕ => 1 - (tajimaA1 n : ℝ) * (if i = 1 then 1 else 0)) θ]
  have hlin : ∑ i ∈ Icc 1 (n - 1),
      (1 - (tajimaA1 n : ℝ) * (if i = 1 then 1 else 0)) ^ 2 / (i : ℝ) =
        (tajimaA1 n : ℝ) * ((tajimaA1 n : ℝ) - 1) := by
    have hterm : ∀ i ∈ Icc 1 (n - 1),
        (1 - (tajimaA1 n : ℝ) * (if i = 1 then 1 else 0)) ^ 2 / (i : ℝ) =
          1 / (i : ℝ) - 2 * (tajimaA1 n : ℝ) * (if i = 1 then 1 else 0) +
            (tajimaA1 n : ℝ) ^ 2 * (if i = 1 then 1 else 0) := by
      intro i _
      by_cases hi : i = 1
      · subst hi
        simp
        ring
      · simp [hi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← tajimaA1_real, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', h1, ↓reduceIte]
    ring
  have hquad := sum_sum_sub_delta (n := n) (by omega) (fun _ => (1 : ℝ)) (tajimaA1 n : ℝ)
  simp only [one_mul, mul_one] at hquad
  rw [hlin, hquad, sum_sum_fuSigma (by omega), sum_fuSigma_one hn, fuSigma_one_one hn]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    intro h
    linarith
  field_simp
  ring

/-- Source: fu_li1993, p. 696, eq. (22), (26). -/
theorem markedKingman_fuLiFNumerator_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, fuLiFNumerator n x ∂markedKingmanLaw n θ = 0 := by
  unfold fuLiFNumerator
  rw [integral_sub (integrable_markedKingmanPi hn θ) (integrable_markedKingmanSfs n 1 θ),
    markedKingmanPi_mean hn, markedKingmanSfs_mean le_rfl (by omega)]
  simp

/-- Source: fu1995, eq. (1)–(3), (12), pp. 174–176; durrett2008, Thm 2.2; fu_li1993, p. 701. -/
theorem markedKingman_fuLiFNumerator_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (fuLiFNumerator n) (markedKingmanLaw n θ) =
      (((n : ℝ) + 1) / (3 * ((n : ℝ) - 1)) - 4 / (n : ℝ) + 1) * (θ : ℝ) +
        (θ : ℝ) ^ 2 * ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1),
          (2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1)) -
              (if i = 1 then 1 else 0)) *
            (2 * (j : ℝ) * ((n : ℝ) - j) / ((n : ℝ) * ((n : ℝ) - 1)) -
              (if j = 1 then 1 else 0)) * fuSigma n i j := by
  have h1 : 1 ∈ Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    intro h
    linarith
  have hfun : fuLiFNumerator n = fun x => ∑ i ∈ Icc 1 (n - 1),
      (2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1)) -
        (if i = 1 then 1 else 0)) * markedKingmanSfs n i x := by
    funext x
    unfold fuLiFNumerator
    rw [markedKingmanPi_eq_sum_sfs]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    simp [h1]
  rw [hfun, markedKingman_linear_sfs_variance n (fun i : ℕ =>
    2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1)) - (if i = 1 then 1 else 0)) θ]
  have hlin : ∑ i ∈ Icc 1 (n - 1),
      (2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1)) -
        (if i = 1 then 1 else 0)) ^ 2 / (i : ℝ) =
      ((n : ℝ) + 1) / (3 * ((n : ℝ) - 1)) - 4 / (n : ℝ) + 1 := by
    have hterm : ∀ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1)) -
          (if i = 1 then 1 else 0)) ^ 2 / (i : ℝ) =
        4 / ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 * ((i : ℝ) * ((n : ℝ) - i) ^ 2) +
          (1 - 4 / (n : ℝ)) * (if i = 1 then 1 else 0) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      by_cases h : i = 1
      · subst h
        simp
        field_simp
        ring
      · simp only [h, ↓reduceIte, sub_zero, mul_zero, add_zero]
        field_simp
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_Icc_one_mul_sub_sq', ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', h1, ↓reduceIte, mul_one, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_one]
    field_simp
    ring
  rw [hlin]
  ring

end Rhone.Statistics
