/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Semigroup
public import Rhone.Coalescent.KingmanChain

/-!
# Law of the number of ancestral lineages in Kingman's coalescent

Source: kingman1982, eq. (1.7)–(1.9). -/

@[expose] public section

namespace Rhone.MarkovChain.RateChain

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

theorem eq_sum_semigroup_of_forward (f : ℝ → S → ℝ)
    (hf : ∀ t y, HasDerivAt (fun s => f s y) (∑ x, f t x * R.Q x y) t) (t : ℝ) (y : S) :
    f t y = ∑ x, f 0 x * R.semigroup t x y := by
  have hd : ∀ s, HasDerivAt (fun s => ∑ x, f s x * R.semigroup (t - s) x y) 0 s := by
    intro s
    have hP : ∀ x, HasDerivAt (fun s => R.semigroup (t - s) x y)
        (-(R.Q * R.semigroup (t - s)) x y) s := by
      intro x
      have h := (R.hasDerivAt_semigroup' (t - s) x y).comp s ((hasDerivAt_id s).const_sub t)
      simpa [Function.comp_def] using h
    have h := HasDerivAt.fun_sum (u := univ) fun x _ => (hf s x).mul (hP x)
    have h1 : ∑ x, (∑ z, f s z * R.Q z x) * R.semigroup (t - s) x y =
        ∑ x, f s x * (R.Q * R.semigroup (t - s)) x y := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => by ring
    have h0 : ∑ x, ((∑ z, f s z * R.Q z x) * R.semigroup (t - s) x y +
        f s x * -(R.Q * R.semigroup (t - s)) x y) = 0 := by
      simp only [mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, h1, add_neg_cancel]
    rwa [h0] at h
  have hconst : ∑ x, f t x * R.semigroup (t - t) x y = ∑ x, f 0 x * R.semigroup (t - 0) x y :=
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  rw [sub_self, sub_zero, semigroup_zero] at hconst
  rw [← hconst]
  simp [Matrix.one_apply]

end Rhone.MarkovChain.RateChain

namespace Rhone.Coalescent

open Finset MarkovChain

theorem eq_mul_exp_of_hasDerivAt {u : ℝ → ℝ} {c : ℝ}
    (hu : ∀ s, HasDerivAt u (-(c * u s)) s) (t : ℝ) : u t = u 0 * Real.exp (-(c * t)) := by
  have hd : ∀ s, HasDerivAt (fun s => u s * Real.exp (c * s)) 0 s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).exp
    have h := (hu s).mul he
    have h0 : -(c * u s) * Real.exp (c * s) + u s * (Real.exp (c * s) * c) = 0 := by ring
    rwa [h0] at h
  have hconst : u t * Real.exp (c * t) = u 0 * Real.exp (c * 0) :=
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  rw [mul_zero, Real.exp_zero, mul_one] at hconst
  rw [Real.exp_neg, ← hconst, mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]

/-- Source: kingman1982, eq. (1.7)–(1.9). -/
theorem blockQ_mul_apply (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) :
    (blockQ n * M) i j = (coalRate i : ℝ) *
      ((if h : 1 ≤ (i : ℕ) then M ⟨(i : ℕ) - 1, by omega⟩ j else 0) - M i j) := by
  by_cases h : 1 ≤ (i : ℕ)
  · rw [Matrix.mul_apply, sum_blockQ_mul n i h (fun x => M x j), dite_eq_left h]
  · have h0 : coalRate (i : ℕ) = 0 := coalRate_eq_zero (by omega)
    simp [Matrix.mul_apply, blockQ, h0]

/-- Source: kingman1982, eq. (1.7)–(1.9). -/
theorem blockChain_semigroup_eq_zero_of_lt (n : ℕ) (t : ℝ) (i j : Fin (n + 1))
    (hij : i < j) : (blockChain n).semigroup t i j = 0 := by
  suffices H : ∀ m : ℕ, ∀ i : Fin (n + 1), (i : ℕ) = m → ∀ j, i < j → ∀ t,
      (blockChain n).semigroup t i j = 0 from H i i rfl j hij t
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi j hij t
    have hlt : (i : ℕ) < (j : ℕ) := Fin.lt_def.1 hij
    have hu : ∀ s, HasDerivAt (fun s => (blockChain n).semigroup s i j)
        (-((coalRate i : ℝ) * (blockChain n).semigroup s i j)) s := by
      intro s
      have h := (blockChain n).hasDerivAt_semigroup' s i j
      rw [blockChain_Q, blockQ_mul_apply] at h
      by_cases h1 : 1 ≤ (i : ℕ)
      · rw [dite_eq_left h1, ih ((i : ℕ) - 1) (by omega) ⟨(i : ℕ) - 1, by omega⟩ rfl j
          (Fin.lt_def.2 (by simp only; omega)) s, zero_sub, mul_neg] at h
        exact h
      · have h0 : (coalRate (i : ℕ) : ℝ) = 0 := by
          rw [coalRate_eq_zero (by omega), Rat.cast_zero]
        rw [h0, zero_mul] at h
        rw [h0, zero_mul, neg_zero]
        exact h
    rw [eq_mul_exp_of_hasDerivAt hu t, RateChain.semigroup_zero, Matrix.one_apply_ne hij.ne,
      zero_mul]

/-- Source: kingman1982, eq. (1.7)–(1.9). -/
theorem blockChain_semigroup_last_last (n : ℕ) (t : ℝ) :
    (blockChain n).semigroup t (Fin.last n) (Fin.last n) =
      Real.exp (-((coalRate n : ℝ) * t)) := by
  have hu : ∀ s, HasDerivAt (fun s => (blockChain n).semigroup s (Fin.last n) (Fin.last n))
      (-((coalRate ((Fin.last n : Fin (n + 1)) : ℕ) : ℝ) *
        (blockChain n).semigroup s (Fin.last n) (Fin.last n))) s := by
    intro s
    have h := (blockChain n).hasDerivAt_semigroup' s (Fin.last n) (Fin.last n)
    rw [blockChain_Q, blockQ_mul_apply] at h
    by_cases h1 : 1 ≤ ((Fin.last n : Fin (n + 1)) : ℕ)
    · rw [dite_eq_left h1, blockChain_semigroup_eq_zero_of_lt n s _ _
        (Fin.lt_def.2 (by simp only [Fin.val_last] at h1 ⊢; omega)), zero_sub, mul_neg] at h
      exact h
    · have h0 : (coalRate ((Fin.last n : Fin (n + 1)) : ℕ) : ℝ) = 0 := by
        rw [coalRate_eq_zero (by omega), Rat.cast_zero]
      rw [h0, zero_mul] at h
      rw [h0, zero_mul, neg_zero]
      exact h
  rw [eq_mul_exp_of_hasDerivAt hu t, RateChain.semigroup_zero, Matrix.one_apply_eq, one_mul,
    Fin.val_last]

noncomputable def lineageCoeff (n j k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - j) * (2 * (k : ℝ) - 1) *
    ((j + k - 2).factorial : ℝ) * (n.factorial : ℝ) * ((n - 1).factorial : ℝ) /
    (((j - 1).factorial : ℝ) * (j.factorial : ℝ) * ((k - j).factorial : ℝ) *
      ((n - k).factorial : ℝ) * ((n + k - 1).factorial : ℝ))

theorem lineageCoeff_add (i d e : ℕ) :
    lineageCoeff (i + 1 + d + e) (i + 1) (i + 1 + d) =
      (-1 : ℝ) ^ d * (2 * (i : ℝ) + 2 * d + 1) * ((2 * i + d).factorial : ℝ) *
        ((i + 1 + d + e).factorial : ℝ) * ((i + d + e).factorial : ℝ) /
        ((i.factorial : ℝ) * ((i + 1).factorial : ℝ) * (d.factorial : ℝ) * (e.factorial : ℝ) *
          ((2 * i + 2 * d + e + 1).factorial : ℝ)) := by
  unfold lineageCoeff
  rw [show i + 1 + d - (i + 1) = d from by omega,
    show i + 1 + (i + 1 + d) - 2 = 2 * i + d from by omega,
    show i + 1 + d + e - 1 = i + d + e from by omega,
    show i + 1 - 1 = i from by omega,
    show i + 1 + d + e - (i + 1 + d) = e from by omega,
    show i + 1 + d + e + (i + 1 + d) - 1 = 2 * i + 2 * d + e + 1 from by omega]
  push_cast
  ring

theorem sum_lineageCoeff_partial (i d e : ℕ) :
    ((d : ℝ) + e) * ∑ k ∈ Icc (i + 1) (i + 1 + d), lineageCoeff (i + 1 + d + e) (i + 1) k =
      (-1 : ℝ) ^ d * ((2 * i + d + 1).factorial : ℝ) * ((i + 1 + d + e).factorial : ℝ) *
        ((i + d + e).factorial : ℝ) * e /
        ((i.factorial : ℝ) * ((i + 1).factorial : ℝ) * (d.factorial : ℝ) * (e.factorial : ℝ) *
          ((2 * i + 2 * d + e + 1).factorial : ℝ)) := by
  induction d generalizing e with
  | zero =>
    have h := lineageCoeff_add i 0 e
    simp only [add_zero, mul_zero, pow_zero, one_mul, Nat.cast_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one] at h ⊢
    rw [Finset.Icc_self, Finset.sum_singleton, h, Nat.factorial_succ (2 * i)]
    push_cast
    ring
  | succ d ih =>
    have hn : i + 1 + d + (e + 1) = i + 1 + (d + 1) + e := by omega
    have hT := lineageCoeff_add i (d + 1) e
    have hI := ih (e + 1)
    rw [hn, show i + d + (e + 1) = i + (d + 1) + e from by omega,
      show 2 * i + 2 * d + (e + 1) + 1 = 2 * i + 2 * d + e + 2 from by omega] at hI
    rw [show 2 * i + 2 * (d + 1) + e + 1 = 2 * i + 2 * d + e + 2 + 1 from by omega,
      Nat.factorial_succ (2 * i + 2 * d + e + 2)] at hT ⊢
    have hsplit : ∑ k ∈ Icc (i + 1) (i + 1 + (d + 1)),
        lineageCoeff (i + 1 + (d + 1) + e) (i + 1) k =
        ∑ k ∈ Icc (i + 1) (i + 1 + d), lineageCoeff (i + 1 + (d + 1) + e) (i + 1) k +
          lineageCoeff (i + 1 + (d + 1) + e) (i + 1) (i + 1 + (d + 1)) :=
      Finset.sum_Icc_succ_top (b := i + 1 + d) (by omega) _
    have hcoef : (((d + 1 : ℕ) : ℝ) + e) = (d : ℝ) + ((e + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hsplit, mul_add, hcoef, hI, hT, show 2 * i + (d + 1) + 1 = 2 * i + d + 1 + 1 from rfl,
      show 2 * i + (d + 1) = 2 * i + d + 1 from rfl, Nat.factorial_succ (2 * i + d + 1),
      Nat.factorial_succ e, Nat.factorial_succ d]
    push_cast
    field_simp
    ring

theorem sum_lineageCoeff (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ∑ k ∈ Icc j n, lineageCoeff n j k = if j = n then 1 else 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  have h := sum_lineageCoeff_partial i d 0
  simp only [add_zero, Nat.cast_zero, mul_zero, zero_div] at h
  rcases d with _ | d
  · have hc := lineageCoeff_add i 0 0
    simp only [add_zero, mul_zero, pow_zero, one_mul, Nat.cast_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, ↓reduceIte] at hc ⊢
    rw [Finset.Icc_self, Finset.sum_singleton, hc, Nat.factorial_succ (2 * i)]
    push_cast
    field_simp
  · rw [ite_eq_right (by omega)]
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (by positivity)
    · exact h'

theorem lineageCoeff_succ_left (n j k : ℕ) (hj : 1 ≤ j) (hjk : j < k) (hkn : k ≤ n) :
    ((coalRate j : ℝ) - (coalRate k : ℝ)) * lineageCoeff n j k =
      (coalRate (j + 1) : ℝ) * lineageCoeff n (j + 1) k := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = i + 1 + (d + 1) := ⟨k - (i + 1) - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + (d + 1) + e := ⟨n - (i + 1 + (d + 1)), by omega⟩
  have h1 := lineageCoeff_add i (d + 1) e
  have h2 := lineageCoeff_add (i + 1) d e
  rw [show i + 1 + 1 + d + e = i + 1 + (d + 1) + e from by omega,
    show i + 1 + 1 + d = i + 1 + (d + 1) from by omega,
    show i + 1 + d + e = i + (d + 1) + e from by omega,
    show 2 * (i + 1) + 2 * d + e + 1 = 2 * i + 2 * (d + 1) + e + 1 from by omega,
    show 2 * (i + 1) + d = 2 * i + (d + 1) + 1 from by omega,
    Nat.factorial_succ (2 * i + (d + 1)), Nat.factorial_succ (i + 1)] at h2
  rw [h1, h2, Nat.factorial_succ d, Nat.factorial_succ i]
  unfold coalRate
  push_cast
  field_simp
  ring

noncomputable def lineageLaw (n : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  if 1 ≤ j then ∑ k ∈ Icc j n, Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k else 0

theorem hasDerivAt_lineageLaw (n j : ℕ) (hjn : j ≤ n) (t : ℝ) :
    HasDerivAt (fun s => lineageLaw n s j)
      (lineageLaw n t (j + 1) * (coalRate (j + 1) : ℝ) - lineageLaw n t j * (coalRate j : ℝ))
      t := by
  by_cases hj : 1 ≤ j
  · unfold lineageLaw
    simp only [ite_eq_left hj, ite_eq_left (Nat.le_add_left 1 j)]
    have hterm : ∀ k : ℕ, HasDerivAt
        (fun s => Real.exp (-((coalRate k : ℝ) * s)) * lineageCoeff n j k)
        (-(coalRate k : ℝ) * Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k) t := by
      intro k
      have h := (((hasDerivAt_id t).const_mul (-(coalRate k : ℝ))).exp).mul_const
        (lineageCoeff n j k)
      simp only [id_eq, mul_one, neg_mul] at h
      convert h using 1
      ring
    have h := HasDerivAt.fun_sum (u := Icc j n) fun k _ => hterm k
    convert h using 1
    have key : (∑ k ∈ Ioc j n, Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n (j + 1) k) *
        (coalRate (j + 1) : ℝ) = ∑ k ∈ Ioc j n, ((coalRate j : ℝ) - (coalRate k : ℝ)) *
          (Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_Ioc] at hk
      have hr := lineageCoeff_succ_left n j k hj hk.1 hk.2
      linear_combination (-Real.exp (-((coalRate k : ℝ) * t))) * hr
    rw [Finset.Icc_add_one_left_eq_Ioc, key,
      ← Finset.sum_Ioc_add_eq_sum_Icc (f := fun k =>
        Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k) hjn,
      ← Finset.sum_Ioc_add_eq_sum_Icc (f := fun k =>
        -(coalRate k : ℝ) * Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k) hjn]
    have hs : ∑ k ∈ Ioc j n, ((coalRate j : ℝ) - (coalRate k : ℝ)) *
        (Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k) =
        (coalRate j : ℝ) * ∑ k ∈ Ioc j n,
          Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k +
        ∑ k ∈ Ioc j n,
          -(coalRate k : ℝ) * Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hs]
    ring
  · obtain rfl : j = 0 := by omega
    have h0 : (coalRate (0 + 1) : ℝ) = 0 := by
      rw [coalRate_eq_zero (by omega), Rat.cast_zero]
    have hf : ∀ s, lineageLaw n s 0 = 0 := fun s => ite_eq_right (by omega)
    simp only [hf, h0, mul_zero, zero_mul, sub_zero]
    exact hasDerivAt_const t (0 : ℝ)

/-- Source: kingman1982, eq. (1.7)–(1.9). -/
theorem sum_mul_blockQ (n : ℕ) (u : ℕ → ℝ) (y : Fin (n + 1)) :
    ∑ x : Fin (n + 1), u x * blockQ n x y =
      (if (y : ℕ) + 1 ≤ n then u ((y : ℕ) + 1) * (coalRate ((y : ℕ) + 1) : ℝ) else 0) -
        u y * (coalRate y : ℝ) := by
  have hterm : ∀ x : Fin (n + 1), u x * blockQ n x y =
      (if (y : ℕ) + 1 = (x : ℕ) then u x * (coalRate x : ℝ) else 0) -
        (if y = x then u x * (coalRate x : ℝ) else 0) := by
    intro x
    unfold blockQ
    split_ifs <;> ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Fin.sum_univ_eq_sum_range
      (fun x : ℕ => if (y : ℕ) + 1 = x then u x * (coalRate x : ℝ) else 0) (n + 1),
      Finset.sum_ite_eq (range (n + 1)) ((y : ℕ) + 1)]
    simp only [mem_range, Nat.lt_succ_iff]
  · simp

theorem blockChain_semigroup_last_eq_lineageLaw (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (j : Fin (n + 1)) :
    (blockChain n).semigroup t (Fin.last n) j = lineageLaw n t j := by
  have hf : ∀ t (y : Fin (n + 1)), HasDerivAt (fun s => lineageLaw n s (y : ℕ))
      (∑ x : Fin (n + 1), lineageLaw n t x * (blockChain n).Q x y) t := by
    intro t y
    rw [blockChain_Q, sum_mul_blockQ n (lineageLaw n t) y]
    have h := hasDerivAt_lineageLaw n y (by omega) t
    by_cases hy : (y : ℕ) + 1 ≤ n
    · rw [ite_eq_left hy]
      exact h
    · have hz : lineageLaw n t ((y : ℕ) + 1) = 0 := by
        unfold lineageLaw
        rw [ite_eq_left (by omega), Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [hz, zero_mul] at h
      rw [ite_eq_right hy]
      exact h
  have h0 : ∀ x : Fin (n + 1), lineageLaw n 0 x = if x = Fin.last n then 1 else 0 := by
    intro x
    unfold lineageLaw
    by_cases hx : 1 ≤ (x : ℕ)
    · rw [ite_eq_left hx]
      simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
      rw [sum_lineageCoeff n x hx (by omega)]
      simp only [Fin.ext_iff, Fin.val_last]
    · rw [ite_eq_right hx, ite_eq_right]
      intro hxl
      rw [hxl, Fin.val_last] at hx
      exact hx hn
  have h := (blockChain n).eq_sum_semigroup_of_forward (fun s y => lineageLaw n s y) hf t j
  rw [h]
  simp [h0]

set_option linter.unusedVariables false in
theorem blockChain_semigroup_last (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (j : Fin (n + 1))
    (hj : 1 ≤ (j : ℕ)) :
    (blockChain n).semigroup t (Fin.last n) j =
      ∑ k ∈ Icc (j : ℕ) n, Real.exp (-((coalRate k : ℝ) * t)) * lineageCoeff n j k := by
  rw [blockChain_semigroup_last_eq_lineageLaw n (by omega) t j, lineageLaw, ite_eq_left hj]

end Rhone.Coalescent
