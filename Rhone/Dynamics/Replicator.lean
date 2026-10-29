/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MultiAlleleSelection
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
/-!
# Frequency-dependent replicator vector field

Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
@[expose] public section
namespace Rhone.Dynamics
open Finset
variable {I : Type*} [Fintype I]

/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
def simplex (x : I → ℝ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1
/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
noncomputable def payoff (A : I → I → ℝ) (x y : I → ℝ) : ℝ :=
  ∑ i, x i * marginalFit A y i
/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
noncomputable def replicator (A : I → I → ℝ) (x : I → ℝ) (i : I) : ℝ :=
  x i * (marginalFit A x i - payoff A x x)
/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
def mix (p q : I → ℝ) (e : ℝ) (i : I) : ℝ := (1-e)*p i+e*q i
/-- Source: hofbauer_sigmund2003, p. 486, eq. 15–18. -/
def IsESS (A : I → I → ℝ) (p : I → ℝ) : Prop :=
  simplex p ∧ ∀ q, simplex q → q ≠ p → ∃ e0 > 0,
    ∀ e, 0 < e → e < e0 → e < 1 →
      payoff A q (mix p q e) < payoff A p (mix p q e)

/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem replicator_sum_general (A : I → I → ℝ) (x : I → ℝ)
    (hx : simplex x) : ∑ i, replicator A x i = 0 := by
  simp only [replicator, mul_sub, sum_sub_distrib, ← sum_mul, hx.2, one_mul, payoff]
  exact sub_self _
/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem replicator_absent_general (A : I → I → ℝ) (x : I → ℝ) (i : I)
    (hi : x i = 0) : replicator A x i = 0 := by simp [replicator, hi]
/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem replicator_rest_iff_general (A : I → I → ℝ) (x : I → ℝ) :
    (∀ i, replicator A x i = 0) ↔
      ∀ i, x i ≠ 0 → marginalFit A x i = payoff A x x := by
  simp only [replicator, mul_eq_zero, sub_eq_zero]
  constructor
  · intro h i hi
    exact (h i).resolve_left hi
  · intro h i
    by_cases hi : x i = 0
    · exact Or.inl hi
    · exact Or.inr (h i hi)

private theorem payoff_mix (A : I → I → ℝ) (x p q : I → ℝ) (e : ℝ) :
    payoff A x (mix p q e) = (1-e)*payoff A x p+e*payoff A x q := by
  have hinner : ∀ i, marginalFit A (mix p q e) i =
      (1-e)*marginalFit A p i+e*marginalFit A q i := by
    intro i
    unfold marginalFit mix
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  unfold payoff
  simp only [hinner]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  ring

private theorem rare_linear_iff (d c : ℝ) :
    (∃ e0 > 0, ∀ e, 0 < e → e < e0 → e < 1 → 0 < (1-e)*d+e*c) ↔
      0 < d ∨ (d = 0 ∧ 0 < c) := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    have hd : 0 ≤ d := by
      by_contra hn
      have hdneg : d < 0 := lt_of_not_ge hn
      let e := min (δ/2) (min (1/2) ((-d)/(2*(|c-d|+1))))
      have he : 0 < e := by
        dsimp [e]
        exact lt_min (by linarith) (lt_min (by norm_num) (div_pos (by linarith) (by positivity)))
      have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have he1 : e < 1 := by
        have : e ≤ (1:ℝ)/2 := le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
      have heb : e ≤ (-d)/(2*(|c-d|+1)) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hmul : e*(2*(|c-d|+1)) ≤ -d :=
        (le_div_iff₀ (by positivity)).mp heb
      have hsign : e*(c-d) ≤ e*|c-d| := mul_le_mul_of_nonneg_left (le_abs_self _) he.le
      have hh := h e he heδ he1
      nlinarith
    rcases eq_or_lt_of_le hd with heq | hpos
    · right
      have hd0 : d = 0 := heq.symm
      refine ⟨hd0, ?_⟩
      let e := min (δ/2) (1/2)
      have he : 0 < e := lt_min (by linarith) (by norm_num)
      have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have he1 : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hh := h e he heδ he1
      rw [hd0] at hh
      nlinarith
    · exact Or.inl hpos
  · intro h
    rcases h with hd | ⟨hd,hc⟩
    · refine ⟨d/(|c-d|+1), by positivity, ?_⟩
      intro e he heb he1
      have hb : e*(|c-d|+1) < d := (lt_div_iff₀ (by positivity)).mp heb
      have hlo : -|c-d| ≤ c-d := neg_abs_le _
      have hm := mul_le_mul_of_nonneg_left hlo he.le
      nlinarith
    · refine ⟨1, by norm_num, ?_⟩
      intro e he heb he1
      rw [hd]
      nlinarith

/-- Source: hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem ess_iff_invasion_criterion_general (A : I → I → ℝ) (p : I → ℝ) :
    IsESS A p ↔ simplex p ∧ ∀ q, simplex q → q ≠ p →
      payoff A q p < payoff A p p ∨
        (payoff A q p = payoff A p p ∧ payoff A q q < payoff A p q) := by
  unfold IsESS
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro hq
  apply imp_congr_right
  intro hne
  have hlinear : ∀ e, payoff A q (mix p q e) < payoff A p (mix p q e) ↔
      0 < (1-e)*(payoff A p p-payoff A q p)+e*(payoff A p q-payoff A q q) := by
    intro e
    rw [payoff_mix, payoff_mix]
    constructor <;> intro h <;> nlinarith
  simp_rw [hlinear]
  rw [rare_linear_iff]
  constructor
  · intro h
    rcases h with h | ⟨h,h'⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h
    rcases h with h | ⟨h,h'⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- Source: hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem ess_nash_general (A : I → I → ℝ) (p q : I → ℝ)
    (hp : IsESS A p) (hq : simplex q) : payoff A q p ≤ payoff A p p := by
  by_cases hqp : q = p
  · simp [hqp]
  · rcases ((ess_iff_invasion_criterion_general A p).mp hp).2 q hq hqp with h | h
    · exact h.le
    · exact h.1.le

/-- Source: hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem ess_rest_general (A : I → I → ℝ) (p : I → ℝ)
    (hp : IsESS A p) : ∀ i, replicator A p i = 0 := by
  classical
  have hfit : ∀ i, marginalFit A p i ≤ payoff A p p := by
    intro i
    let q : I → ℝ := fun j => if j = i then 1 else 0
    have hq : simplex q := by
      constructor
      · intro j
        dsimp [q]
        split_ifs <;> norm_num
      · simp [q]
    have hn := ess_nash_general A p q hp hq
    simpa [payoff, q] using hn
  have hnon : ∀ i, 0 ≤ p i*(payoff A p p-marginalFit A p i) :=
    fun i => mul_nonneg (hp.1.1 i) (sub_nonneg.mpr (hfit i))
  have hsum : ∑i,p i*(payoff A p p-marginalFit A p i)=0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hp.1.2, one_mul, payoff]
    exact sub_self _
  have hz := (sum_eq_zero_iff_of_nonneg (fun i _ => hnon i)).mp hsum
  intro i
  have hi := hz i (mem_univ i)
  unfold replicator
  nlinarith

/-- Source: hofbauer_sigmund2003, pp. 481–482, eq. 3; hofbauer_sigmund2003, p. 486, eq. 15–18. -/
theorem symmetric_mean_fitness_derivative_general (A : I → I → ℝ)
    (x : ℝ → I → ℝ) (t : ℝ) (hx : simplex (x t))
    (hA : ∀ i j, A i j = A j i)
    (hd : ∀ i, HasDerivAt (fun u => x u i) (replicator A (x t) i) t) :
    HasDerivAt (fun u => payoff A (x u) (x u))
      (2 * ∑ i, x t i *
        (marginalFit A (x t) i - payoff A (x t) (x t)) ^ 2) t ∧
    0 ≤ 2 * ∑ i, x t i *
      (marginalFit A (x t) i - payoff A (x t) (x t)) ^ 2 := by
  have hm : ∀i, HasDerivAt (fun u=>marginalFit A (x u) i)
      (∑j,A i j*replicator A (x t) j) t := by
    intro i
    exact HasDerivAt.fun_sum (fun j (_ : j∈(univ:Finset I)) => (hd j).const_mul (A i j))
  have hp := HasDerivAt.fun_sum (fun i (_ : i∈(univ:Finset I)) => (hd i).mul (hm i))
  have hsym : ∑i,x t i*(∑j,A i j*replicator A (x t) j) =
      ∑j,replicator A (x t) j*marginalFit A (x t) j := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    unfold marginalFit
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [hA i j]
    ring
  have hvariance : ∑i,replicator A (x t) i*marginalFit A (x t) i =
      ∑i,x t i*(marginalFit A (x t) i-payoff A (x t) (x t))^2 := by
    have hterm : ∀i, x t i*(marginalFit A (x t) i-payoff A (x t) (x t))^2 =
        replicator A (x t) i*marginalFit A (x t) i -
          payoff A (x t) (x t)*replicator A (x t) i := by
      intro i
      unfold replicator
      ring
    simp only [hterm, sum_sub_distrib, ← mul_sum, replicator_sum_general A (x t) hx,
      mul_zero, sub_zero]
  constructor
  · convert hp using 1
    · rfl
    · rw [sum_add_distrib, hsym, hvariance]
      ring
  · exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => mul_nonneg (hx.1 i) (sq_nonneg _))

end Rhone.Dynamics
