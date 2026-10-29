/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisher

/-! # Weir–Cockerham variance components for a haploid sampling design -/

@[expose] public section

namespace Rhone.Statistics.WeirCockerham

open Finset MarkovChain

variable {r : ℕ}

def countSupport (n : Fin r → ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i => range (n i + 1)

noncomputable def condMass (n : Fin r → ℕ) (p : Fin r → ℝ) (x : Fin r → ℕ) : ℝ :=
  ∏ i, binomRow (n i) (p i) (x i)

noncomputable def condExpect (n : Fin r → ℕ) (p : Fin r → ℝ) (f : (Fin r → ℕ) → ℝ) : ℝ :=
  ∑ x ∈ countSupport n, condMass n p x * f x

noncomputable def wcExpect {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (n : Fin r → ℕ)
    (P : Fin r → Ω → ℝ) (f : (Fin r → ℕ) → ℝ) : ℝ :=
  ∑ ω, w ω * condExpect n (fun i => P i ω) f

theorem condExpect_prod (n : Fin r → ℕ) (p : Fin r → ℝ) (g : Fin r → ℕ → ℝ) :
    condExpect n p (fun x => ∏ i, g i (x i)) =
      ∏ i, ∑ y ∈ range (n i + 1), binomRow (n i) (p i) y * g i y := by
  rw [Finset.prod_univ_sum (fun i => range (n i + 1))
    (fun i y => binomRow (n i) (p i) y * g i y)]
  unfold condExpect condMass countSupport
  exact sum_congr rfl fun x _ => (prod_mul_distrib).symm

theorem condExpect_one (n : Fin r → ℕ) (p : Fin r → ℝ) :
    condExpect n p (fun _ => 1) = 1 := by
  have := condExpect_prod n p (fun _ _ => (1 : ℝ))
  simpa [sum_binomRow] using this

theorem condExpect_add (n : Fin r → ℕ) (p : Fin r → ℝ) (f g : (Fin r → ℕ) → ℝ) :
    condExpect n p (fun x => f x + g x) = condExpect n p f + condExpect n p g := by
  simp only [condExpect, mul_add, sum_add_distrib]

theorem condExpect_const_mul (n : Fin r → ℕ) (p : Fin r → ℝ) (c : ℝ) (f : (Fin r → ℕ) → ℝ) :
    condExpect n p (fun x => c * f x) = c * condExpect n p f := by
  simp only [condExpect, mul_sum]
  exact sum_congr rfl fun x _ => by ring

theorem condExpect_sum {ι : Type*} (s : Finset ι) (n : Fin r → ℕ) (p : Fin r → ℝ)
    (f : ι → (Fin r → ℕ) → ℝ) :
    condExpect n p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, condExpect n p (f i) := by
  simp only [condExpect, mul_sum]
  exact sum_comm

theorem condExpect_coord (n : Fin r → ℕ) (p : Fin r → ℝ) (a : Fin r) :
    condExpect n p (fun x => (x a : ℝ)) = n a * p a := by
  have := condExpect_prod n p (fun i y => if i = a then (y : ℝ) else 1)
  simp only [prod_ite_eq', mem_univ, ite_true] at this
  rw [this, prod_eq_single a]
  · simp [sum_binomRow_mul]
  · intro i _ hi
    simp [hi, sum_binomRow]
  · simp

theorem condExpect_coord_sq (n : Fin r → ℕ) (p : Fin r → ℝ) (a : Fin r) :
    condExpect n p (fun x => (x a : ℝ) * x a) = n a * p a * (1 - p a) + (n a * p a) ^ 2 := by
  have := condExpect_prod n p (fun i y => if i = a then (y : ℝ) * y else 1)
  simp only [prod_ite_eq', mem_univ, ite_true] at this
  rw [this, prod_eq_single a]
  · simp [sum_binomRow_mul_mul]
  · intro i _ hi
    simp [hi, sum_binomRow]
  · simp

theorem condExpect_coord_mul (n : Fin r → ℕ) (p : Fin r → ℝ) {a b : Fin r} (hab : a ≠ b) :
    condExpect n p (fun x => (x a : ℝ) * x b) = n a * p a * (n b * p b) := by
  have := condExpect_prod n p
    (fun i y => if i = a then (y : ℝ) else if i = b then (y : ℝ) else 1)
  have hl : ∀ x : Fin r → ℕ, (∏ i, if i = a then (x i : ℝ) else if i = b then (x i : ℝ) else 1)
      = (x a : ℝ) * x b := fun x => by
    rw [prod_eq_mul a b hab]
    · simp
    · intro c _ hc
      simp [hc.1, hc.2]
    · simp
    · simp
  simp only [hl] at this
  rw [this, prod_eq_mul a b hab]
  · simp [sum_binomRow_mul]
  · intro c _ hc
    simp [hc.1, hc.2, sum_binomRow]
  · simp
  · simp

theorem condExpect_coord_cross (n : Fin r → ℕ) (p : Fin r → ℝ) (a b : Fin r) :
    condExpect n p (fun x => (x a : ℝ) * x b) =
      n a * p a * (n b * p b) + if a = b then n a * p a * (1 - p a) else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [condExpect_coord_sq]
    simp only [ite_true]
    ring
  · rw [condExpect_coord_mul n p hab]
    simp [hab]

noncomputable def totalN (n : Fin r → ℕ) : ℝ := ∑ i, (n i : ℝ)

noncomputable def sumSqN (n : Fin r → ℕ) : ℝ := ∑ i, (n i : ℝ) ^ 2

noncomputable def ncBar (n : Fin r → ℕ) : ℝ :=
  (totalN n - sumSqN n / totalN n) / ((r : ℝ) - 1)

noncomputable def pBar (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ := (∑ i, (x i : ℝ)) / totalN n

noncomputable def msp (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ :=
  (∑ i, (n i : ℝ) * ((x i : ℝ) / n i - pBar n x) ^ 2) / ((r : ℝ) - 1)

noncomputable def msg (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ :=
  (∑ i, (n i : ℝ) * ((x i : ℝ) / n i) * (1 - (x i : ℝ) / n i)) / (totalN n - r)

noncomputable def wcA (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ := (msp n x - msg n x) / ncBar n

noncomputable def wcB (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ := msg n x

noncomputable def sqSum (n : Fin r → ℕ) (x : Fin r → ℕ) : ℝ := ∑ i, (x i : ℝ) ^ 2 / n i

noncomputable def cntSum (x : Fin r → ℕ) : ℝ := ∑ i, (x i : ℝ)

theorem ssp_eq (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (hN : totalN n ≠ 0) (x : Fin r → ℕ) :
    ∑ i, (n i : ℝ) * ((x i : ℝ) / n i - pBar n x) ^ 2 =
      sqSum n x - cntSum x ^ 2 / totalN n := by
  have h : ∀ i, (n i : ℝ) * ((x i : ℝ) / n i - pBar n x) ^ 2 =
      (x i : ℝ) ^ 2 / n i - 2 * pBar n x * x i + pBar n x ^ 2 * n i := by
    intro i
    have : (n i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
    field_simp
    ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hX : ∑ i, (x i : ℝ) = cntSum x := rfl
  have hT : ∑ i, (n i : ℝ) = totalN n := rfl
  rw [hX, hT]
  unfold sqSum pBar
  rw [hX]
  field_simp
  ring

theorem ssg_eq (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (x : Fin r → ℕ) :
    ∑ i, (n i : ℝ) * ((x i : ℝ) / n i) * (1 - (x i : ℝ) / n i) =
      cntSum x - sqSum n x := by
  have h : ∀ i, (n i : ℝ) * ((x i : ℝ) / n i) * (1 - (x i : ℝ) / n i) =
      (x i : ℝ) - (x i : ℝ) ^ 2 / n i := by
    intro i
    have : (n i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
    field_simp
  simp only [h, sum_sub_distrib]
  rfl

theorem condExpect_sqSum (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (p : Fin r → ℝ) :
    condExpect n p (sqSum n) = ∑ i, (p i * (1 - p i) + n i * p i ^ 2) := by
  unfold sqSum
  rw [condExpect_sum]
  refine sum_congr rfl fun i _ => ?_
  have : (n i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
  have h : (fun x : Fin r → ℕ => (x i : ℝ) ^ 2 / n i) =
      fun x => (1 / (n i : ℝ)) * ((x i : ℝ) * x i) := funext fun x => by ring
  rw [h, condExpect_const_mul, condExpect_coord_sq]
  field_simp

theorem condExpect_cntSum (n : Fin r → ℕ) (p : Fin r → ℝ) :
    condExpect n p cntSum = ∑ i, (n i : ℝ) * p i := by
  unfold cntSum
  rw [condExpect_sum]
  exact sum_congr rfl fun i _ => condExpect_coord n p i

theorem condExpect_cntSum_sq (n : Fin r → ℕ) (p : Fin r → ℝ) :
    condExpect n p (fun x => cntSum x ^ 2) =
      ∑ i, (n i : ℝ) * p i * (1 - p i) + (∑ i, (n i : ℝ) * p i) ^ 2 := by
  have h : (fun x : Fin r → ℕ => cntSum x ^ 2) =
      fun x => ∑ i, ∑ j, (x i : ℝ) * x j := funext fun x => by
    unfold cntSum
    rw [sq, sum_mul_sum]
  rw [h, condExpect_sum]
  simp only [condExpect_sum, condExpect_coord_cross, sum_add_distrib, sum_ite_eq, mem_univ,
    ite_true]
  rw [add_comm, sq, sum_mul_sum]

section Outer

variable {Ω : Type*} [Fintype Ω]

theorem wcExpect_comb (w : Ω → ℝ) (n : Fin r → ℕ) (P : Fin r → Ω → ℝ) (a b c : ℝ) :
    wcExpect w n P (fun x => a * sqSum n x + b * cntSum x ^ 2 + c * cntSum x) =
      a * wcExpect w n P (sqSum n) + b * wcExpect w n P (fun x => cntSum x ^ 2)
        + c * wcExpect w n P cntSum := by
  unfold wcExpect
  simp only [condExpect_add, condExpect_const_mul, mul_add, sum_add_distrib, mul_sum]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact sum_congr rfl fun ω _ => by ring

theorem wcExpect_add (w : Ω → ℝ) (n : Fin r → ℕ) (P : Fin r → Ω → ℝ) (f g : (Fin r → ℕ) → ℝ) :
    wcExpect w n P (fun x => f x + g x) = wcExpect w n P f + wcExpect w n P g := by
  unfold wcExpect
  simp only [condExpect_add, mul_add, sum_add_distrib]

theorem freq_second (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (P : Fin r → Ω → ℝ) (p F : ℝ) (i : Fin r)
    (hmean : ∀ i, ∑ ω, w ω * P i ω = p)
    (hvar : ∀ i, ∑ ω, w ω * (P i ω - p) ^ 2 = F * (p * (1 - p))) :
    ∑ ω, w ω * P i ω ^ 2 = p ^ 2 + F * (p * (1 - p)) := by
  have h : ∀ ω, w ω * (P i ω - p) ^ 2 =
      w ω * P i ω ^ 2 - 2 * p * (w ω * P i ω) + p ^ 2 * w ω := fun ω => by ring
  have := hvar i
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, hmean, hw] at this
  linarith

theorem freq_cross (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (P : Fin r → Ω → ℝ) (p F : ℝ) (i j : Fin r)
    (hmean : ∀ i, ∑ ω, w ω * P i ω = p)
    (hvar : ∀ i, ∑ ω, w ω * (P i ω - p) ^ 2 = F * (p * (1 - p)))
    (hcov : ∀ i j, i ≠ j → ∑ ω, w ω * ((P i ω - p) * (P j ω - p)) = 0) :
    ∑ ω, w ω * (P i ω * P j ω) = p ^ 2 + if i = j then F * (p * (1 - p)) else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, ← sq]
    exact freq_second w hw P p F i hmean hvar
  · have h : ∀ ω, w ω * ((P i ω - p) * (P j ω - p)) =
        w ω * (P i ω * P j ω) - p * (w ω * P j ω) - p * (w ω * P i ω) + p ^ 2 * w ω :=
      fun ω => by ring
    have := hcov i j hij
    simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, hmean, hw] at this
    simp only [hij, ite_false]
    linarith

theorem wcExpect_sqSum (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (P : Fin r → Ω → ℝ) (p F : ℝ)
    (hmean : ∀ i, ∑ ω, w ω * P i ω = p)
    (hvar : ∀ i, ∑ ω, w ω * (P i ω - p) ^ 2 = F * (p * (1 - p))) :
    wcExpect w n P (sqSum n) =
      (r : ℝ) * ((1 - F) * (p * (1 - p))) + totalN n * (p ^ 2 + F * (p * (1 - p))) := by
  unfold wcExpect
  simp only [condExpect_sqSum n hn, mul_sum]
  rw [sum_comm]
  have h : ∀ i : Fin r, ∑ ω, w ω * (P i ω * (1 - P i ω) + n i * P i ω ^ 2) =
      p - (p ^ 2 + F * (p * (1 - p))) + n i * (p ^ 2 + F * (p * (1 - p))) := by
    intro i
    have e : ∀ ω, w ω * (P i ω * (1 - P i ω) + n i * P i ω ^ 2) =
        w ω * P i ω + ((n i : ℝ) - 1) * (w ω * P i ω ^ 2) := fun ω => by ring
    simp only [e, sum_add_distrib, ← mul_sum, hmean, freq_second w hw P p F i hmean hvar]
    ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← sum_mul, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold totalN
  ring

theorem wcExpect_cntSum (w : Ω → ℝ) (n : Fin r → ℕ)
    (P : Fin r → Ω → ℝ) (p : ℝ) (hmean : ∀ i, ∑ ω, w ω * P i ω = p) :
    wcExpect w n P cntSum = totalN n * p := by
  unfold wcExpect
  simp only [condExpect_cntSum, mul_sum]
  rw [sum_comm]
  have h : ∀ i : Fin r, ∑ ω, w ω * ((n i : ℝ) * P i ω) = n i * p := by
    intro i
    have e : ∀ ω, w ω * ((n i : ℝ) * P i ω) = n i * (w ω * P i ω) := fun ω => by ring
    simp only [e, ← mul_sum, hmean]
  simp only [h]
  unfold totalN
  rw [sum_mul]

theorem wcExpect_cntSum_sq (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (n : Fin r → ℕ)
    (P : Fin r → Ω → ℝ) (p F : ℝ)
    (hmean : ∀ i, ∑ ω, w ω * P i ω = p)
    (hvar : ∀ i, ∑ ω, w ω * (P i ω - p) ^ 2 = F * (p * (1 - p)))
    (hcov : ∀ i j, i ≠ j → ∑ ω, w ω * ((P i ω - p) * (P j ω - p)) = 0) :
    wcExpect w n P (fun x => cntSum x ^ 2) =
      totalN n ^ 2 * p ^ 2 + F * (p * (1 - p)) * sumSqN n
        + totalN n * ((1 - F) * (p * (1 - p))) := by
  unfold wcExpect
  simp only [condExpect_cntSum_sq]
  have h : ∀ ω, w ω * (∑ i, (n i : ℝ) * P i ω * (1 - P i ω) + (∑ i, (n i : ℝ) * P i ω) ^ 2) =
      ∑ i, (n i : ℝ) * (w ω * P i ω - w ω * P i ω ^ 2) +
        ∑ i, ∑ j, (n i : ℝ) * n j * (w ω * (P i ω * P j ω)) := by
    intro ω
    rw [sq, sum_mul_sum, mul_add, mul_sum, mul_sum]
    congr 1
    · exact sum_congr rfl fun i _ => by ring
    · refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
  simp only [h, sum_add_distrib]
  rw [sum_comm (f := fun ω i => (n i : ℝ) * (w ω * P i ω - w ω * P i ω ^ 2))]
  have h1 : ∀ i : Fin r, ∑ ω, (n i : ℝ) * (w ω * P i ω - w ω * P i ω ^ 2) =
      n i * ((1 - F) * (p * (1 - p))) := by
    intro i
    simp only [← mul_sum, sum_sub_distrib, hmean, freq_second w hw P p F i hmean hvar]
    ring
  have h2 : ∀ i : Fin r, ∑ ω, ∑ j, (n i : ℝ) * n j * (w ω * (P i ω * P j ω)) =
      ∑ j, (n i : ℝ) * n j * (p ^ 2 + if i = j then F * (p * (1 - p)) else 0) := by
    intro i
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    simp only [← mul_sum, freq_cross w hw P p F i j hmean hvar hcov]
  simp only [h1]
  rw [sum_comm (f := fun ω i => ∑ j, (n i : ℝ) * n j * (w ω * (P i ω * P j ω)))]
  simp only [h2, mul_add, sum_add_distrib]
  unfold totalN sumSqN
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul]
  simp only [sq]
  ring

end Outer

section Main

variable {Ω : Type*} [Fintype Ω]

private theorem totalN_cast (n : Fin r → ℕ) : totalN n = ((∑ i, n i : ℕ) : ℝ) := by
  simp [totalN]

theorem design_facts (hr : 2 ≤ r) (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (hnr : r < ∑ i, n i) :
    0 < totalN n ∧ (r : ℝ) < totalN n ∧ sumSqN n < totalN n ^ 2 := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hNr : (r : ℝ) < totalN n := by
    rw [totalN_cast]; exact_mod_cast hnr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlt : ∀ i, (n i : ℝ) < totalN n := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have h1 : n i + n j ≤ ∑ k, n k := by
      rw [← sum_pair hj.symm]
      exact sum_le_sum_of_subset (subset_univ _)
    have h2 := hn j
    have : ((n i : ℕ) : ℝ) < ((∑ k, n k : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rwa [totalN_cast]
  refine ⟨by linarith, hNr, ?_⟩
  unfold sumSqN
  have : ∑ i, (n i : ℝ) ^ 2 < ∑ i, (n i : ℝ) * totalN n := by
    refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
    have hp : (0 : ℝ) < n i := by exact_mod_cast hn i
    nlinarith [hlt i]
  rw [← sum_mul] at this
  have hT : ∑ i, (n i : ℝ) = totalN n := rfl
  rw [hT] at this
  nlinarith

theorem msp_eq (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (hN : totalN n ≠ 0) :
    msp n = fun x => (1 / ((r : ℝ) - 1)) * sqSum n x
      + ((-1 / totalN n) * (1 / ((r : ℝ) - 1))) * cntSum x ^ 2 + 0 * cntSum x := by
  funext x
  unfold msp
  rw [ssp_eq n hn hN x]
  ring

theorem msg_eq (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    msg n = fun x => (-1 / (totalN n - r)) * sqSum n x + 0 * cntSum x ^ 2
      + (1 / (totalN n - r)) * cntSum x := by
  funext x
  unfold msg
  rw [ssg_eq n hn x]
  ring

theorem wc_unbiased (hr : 2 ≤ r) (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (hnr : r < ∑ i, n i) (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (P : Fin r → Ω → ℝ) (p F : ℝ)
    (hmean : ∀ i, ∑ ω, w ω * P i ω = p)
    (hvar : ∀ i, ∑ ω, w ω * (P i ω - p) ^ 2 = F * (p * (1 - p)))
    (hcov : ∀ i j, i ≠ j → ∑ ω, w ω * ((P i ω - p) * (P j ω - p)) = 0) :
    wcExpect w n P (wcA n) = F * (p * (1 - p)) ∧
    wcExpect w n P (wcB n) = (1 - F) * (p * (1 - p)) ∧
    wcExpect w n P (fun x => wcA n x + wcB n x) = p * (1 - p) := by
  obtain ⟨hN, hNr, hS⟩ := design_facts hr n hn hnr
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hd : (0 : ℝ) < totalN n - r := by linarith
  have hnc : 0 < ncBar n := by
    unfold ncBar
    have : 0 < totalN n - sumSqN n / totalN n := by
      have : sumSqN n / totalN n < totalN n := by
        rw [div_lt_iff₀ hN]; nlinarith
      linarith
    positivity
  have hQ := wcExpect_sqSum w hw n hn P p F hmean hvar
  have hX := wcExpect_cntSum w n P p hmean
  have hXX := wcExpect_cntSum_sq w hw n P p F hmean hvar hcov
  have hN0 := hN.ne'
  have hr10 := hr1.ne'
  have hd0 := hd.ne'
  have hnc0 := hnc.ne'
  have hncdef : ncBar n * ((r : ℝ) - 1) = totalN n - sumSqN n / totalN n := by
    unfold ncBar; field_simp
  have hMSP : wcExpect w n P (msp n) = (1 - F) * (p * (1 - p)) + F * (p * (1 - p)) * ncBar n := by
    rw [msp_eq n hn hN0, wcExpect_comb, hQ, hX, hXX]
    have : sumSqN n / totalN n = totalN n - ncBar n * ((r : ℝ) - 1) := by linarith
    field_simp
    have h2 : sumSqN n = totalN n * (totalN n - ncBar n * ((r : ℝ) - 1)) := by
      field_simp at this; linarith
    rw [h2]
    ring
  have hMSG : wcExpect w n P (msg n) = (1 - F) * (p * (1 - p)) := by
    rw [msg_eq n hn, wcExpect_comb, hQ, hX, hXX]
    field_simp
    ring
  have hb : wcExpect w n P (wcB n) = (1 - F) * (p * (1 - p)) := hMSG
  have ha : wcExpect w n P (wcA n) = F * (p * (1 - p)) := by
    have hform : wcA n = fun x => (1 / ncBar n) * msp n x + (-1 / ncBar n) * msg n x := by
      funext x
      unfold wcA
      ring
    rw [hform]
    have hlin : ∀ (a b : ℝ), wcExpect w n P (fun x => a * msp n x + b * msg n x) =
        a * wcExpect w n P (msp n) + b * wcExpect w n P (msg n) := by
      intro a b
      unfold wcExpect
      simp only [condExpect_add, condExpect_const_mul, mul_add, sum_add_distrib, mul_sum]
      refine congrArg₂ _ ?_ ?_ <;> exact sum_congr rfl fun ω _ => by ring
    rw [hlin, hMSP, hMSG]
    field_simp
    ring
  refine ⟨ha, hb, ?_⟩
  rw [wcExpect_add, ha, hb]
  ring

end Main

end Rhone.Statistics.WeirCockerham
