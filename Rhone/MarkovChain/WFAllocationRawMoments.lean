/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFAllocationLD

/-!
# Raw moments of the Wright–Fisher multinomial allele allocation counts

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset
open scoped Matrix

/-- Source: ewens2004, sec. 3.1. -/
def rawFeatures (x y z : ℝ) : Fin 14 → ℝ :=
  ![1, x, y, z, x^2, y^2, x*y, x^2*y, x*y^2, x^2*y^2, z*x, z*y, z*x*y, z^2]

/-- Source: ewens2004, sec. 3.1. -/
def rawIncrementMatrix (g : Dynamics.Gametes ℝ) : Matrix (Fin 14) (Fin 14) ℝ :=
  let p := g.pA
  let q := g.pB
  let t := g.x11
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    p, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    q, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    t, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    p, 2*p, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    q, 0, 2*q, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    t, q, p, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    t, 2*t, p, 0, q, 0, 2*p, 1, 0, 0, 0, 0, 0, 0;
    t, q, 2*t, 0, 0, p, 2*q, 0, 1, 0, 0, 0, 0, 0;
    t, 2*t, 2*t, 0, q, p, 4*t, 2*q, 2*p, 1, 0, 0, 0, 0;
    t, t, 0, p, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    t, 0, t, q, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    t, t, t, t, 0, 0, t, 0, 0, 0, q, p, 1, 0;
    t, 0, 0, 2*t, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Source: ewens2004, sec. 3.1. -/
def rawMomentFormula (M : ℕ) (g : Dynamics.Gametes ℝ) : Fin 14 → ℝ :=
  let m := (M : ℝ)
  let p := g.pA
  let q := g.pB
  let t := g.x11
  ![1,
    m*p,
    m*q,
    m*t,
    m*p^2*(m - 1) + m*p,
    m*q^2*(m - 1) + m*q,
    m*p*q*(m - 1) + m*t,
    m*p^2*q*(m - 2)*(m - 1) + m*t + m*(m - 1)*(p*q + 2*p*t),
    m*p*q^2*(m - 2)*(m - 1) + m*t + m*(m - 1)*(p*q + 2*q*t),
    m*p^2*q^2*(m - 3)*(m - 2)*(m - 1) + m*t + m*(m - 2)*(m - 1)*(p^2*q + p*q^2 + 4*p*q*t) + m*(m
    - 1)*(p*q + 2*p*t + 2*q*t + 2*t^2),
    m*p*t*(m - 1) + m*t,
    m*q*t*(m - 1) + m*t,
    m*p*q*t*(m - 2)*(m - 1) + m*t + m*(m - 1)*(p*t + q*t + t^2),
    m*t^2*(m - 1) + m*t]

/-- Source: ewens2004, sec. 3.1. -/
def rawCountFeatures (M : ℕ) (a : Rhone.MarkovChain.AlleleCounts M 4) : Fin 14 → ℝ :=
  rawFeatures ((a.val 0 : ℝ)+(a.val 1 : ℝ))
    ((a.val 0 : ℝ)+(a.val 2 : ℝ)) (a.val 0 : ℝ)

/-- Source: ewens2004, sec. 3.1. -/
theorem raw_increment_formula (g : Dynamics.Gametes ℝ) (ht : g.total = 1) (x y z : ℝ) :
    (∑ i : Fin 4, Dynamics.TwoLocusSelection.vector g i •
      rawFeatures (x+if i = 0 ∨ i = 1 then 1 else 0)
        (y+if i = 0 ∨ i = 2 then 1 else 0) (z+if i = 0 then 1 else 0)) =
      rawIncrementMatrix g *ᵥ rawFeatures x y z := by
  have h22 : g.x22 = 1-g.x11-g.x12-g.x21 := by
    unfold Dynamics.Gametes.total at ht
    linarith
  ext i
  fin_cases i <;>
    norm_num [rawFeatures, rawIncrementMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Dynamics.TwoLocusSelection.vector, Dynamics.Gametes.pA,
          Dynamics.Gametes.pB, h22] <;> ring

/-- Source: ewens2004, sec. 3.1. -/
theorem raw_formula_step (M : ℕ) (g : Dynamics.Gametes ℝ) :
    rawIncrementMatrix g *ᵥ rawMomentFormula M g = rawMomentFormula (M+1) g := by
  ext i
  fin_cases i <;>
    norm_num [rawIncrementMatrix, rawMomentFormula, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Nat.cast_add, Nat.cast_one] <;> ring

private theorem sum_allocation_cons (M : ℕ)
    (f : (Fin (M + 1) → Fin 4) → (Fin 14 → ℝ)) :
    (∑ ω : Fin (M + 1) → Fin 4, f ω) =
      ∑ i : Fin 4, ∑ ω : Fin M → Fin 4, f (Fin.cons i ω) := by
  let e : (Fin 4 × (Fin M → Fin 4)) ≃ (Fin (M + 1) → Fin 4) :=
    { toFun := fun a => Fin.cons a.1 a.2
      invFun := fun ω => (ω 0, fun t => ω t.succ)
      left_inv := fun a => by simp
      right_inv := fun ω => by ext t; refine Fin.cases ?_ (fun j => ?_) t <;> simp }
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem allocation_count_cons_real (M : ℕ) (i : Fin 4)
    (ω : Fin M → Fin 4) (l : Fin 4) :
    ((wfAlleleAllocationCounts (M+1) 4 (Fin.cons i ω)).val l : ℝ) =
      ((wfAlleleAllocationCounts M 4 ω).val l : ℝ) + if i = l then 1 else 0 := by
  have hcount (N : ℕ) (η : Fin N → Fin 4) :
      ((wfAlleleAllocationCounts N 4 η).val l : ℝ) =
        ∑ t : Fin N, if η t = l then (1 : ℝ) else 0 := by
    have hn : (wfAlleleAllocationCounts N 4 η).val l =
        ∑ t : Fin N, if η t = l then 1 else 0 := by
      rw [wfAlleleAllocationCounts_apply, card_eq_sum_ones, sum_filter]
    exact_mod_cast hn
  rw [hcount, hcount, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, add_comm]

private theorem raw_count_cons (M : ℕ) (i : Fin 4) (ω : Fin M → Fin 4) :
    rawCountFeatures (M+1) (wfAlleleAllocationCounts (M+1) 4 (Fin.cons i ω)) =
      rawFeatures
        (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+
          ((wfAlleleAllocationCounts M 4 ω).val 1 : ℝ)+
          if i = 0 ∨ i = 1 then 1 else 0)
        (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+
          ((wfAlleleAllocationCounts M 4 ω).val 2 : ℝ)+
          if i = 0 ∨ i = 2 then 1 else 0)
        (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+ if i = 0 then 1 else 0) := by
  unfold rawCountFeatures
  simp only [allocation_count_cons_real]
  fin_cases i <;> congr 1 <;> norm_num <;> ring

/-- Source: ewens2004, sec. 3.1. -/
theorem allocation_raw_moments (M : ℕ) (g : Dynamics.Gametes ℝ) (ht : g.total = 1) :
    (∑ ω : Fin M → Fin 4, allocationWeight M g ω •
      rawCountFeatures M (wfAlleleAllocationCounts M 4 ω)) =
      rawMomentFormula M g := by
  classical
  induction M with
  | zero =>
    ext i
    fin_cases i <;>
      simp [allocationWeight, rawCountFeatures, wfAlleleAllocationCounts,
        rawFeatures, rawMomentFormula]
  | succ M ih =>
    rw [sum_allocation_cons]
    have hw (i : Fin 4) (ω : Fin M → Fin 4) :
        allocationWeight (M+1) g (Fin.cons i ω) =
          Dynamics.TwoLocusSelection.vector g i*allocationWeight M g ω := by
      simp [allocationWeight, Fin.prod_univ_succ]
    simp_rw [hw, raw_count_cons]
    rw [sum_comm]
    have hinner (ω : Fin M → Fin 4) :
        (∑ i : Fin 4, (Dynamics.TwoLocusSelection.vector g i*allocationWeight M g ω) •
          rawFeatures
            (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+
              ((wfAlleleAllocationCounts M 4 ω).val 1 : ℝ)+
              if i = 0 ∨ i = 1 then 1 else 0)
            (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+
              ((wfAlleleAllocationCounts M 4 ω).val 2 : ℝ)+
              if i = 0 ∨ i = 2 then 1 else 0)
            (((wfAlleleAllocationCounts M 4 ω).val 0 : ℝ)+ if i = 0 then 1 else 0)) =
        allocationWeight M g ω • (rawIncrementMatrix g *ᵥ
          rawCountFeatures M (wfAlleleAllocationCounts M 4 ω)) := by
      simp_rw [mul_comm (Dynamics.TwoLocusSelection.vector g _) (allocationWeight M g ω), mul_smul]
      rw [← smul_sum, raw_increment_formula g ht]
      rfl
    simp_rw [hinner, ← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum, ih, raw_formula_step]

end Rhone.MarkovChain.WFAllocationLD
