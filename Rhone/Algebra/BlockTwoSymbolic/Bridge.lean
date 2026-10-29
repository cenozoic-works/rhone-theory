/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Solution
public import Rhone.Algebra.BlockTwoSymbolic.Block
public import Rhone.Algebra.BlockTwoSymbolic.Unique

/-! # From the universal polynomial certificate to a solution, for either reading of the tower -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

noncomputable def piAL : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      SymbolicFrequencies.piAF

noncomputable def piBL : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      SymbolicFrequencies.piBF

def s22 : St := ⟨0, 0, 0, 0, 0, 0, 0, 2⟩

theorem s22_mem_closureList : s22 ∈ closureList := by decide

def IsSolutionG (tA tB r pa pb : GenericField.L SymbolicFrequencies.Kpi)
    (q : St → GenericField.L SymbolicFrequencies.Kpi) : Prop :=
  (∀ s ∈ recStates, lhsC tA tB r s * q s
      = rhsC 1 (tA * pa) (tA * (1 - pa)) (tB * pb) (tB * (1 - pb)) r q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC pa (1 - pa) pb (1 - pb) s)

section Bridge

variable (uP vP aP bP rP : GenericField.P SymbolicFrequencies.Kpi)
    (tA tB r pa pb : GenericField.L SymbolicFrequencies.Kpi)

theorem lhsW_mapG_aux (A B : GenericField.P SymbolicFrequencies.Kpi)
    (hu : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) A = 2 * tA)
    (hv : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) B = 2 * tB)
    (hr : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) rP = r) (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (2 * ((s.n * (s.n - 1) : ℕ) : GenericField.P SymbolicFrequencies.Kpi) + A * (s.nA : ℕ) + B *
            (s.nB : ℕ)
          + 2 * rP * (s.t : ℕ))
      = 2 * lhsC tA tB r s := by
  simp only [lhsC, map_add, map_mul, map_ofNat, map_natCast, hu, hv, hr]
  ring

theorem lhsW_mapG
    (hu : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP + vP) = 2 * tA)
    (hv : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP - vP) = 2 * tB)
    (hr : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) rP = r) (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (lhsW uP vP rP s) = 2 * lhsC tA tB r s := by
  rw [lhsW]
  exact lhsW_mapG_aux rP tA tB r (uP + vP) (uP - vP) hu hv hr s

theorem rhsW_mapG_aux (A B : GenericField.P SymbolicFrequencies.Kpi)
    (hu : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) A = 2 * tA)
    (hv : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) B = 2 * tB)
    (hr : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) rP = r)
    (ha : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) aP = pa)
    (hb : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) bP = pb)
    (N : St → GenericField.P SymbolicFrequencies.Kpi) (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (rhsC 2 (A * aP) (A * (1 - aP)) (B * bP) (B * (1 - bP)) (2 * rP) N s)
      = 2 * rhsC 1 (tA * pa) (tA * (1 - pa)) (tB * pb) (tB * (1 - pb)) r
          (fun z => algebraMap (GenericField.P SymbolicFrequencies.Kpi)
              (GenericField.L SymbolicFrequencies.Kpi) (N z)) s := by
  have e0 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 2 = 2 * 1 := by rw [map_ofNat, mul_one]
  have e1 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (A * aP) = 2 * (tA * pa) := by
    rw [map_mul, hu, ha]; ring
  have e2 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (A * (1 - aP))
      = 2 * (tA * (1 - pa)) := by
    rw [map_mul, map_sub, map_one, hu, ha]; ring
  have e3 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (B * bP) = 2 * (tB * pb) := by
    rw [map_mul, hv, hb]; ring
  have e4 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (B * (1 - bP))
      = 2 * (tB * (1 - pb)) := by
    rw [map_mul, map_sub, map_one, hv, hb]; ring
  have e5 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 * rP) = 2 * r := by
    rw [map_mul, map_ofNat, hr]
  rw [rhsC_map, e0, e1, e2, e3, e4, e5, rhsC_scale]

theorem rhsW_mapG
    (hu : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP + vP) = 2 * tA)
    (hv : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP - vP) = 2 * tB)
    (hr : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) rP = r)
    (ha : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) aP = pa)
    (hb : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) bP = pb)
    (N : St → GenericField.P SymbolicFrequencies.Kpi) (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (rhsW uP vP aP bP rP N s)
      = 2 * rhsC 1 (tA * pa) (tA * (1 - pa)) (tB * pb) (tB * (1 - pb)) r
          (fun z => algebraMap (GenericField.P SymbolicFrequencies.Kpi)
              (GenericField.L SymbolicFrequencies.Kpi) (N z)) s := by
  rw [rhsW]
  exact rhsW_mapG_aux aP bP rP tA tB r pa pb (uP + vP) (uP - vP) hu hv hr ha hb N s

theorem isSolutionG_of_poly
    (hu : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP + vP) = 2 * tA)
    (hv : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (uP - vP) = 2 * tB)
    (hr : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) rP = r)
    (ha : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) aP = pa)
    (hb : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) bP = pb)
    (N : St → GenericField.P SymbolicFrequencies.Kpi) (Dc : GenericField.P SymbolicFrequencies.Kpi)
        (hD : Dc ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsW uP vP rP s * N s = rhsW uP vP aP bP rP N s)
    (hbd : ∀ s ∈ bdryStates, N s = bdryC aP (1 - aP) bP (1 - bP) s * Dc) :
    IsSolutionG tA tB r pa pb
        (fun s => algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (N s)
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹) := by
  have hDL : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) Dc ≠ 0 := polyL_ne_zero hD
  constructor
  · intro s hs
    have h := congrArg
        (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi)) (hrec s hs)
    rw [map_mul, lhsW_mapG uP vP rP tA tB r hu hv hr,
      rhsW_mapG uP vP aP bP rP tA tB r pa pb hu hv hr ha hb] at h
    change lhsC tA tB r s *
        (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (N s)
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹) = _
    rw [rhsC_mul_const]
    linear_combination
        ((algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹ / 2) * h
  · intro s hs
    have h := congrArg
        (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi)) (hbd s hs)
    rw [map_mul, bdryC_map] at h
    simp only [map_sub, map_one, ha, hb] at h
    change algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (N s)
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹ = _
    rw [h]
    exact mul_inv_cancel_right₀ hDL _

end Bridge

theorem unique_of_isSolutionG {tA tB r pa pb : GenericField.L SymbolicFrequencies.Kpi}
    (ne_lhs02 : (2 + 2 * tB : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_lhs20 : (2 + 2 * tA : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_lhs11 : (2 + tA + tB : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_d1_12 : (2 + tA + 2 * tB + r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_d1_21 : (2 + 2 * tA + tB + r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_E12 : ((6 + tA + 2 * tB) * (2 + tA + 2 * tB + r) - 4 * r : GenericField.L
        SymbolicFrequencies.Kpi) ≠ 0)
    (ne_E21 : ((6 + 2 * tA + tB) * (2 + 2 * tA + tB + r) - 4 * r : GenericField.L
        SymbolicFrequencies.Kpi) ≠ 0)
    (ne_d2_22 : (2 + 2 * tA + 2 * tB + 2 * r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_W22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) : GenericField.L
        SymbolicFrequencies.Kpi) ≠ 0)
    (ne_W4_22 : ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r :
      GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    (ne_D22 : ((12 + 2 * tA + 2 * tB)
        * ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r)
      - 8 * r * (2 + 2 * tA + 2 * tB + 2 * r) : GenericField.L SymbolicFrequencies.Kpi) ≠ 0)
    {q q2 : St → GenericField.L SymbolicFrequencies.Kpi} (h : IsSolutionG tA tB r pa pb q)
    (h2 : IsSolutionG tA tB r pa pb q2) : ∀ s ∈ closureList, q s = q2 s := by
  intro s hs
  have key := unique_auxF tA tB r pa (1 - pa) pb (1 - pb) (fun z => q z - q2 z)
    ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12 ne_d1_21 ne_E12 ne_E21 ne_d2_22 ne_W22 ne_W4_22
    ne_D22 ?_ ?_ s hs
  · exact sub_eq_zero.mp key
  · intro t ht
    have e := congrArg₂ (· - ·) (h.1 t ht) (h2.1 t ht)
    rw [rhsC_sub] at e
    change lhsC tA tB r t * (q t - q2 t) = _
    rw [mul_sub]
    exact e
  · intro t ht
    rw [h.2 t ht, h2.2 t ht, sub_self]

end Rhone.Algebra.BlockTwoSymbolic
