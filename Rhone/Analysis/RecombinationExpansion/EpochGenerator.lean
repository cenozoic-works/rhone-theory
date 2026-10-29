/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.Operator
public import Rhone.LinearAlgebra.Recursion.Exist
public import Mathlib.Tactic.FieldSimp

/-! # The epoch generator on whole configurations is a rescaling with the same solutions -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def diagCoal (ξ : Config KA KB) : F := ((ξ.n * (ξ.n - 1) : ℕ) : F)

def rhsCoal (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))

def rhsMutA (πA : Fin KA → F) (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
    + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j))

def rhsMutB (πB : Fin KB → F) (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
    + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j))

def rhsRec (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

theorem diag_eq_classes (ξ : Config KA KB) :
    diag θA θB ρ ξ
      = diagCoal ξ + θA * ((ξ.nA : ℕ) : F) + θB * ((ξ.nB : ℕ) : F)
        + ρ * ((ξ.t : ℕ) : F) := rfl

theorem rhs_eq_classes (q : Config KA KB → F) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB q ξ
      = rhsCoal q ξ + θA * rhsMutA πA q ξ + θB * rhsMutB πB q ξ + ρ * rhsRec q ξ := rfl

section Field

variable {F : Type*} [Field F] {lam θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

noncomputable def diagEpoch (lam θA θB ρ : F) (ξ : Config KA KB) : F :=
  (1 / lam) * diagCoal ξ + θA * ((ξ.nA : ℕ) : F) + θB * ((ξ.nB : ℕ) : F)
    + ρ * ((ξ.t : ℕ) : F)

noncomputable def rhsEpoch (lam θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  (1 / lam) * rhsCoal q ξ + θA * rhsMutA πA q ξ + θB * rhsMutB πB q ξ + ρ * rhsRec q ξ

theorem diagEpoch_eq_smul (hlam : lam ≠ 0) (ξ : Config KA KB) :
    diagEpoch lam θA θB ρ ξ = (1 / lam) * diag (lam * θA) (lam * θB) (lam * ρ) ξ := by
  rw [diagEpoch, diag_eq_classes]
  field_simp

theorem rhsEpoch_eq_smul (hlam : lam ≠ 0) (q : Config KA KB → F) (ξ : Config KA KB) :
    rhsEpoch lam θA θB ρ πA πB q ξ
      = (1 / lam) * rhs (lam * θA) (lam * θB) (lam * ρ) πA πB q ξ := by
  rw [rhsEpoch, rhs_eq_classes]
  field_simp

noncomputable def Aepoch (lam θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) (ξ : Config KA KB) : F :=
  diagEpoch lam θA θB ρ ξ * q ξ - rhsEpoch lam θA θB ρ πA πB q ξ

theorem Aepoch_eq_smul (hlam : lam ≠ 0) (q : Config KA KB → F) (ξ : Config KA KB) :
    Aepoch lam θA θB ρ πA πB q ξ
      = (1 / lam) * Lop (lam * θA) (lam * θB) (lam * ρ) πA πB q ξ := by
  rw [Aepoch, diagEpoch_eq_smul hlam, rhsEpoch_eq_smul hlam, Lop]
  ring

structure IsSolutionEpoch (lam θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = πA i
  bdryB : ∀ j, q (Config.eB j) = πB j
  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
    diagEpoch lam θA θB ρ ξ * q ξ = rhsEpoch lam θA θB ρ πA πB q ξ

theorem isSolutionEpoch_iff (hlam : lam ≠ 0) (q : Config KA KB → F) :
    IsSolutionEpoch lam θA θB ρ πA πB q
      ↔ IsSolution (lam * θA) (lam * θB) (lam * ρ) πA πB q := by
  have hstep : ∀ ξ : Config KA KB,
      (diagEpoch lam θA θB ρ ξ * q ξ = rhsEpoch lam θA θB ρ πA πB q ξ)
        ↔ (diag (lam * θA) (lam * θB) (lam * ρ) ξ * q ξ
            = rhs (lam * θA) (lam * θB) (lam * ρ) πA πB q ξ) := by
    intro ξ
    rw [diagEpoch_eq_smul hlam, rhsEpoch_eq_smul hlam, mul_assoc]
    constructor
    · exact fun h => mul_left_cancel₀ (one_div_ne_zero hlam) h
    · exact fun h => by rw [h]
  constructor
  · intro h
    exact ⟨h.empty, h.bdryA, h.bdryB, h.bdryC, fun ξ hn => (hstep ξ).1 (h.recursion ξ hn)⟩
  · intro h
    exact ⟨h.empty, h.bdryA, h.bdryB, h.bdryC, fun ξ hn => (hstep ξ).2 (h.recursion ξ hn)⟩

end Field

section Ordered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {lam θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem epoch_eq_q (hlam : 0 < lam) (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolutionEpoch lam θA θB ρ πA πB q) :
    q = LinearAlgebra.Recursion.q (KA := KA) (KB := KB) (πA := πA) (πB := πB)
      (mul_pos hlam hθA) (mul_pos hlam hθB) (mul_nonneg (le_of_lt hlam) hρ) := by
  have h := (isSolutionEpoch_iff hlam.ne' q).1 hq
  exact q_unique _ _ _ h

theorem exists_isSolutionEpoch (hlam : 0 < lam) (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (πA : Fin KA → F) (πB : Fin KB → F) :
    ∃ q : Config KA KB → F, IsSolutionEpoch lam θA θB ρ πA πB q :=
  ⟨_, (isSolutionEpoch_iff hlam.ne' _).2
    (q_isSolution (πA := πA) (πB := πB) (mul_pos hlam hθA) (mul_pos hlam hθB)
      (mul_nonneg (le_of_lt hlam) hρ))⟩

end Ordered

end Rhone.Analysis.RecombinationExpansion
