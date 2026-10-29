/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.GenericRows
public import Mathlib.Data.List.Forall2
public import Rhone.Computation.RationalWirePrintProof
public import Rhone.Computation.QProbabilityProof
/-! # Exact typed table columns and their mapping onto the grid -/

@[expose] public section
namespace Rhone.Computation.TableMatrix
open LinearAlgebra.Recursion

structure Header (KA KB : Nat) where
  thetaA : Rat
  thetaB : Rat
  piA : Fin KA → Rat
  piB : Fin KB → Rat
  bound : Nat
  configs : List (Rhone.LinearAlgebra.Recursion.Config KA KB)
  grid : List Rat

structure Row (KA KB : Nat) where
  rho : Rat
  values : List Rat
  certificate : List (Rhone.LinearAlgebra.Recursion.Config KA KB × Rat)

def rowAccepted {KA KB : Nat} (header : Header KA KB) (row : Row KA KB) : Bool :=
  GenericRows.check header.thetaA header.thetaB row.rho header.piA header.piB
    header.bound row.certificate &&
  header.configs.all (fun ξ => decide (CheckerSpec.InClosure header.bound ξ)) &&
  decide (List.Forall₂ (fun ξ v => GenericRows.value row.certificate ξ = v)
    header.configs row.values)

def accepted {KA KB : Nat} (header : Header KA KB) (rows : List (Row KA KB)) : Bool :=
  decide (header.configs.Nodup ∧ header.grid.Nodup) &&
    decide (rows.map Row.rho = header.grid) && rows.all (rowAccepted header)

lemma row_values_sound {KA KB : Nat} (header : Header KA KB) (row : Row KA KB)
    (h : rowAccepted header row = true) :
    ∃ (hA : 0 < header.thetaA) (hB : 0 < header.thetaB) (hR : 0 ≤ row.rho),
      List.Forall₂ (fun ξ v => v =
        Rhone.LinearAlgebra.Recursion.q (πA := header.piA) (πB := header.piB) hA hB hR ξ)
      header.configs row.values := by
  simp only [rowAccepted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hA, hB, hR, hq, _⟩ := GenericRows.check_sound h.1.1
  refine ⟨hA, hB, hR, ?_⟩
  apply List.forall₂_of_length_eq_of_get h.2.length_eq
  intro i hξ hv
  rw [← h.2.get hξ hv]
  exact hq _ (h.1.2 _ (List.get_mem _ _))

lemma accepted_grid {KA KB : Nat} (header : Header KA KB) (rows : List (Row KA KB))
    (h : accepted header rows = true) : rows.map Row.rho = header.grid := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

lemma row_width {KA KB : Nat} (header : Header KA KB) (row : Row KA KB)
    (h : rowAccepted header row = true) : row.values.length = header.configs.length := by
  simp only [rowAccepted, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.length_eq.symm

lemma accepted_count {KA KB : Nat} (header : Header KA KB) (rows : List (Row KA KB))
    (h : accepted header rows = true) : rows.length = header.grid.length := by
  have he := congrArg List.length (accepted_grid header rows h)
  simpa using he

lemma accepted_row {KA KB : Nat} (header : Header KA KB) (rows : List (Row KA KB))
    (h : accepted header rows = true) (row : Row KA KB) (hr : row ∈ rows) :
    rowAccepted header row = true := by
  simp only [accepted, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 row hr

def exactValues {KA KB : Nat} (row : Row KA KB) : List String :=
  row.values.map RationalWire.strictPrint

lemma exactValues_decode {KA KB : Nat} (row : Row KA KB) :
    (exactValues row).map RationalWire.decode = row.values.map Except.ok := by
  simp [exactValues, List.map_map, RationalWire.decode_strictPrint]

lemma row_probability_sound {KA KB : Nat} (header : Header KA KB) (row : Row KA KB)
    (h : rowAccepted header row = true)
    (hpa : ∀ i, 0 ≤ header.piA i) (hsa : ∑ i, header.piA i = 1)
    (hpb : ∀ j, 0 ≤ header.piB j) (hsb : ∑ j, header.piB j = 1) :
    List.Forall₂ (fun (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) (v : Rat) => (v : Real) =
      Rhone.Coalescent.TwoLocusGenealogy.qProb (header.thetaA : Real) (header.thetaB : Real)
        (row.rho : Real) (fun i => (header.piA i : Real))
        (fun j => (header.piB j : Real)) ξ) header.configs row.values := by
  obtain ⟨hA, hB, hR, hvals⟩ := row_values_sound header row h
  apply hvals.imp
  intro ξ v hv
  rw [hv]
  exact QProbability.rat_q_probability _ _ _ _ _ hA hB hR hpa hsa hpb hsb ξ

lemma accepted_unique {KA KB : Nat} (header : Header KA KB) (rows : List (Row KA KB))
    (h : accepted header rows = true) : header.configs.Nodup ∧ header.grid.Nodup := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

end Rhone.Computation.TableMatrix
