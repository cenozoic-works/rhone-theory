/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.TableMatrix
/-! # Model-domain guard for complete typed matrices -/

@[expose] public section
namespace Rhone.Computation.TableRelease

def sourceDomain {KA KB : Nat} (h : TableMatrix.Header KA KB) (n : Nat) : Prop :=
  1 ≤ KA ∧ KA ≤ 255 ∧ 1 ≤ KB ∧ KB ≤ 255 ∧ 0 < n ∧ n ≤ 65535 ∧ h.bound = n ∧
  h.configs ≠ [] ∧ h.grid ≠ [] ∧ 0 < h.thetaA ∧ 0 < h.thetaB ∧
  (∀ i, 0 < h.piA i) ∧ (∑ i, h.piA i) = 1 ∧
  (∀ j, 0 < h.piB j) ∧ (∑ j, h.piB j) = 1 ∧
  (∀ ξ ∈ h.configs, ξ.a = 0 ∧ ξ.b = 0 ∧ ξ.n = n) ∧
  ∀ rho ∈ h.grid, 0 ≤ rho

instance {KA KB : Nat} (h : TableMatrix.Header KA KB) (n : Nat) :
    Decidable (sourceDomain h n) := by unfold sourceDomain; infer_instance

def accepted {KA KB : Nat} (h : TableMatrix.Header KA KB) (n : Nat)
    (rows : List (TableMatrix.Row KA KB)) : Bool :=
  decide (sourceDomain h n) && TableMatrix.accepted h rows

lemma accepted_domain {KA KB : Nat} {h : TableMatrix.Header KA KB} {n : Nat}
    {rows : List (TableMatrix.Row KA KB)} (ha : accepted h n rows = true) :
    sourceDomain h n := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.1

lemma accepted_matrix {KA KB : Nat} {h : TableMatrix.Header KA KB} {n : Nat}
    {rows : List (TableMatrix.Row KA KB)} (ha : accepted h n rows = true) :
    TableMatrix.accepted h rows = true := by
  simp only [accepted, Bool.and_eq_true] at ha
  exact ha.2

lemma accepted_probability {KA KB : Nat} {h : TableMatrix.Header KA KB} {n : Nat}
    {rows : List (TableMatrix.Row KA KB)} (ha : accepted h n rows = true)
    (row : TableMatrix.Row KA KB) (hr : row ∈ rows) :
    List.Forall₂ (fun (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) (v : Rat) =>
      (v : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb (h.thetaA : Real) (h.thetaB : Real)
        (row.rho : Real) (fun i => (h.piA i : Real)) (fun j => (h.piB j : Real)) ξ)
      h.configs row.values := by
  have hd := accepted_domain ha
  rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, hpa, hsa, hpb, hsb, _, _⟩
  exact TableMatrix.row_probability_sound h row
    (TableMatrix.accepted_row h rows (accepted_matrix ha) row hr)
    (fun i => (hpa i).le) hsa (fun j => (hpb j).le) hsb

lemma empty_grid_refuses {KA KB : Nat} (h : TableMatrix.Header KA KB) (n : Nat)
    (rows : List (TableMatrix.Row KA KB)) (he : h.grid = []) : accepted h n rows = false := by
  simp [accepted, sourceDomain, he]

lemma empty_columns_refuses {KA KB : Nat} (h : TableMatrix.Header KA KB) (n : Nat)
    (rows : List (TableMatrix.Row KA KB)) (he : h.configs = []) : accepted h n rows = false := by
  simp [accepted, sourceDomain, he]

end Rhone.Computation.TableRelease
