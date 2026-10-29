/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.TableRelease
public import Rhone.Computation.TableFormatRow
/-! # Acceptance of typed table matrices in a single output format -/

@[expose] public section
namespace Rhone.Computation.TableFormatFile

def accepted {KA KB : Nat} (header : TableMatrix.Header KA KB) (n : Nat)
    (policy : TableScalars.Policy) (kind : TableFormatRow.Format)
    (original : List (TableMatrix.Row KA KB))
    (output : List (List TableScalars.Scalar)) : Bool :=
  TableRelease.accepted header n original &&
    decide (List.Forall₂ (fun row values =>
      TableFormatRow.accepted policy kind row.values values = true) original output)

lemma accepted_source {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy} {kind : TableFormatRow.Format}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy kind original output = true) :
    TableRelease.accepted header n original = true := by
  simp only [accepted, Bool.and_eq_true] at h
  exact h.1

lemma accepted_rows {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy} {kind : TableFormatRow.Format}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy kind original output = true) :
    List.Forall₂ (fun row values =>
      TableFormatRow.accepted policy kind row.values values = true) original output := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

lemma accepted_count {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy} {kind : TableFormatRow.Format}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy kind original output = true) :
    output.length = header.grid.length := by
  exact (accepted_rows h).length_eq.symm.trans
    (TableMatrix.accepted_count header original
      (TableRelease.accepted_matrix (accepted_source h)))

lemma accepted_position {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy} {kind : TableFormatRow.Format}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy kind original output = true)
    (i : Nat) (hi : i < original.length) (ho : i < output.length) :
    TableFormatRow.accepted policy kind (original.get ⟨i, hi⟩).values
      (output.get ⟨i, ho⟩) = true :=
  (accepted_rows h).get hi ho

lemma accepted_width {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy} {kind : TableFormatRow.Format}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy kind original output = true)
    (i : Nat) (hi : i < original.length) (ho : i < output.length) :
    (output.get ⟨i, ho⟩).length = header.configs.length := by
  exact (TableFormatRow.accepted_width (accepted_position h i hi ho)).trans
    (TableMatrix.row_width header (original.get ⟨i, hi⟩)
      (TableMatrix.accepted_row header original
        (TableRelease.accepted_matrix (accepted_source h)) _ (List.get_mem _ _)))

lemma exact_file {KA KB : Nat} {header : TableMatrix.Header KA KB} {n : Nat}
    {policy : TableScalars.Policy}
    {original : List (TableMatrix.Row KA KB)} {output : List (List TableScalars.Scalar)}
    (h : accepted header n policy .exact original output = true) :
    output = original.map (fun row => row.values.map
      (fun x => TableScalars.Scalar.exact (RationalWire.strictPrint x))) := by
  have hr := accepted_rows h
  clear h
  induction hr with
  | nil => rfl
  | cons hc ht ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨TableFormatRow.exact_row hc, ih⟩

end Rhone.Computation.TableFormatFile
