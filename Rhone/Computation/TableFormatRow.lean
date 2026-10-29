/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.TableScalars
/-! # Uniform-format table rows checked against the original values -/

@[expose] public section
namespace Rhone.Computation.TableFormatRow

inductive Format where
  | exact
  | binary64
  | ldhat
  deriving DecidableEq

def format : TableScalars.Scalar → Format
  | .exact _ => .exact
  | .binary64 _ _ => .binary64
  | .ldhat _ _ _ => .ldhat

def accepted (policy : TableScalars.Policy) (kind : Format)
    (original : List Rat) (output : List TableScalars.Scalar) : Bool :=
  TableScalars.rowAccepted policy original output &&
    output.all (fun scalar => decide (format scalar = kind))

lemma accepted_scalars {policy : TableScalars.Policy} {kind : Format}
    {original : List Rat} {output : List TableScalars.Scalar}
    (h : accepted policy kind original output = true) :
    TableScalars.rowAccepted policy original output = true := by
  simp only [accepted, Bool.and_eq_true] at h
  exact h.1

lemma accepted_format {policy : TableScalars.Policy} {kind : Format}
    {original : List Rat} {output : List TableScalars.Scalar}
    (h : accepted policy kind original output = true)
    (scalar : TableScalars.Scalar) (hs : scalar ∈ output) : format scalar = kind := by
  simp only [accepted, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 scalar hs

lemma accepted_width {policy : TableScalars.Policy} {kind : Format}
    {original : List Rat} {output : List TableScalars.Scalar}
    (h : accepted policy kind original output = true) : output.length = original.length :=
  TableScalars.row_width (accepted_scalars h)

lemma exact_row {policy : TableScalars.Policy}
    {original : List Rat} {output : List TableScalars.Scalar}
    (h : accepted policy .exact original output = true) :
    output = original.map (fun x => TableScalars.Scalar.exact (RationalWire.strictPrint x)) := by
  have hv := accepted_scalars h
  simp only [TableScalars.rowAccepted, decide_eq_true_eq] at hv
  have hf : ∀ scalar ∈ output, format scalar = .exact := accepted_format h
  clear h
  induction hv with
  | nil => rfl
  | @cons x scalar xs ys hc ht ih =>
    have hhead := hf scalar (by simp)
    cases scalar with
    | exact text =>
      simp only [TableScalars.accepted, decide_eq_true_eq] at hc
      subst text
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact ih (fun s hs => hf s (by simp [hs]))
    | binary64 bits e => simp [format] at hhead
    | ldhat k e n => simp [format] at hhead

end Rhone.Computation.TableFormatRow
