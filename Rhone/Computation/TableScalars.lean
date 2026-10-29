/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Scientific
public import Rhone.Computation.NearestLog
public import Rhone.Computation.RationalWirePrintProof
public import Mathlib.Data.List.Forall2
/-! # Scalar acceptance against the original rational values for table formats -/

@[expose] public section
namespace Rhone.Computation.TableScalars

structure Policy where
  logExponentLimit : Int
  logOrderLimit : Nat

inductive Scalar where
  | exact (text : String)
  | binary64 (bits : Nat) (exponent : Int)
  | ldhat (index exponent : Int) (order : Nat)

def accepted (policy : Policy) (x : Rat) : Scalar → Bool
  | .exact text => decide (text = RationalWire.strictPrint x)
  | .binary64 bits e => Binary64Scientific.guardedAccepted x bits e
  | .ldhat k e n =>
    if e < -policy.logExponentLimit ∨ policy.logExponentLimit < e ∨ policy.logOrderLimit < n
    then false else NearestLog.accepted x (1 / 1000) k e n

lemma exact_sound {policy : Policy} {x : Rat} {text : String}
    (h : accepted policy x (.exact text) = true) : RationalWire.decode text = .ok x := by
  simp only [accepted, decide_eq_true_eq] at h
  rw [h]
  exact RationalWire.decode_strictPrint x

lemma binary64_relative {policy : Policy} {x y : Rat} {bits : Nat} {e : Int}
    (h : accepted policy x (.binary64 bits e) = true)
    (hd : Binary64FiniteNearest.decodeFinite bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 :=
  Binary64Scientific.guarded_relative h hd

lemma binary64_nearest {policy : Policy} {x y z : Rat} {bits other : Nat} {e : Int}
    (h : accepted policy x (.binary64 bits e) = true)
    (hd : Binary64FiniteNearest.decodeFinite bits = some y)
    (hz : Binary64FiniteNearest.decodeFinite other = some z) : |y - x| ≤ |z - x| :=
  Binary64Scientific.guarded_nearest h hd hz

lemma ldhat_accepts {policy : Policy} {x : Rat} {k e : Int} {n : Nat}
    (h : accepted policy x (.ldhat k e n) = true) :
    NearestLog.accepted x (1 / 1000) k e n = true := by
  dsimp only [accepted] at h
  split_ifs at h
  exact h

lemma ldhat_error {policy : Policy} {x : Rat} {k e : Int} {n : Nat}
    (h : accepted policy x (.ldhat k e n) = true) :
    |(k : Real) / 1000 - Real.log (x : Real)| < 1 / 2000 := by
  have he := NearestLog.accepted_error (ldhat_accepts h)
  norm_num at he
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using he

lemma ldhat_nearest {policy : Policy} {x : Rat} {k e : Int} {n : Nat}
    (h : accepted policy x (.ldhat k e n) = true) (j : Int) (hj : j ≠ k) :
    |(k : Real) / 1000 - Real.log (x : Real)| <
      |(j : Real) / 1000 - Real.log (x : Real)| := by
  have he := NearestLog.accepted_unique_nearest (ldhat_accepts h) j hj
  norm_num at he
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using he

def rowAccepted (policy : Policy) (original : List Rat) (output : List Scalar) : Bool :=
  decide (List.Forall₂ (fun x scalar => accepted policy x scalar = true) original output)

lemma row_width {policy : Policy} {original : List Rat} {output : List Scalar}
    (h : rowAccepted policy original output = true) : output.length = original.length := by
  simp only [rowAccepted, decide_eq_true_eq] at h
  exact h.length_eq.symm

lemma row_original_pair {policy : Policy} {original : List Rat} {output : List Scalar}
    (h : rowAccepted policy original output = true) (i : Nat)
    (hi : i < original.length) (ho : i < output.length) :
    accepted policy (original.get ⟨i, hi⟩) (output.get ⟨i, ho⟩) = true := by
  simp only [rowAccepted, decide_eq_true_eq] at h
  exact h.get hi ho

end Rhone.Computation.TableScalars
