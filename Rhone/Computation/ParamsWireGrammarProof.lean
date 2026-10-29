/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsWireAcceptanceProof
public import Rhone.Computation.RationalWireGrammarProof

/-! # Parameter AST acceptance in the fixed ASCII grammar -/

@[expose] public section
namespace Rhone.Computation.ParamsWire
open Lean

def HasRationalSyntaxField (doc : Json) (name : String) : Prop :=
  ∃ s, doc.getObjVal? name = .ok (.str s) ∧
    ∃ r, RationalWire.RationalSyntax s.toList r

def HasFrequencySyntaxField (doc : Json) (name : String) : Prop :=
  ∃ xs : Array Json, doc.getObjVal? name = .ok (.arr xs) ∧
    ∀ v ∈ xs, ∃ s r, v = .str s ∧ RationalWire.RationalSyntax s.toList r

theorem decode_success_syntax_iff (doc : Json) :
    (∃ p, decode doc = .ok p) ↔
      HasRationalSyntaxField doc "theta_a" ∧ HasRationalSyntaxField doc "theta_b" ∧
      HasRationalSyntaxField doc "rho" ∧ HasFrequencySyntaxField doc "pi_a" ∧
      HasFrequencySyntaxField doc "pi_b" := by
  simpa only [HasRationalField, HasFrequencyField, HasRationalSyntaxField,
    HasFrequencySyntaxField, RationalWire.decode_eq_ok_iff] using decode_success_iff doc

end Rhone.Computation.ParamsWire
