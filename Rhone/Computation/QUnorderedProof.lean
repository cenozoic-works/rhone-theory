/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.QUnordered
public import Rhone.Computation.QWireProof
public import Mathlib.Data.Nat.Choose.Multinomial

/-! # Meaning of the unordered q reader -/

@[expose] public section
namespace Rhone.Computation.QUnordered
open Lean

noncomputable def unorderedProb (thetaA thetaB rho : Real) (piA piB : Fin 2 → Real)
    (c : Config) : Real :=
  (Nat.multinomial Finset.univ (fun k : Fin 4 => c.c.getD k.val 0) : Real) *
    Rhone.Coalescent.TwoLocusGenealogy.qProb thetaA thetaB rho piA piB (CheckerEncoding.decode c)

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => cases h
  | ok a => exact step a rfl h

theorem factorial_eq (n : Nat) : factorial n = n.factorial := by
  unfold factorial
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [Nat.factorial_succ, Nat.mul_comm]

theorem factor_eq (c : Config) (h : c.c.size = 4) :
    factor c = Nat.multinomial Finset.univ (fun k : Fin 4 => c.c.getD k.val 0) := by
  rcases c with ⟨a, b, ⟨l⟩⟩
  simp only [List.size_toArray] at h
  match l, h with
  | [x0, x1, x2, x3], _ =>
    simp [factor, factorial_eq, Nat.multinomial, Fin.sum_univ_four, Fin.prod_univ_four,
      Array.getD, Nat.mul_assoc, Nat.add_assoc]

theorem requestAst_probability (doc out : Json) (hok : requestAst doc = .ok out) :
    ∃ (r : QWire.Request) (v : Rat), decode doc = .ok r ∧ out = result v ∧
      r.params.valid = true ∧ r.config.a.size = 2 ∧ r.config.b.size = 2 ∧
      r.config.c.size = 4 ∧ fullyTyped r.config = true ∧
      (v : Real) = unorderedProb
        (r.params.thetaA : Real) (r.params.thetaB : Real) (r.params.rho : Real)
        (fun i : Fin 2 => (r.params.piA.getD i.val 0 : Real))
        (fun j : Fin 2 => (r.params.piB.getD j.val 0 : Real)) r.config := by
  unfold requestAst at hok
  refine of_bind_ok hok fun r hr hok => ?_
  refine of_bind_ok hok fun v hv hok => ?_
  cases hok
  unfold evaluate at hv
  split at hv
  · cases hv
  rename_i ht
  simp only [Bool.not_eq_true'] at ht
  have ht' : fullyTyped r.config = true := by simpa using ht
  refine of_bind_ok hv fun w hw hv => ?_
  cases hv
  obtain ⟨hp, ha, hb, hc⟩ := QWire.q_success_domain r.params r.config w hw
  obtain ⟨w', hw', hprob⟩ := QProbability.compute_q_probability r.params r.config hp ha hb hc
  have hval : w = w' := Except.ok.inj (hw.symm.trans hw')
  subst hval
  refine ⟨r, _, hr, rfl, hp, ha, hb, hc, ht', ?_⟩
  rw [unorderedProb, ← factor_eq _ hc, ← hprob]
  push_cast
  rfl

end Rhone.Computation.QUnordered
