/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.TableBytes
public import Rhone.Computation.GenericArtifactProof

/-! # Meaning of acceptance of the exact table bytes reader -/

@[expose] public section
namespace Rhone.Computation.TableBytes
open Lean GenericArtifact
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => cases h
  | ok a => exact step a rfl h

theorem decode_table {doc : Json} {r : Request} (hd : decode doc = .ok r) :
    ∃ table : Json, Json.parse r.text = .ok table ∧ decodeHeader table = .ok r.header := by
  unfold decode at hd
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  split at hd
  · cases hd
  refine of_bind_ok hd fun text _ hd => ?_
  refine of_bind_ok hd fun table ht hd => ?_
  refine of_bind_ok hd fun header hh hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  cases hd
  exact ⟨table, ht, hh⟩

theorem decode_accepted {doc : Json} {r : Request} (hd : decode doc = .ok r)
    (ha : r.accepted = true) :
    render r.header r.values r.info = some r.text ∧
      (∃ table : Json, Json.parse r.text = .ok table ∧ decodeHeader table = .ok r.header) ∧
      ∀ g c, g < r.header.grid.size → c < r.header.keys.size →
        ∃ config : Config,
          parseConfig (r.header.keys.getD c "") r.header.piA.size r.header.piB.size =
            .ok config ∧
          ((r.values.getD g #[]).getD c 0 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
            (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
            (fun i => (GenericWire.pi r.header.piA i : Real))
            (fun j => (GenericWire.pi r.header.piB j : Real))
            (GenericWire.toSpec r.header.piA.size r.header.piB.size config) := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨hart, hbytes⟩ := ha
  obtain ⟨table, hp, hh⟩ := decode_table hd
  refine ⟨hbytes, ⟨table, hp, hh⟩, fun g c hg hc => ?_⟩
  exact header_accepted_probability (schema := "rhone-table-v3") (allowed := tableFields)
    (r := r.artifact) hh hart hg hc

end Rhone.Computation.TableBytes
