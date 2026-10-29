module

public import Rhone.Computation.CorrectnessProof
public import Rhone.Computation.CheckerSoundnessProof
public import Rhone.Computation.CheckerCompletenessProof

@[expose] public section

namespace Rhone.Palomar.ComputeTwoLocus

open Rhone.Computation

theorem q_correct (p : Params) (c : Rhone.Computation.Config) (hp : p.valid = true)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      Rhone.Computation.q p c = .ok (Rhone.LinearAlgebra.Recursion.q
        (πA := fun k : Fin 2 => p.piA.getD k.val 0)
        (πB := fun k : Fin 2 => p.piB.getD k.val 0)
        hθA hθB hρ (CheckerEncoding.decode c)) :=
  Rhone.Computation.q_correct p c hp ha hb hc

theorem checkTable_sound {p : Params} {n : Nat}
    {entries : Array (Rhone.Computation.Config × Rat)}
    (h : checkTable p n entries = true) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      ∀ entry ∈ entries, entry.2 =
        Rhone.LinearAlgebra.Recursion.q (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
          (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ
          (CheckerEncoding.decode entry.1) :=
  Rhone.Computation.checkTable_sound h

theorem checkTable_complete (p : Params) (hp : p.valid = true) (n : Nat) :
    checkTable p n ((closure n).map fun s => (s,
      Rhone.LinearAlgebra.Recursion.q
        (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
        (πB := fun (j : Fin 2) => p.piB.getD j.val 0)
        ((Params.valid_iff p).mp hp).1 ((Params.valid_iff p).mp hp).2.1
        ((Params.valid_iff p).mp hp).2.2.1 (CheckerEncoding.decode s))) = true :=
  Rhone.Computation.checkTable_complete p hp n

end Rhone.Palomar.ComputeTwoLocus
