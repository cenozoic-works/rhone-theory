/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-! # Finite event model for the two-locus island ARG -/

@[expose] public section

namespace Rhone.MarkovChain.Identifiability

abbrev Shape := List (List Nat)
abbrev State := Fin 16

def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs

def sortNat : List Nat → List Nat
  | [] => []
  | a :: as => insertNat a (sortNat as)

def listLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then listLE as bs else false

def insertGroup (a : List Nat) : Shape → Shape
  | [] => [a]
  | b :: bs => if listLE a b then a :: b :: bs else b :: insertGroup a bs

def sortGroups : Shape → Shape
  | [] => []
  | a :: as => insertGroup a (sortGroups as)

def canonical (s : Shape) : Shape :=
  sortGroups ((s.filter (fun g => !g.isEmpty)).map sortNat)

def carriesA (a : Nat) : Bool := a == 1 || a == 3
def carriesB (a : Nat) : Bool := a == 2 || a == 3
def overlap (a b : Nat) : Nat :=
  (if carriesA a && carriesA b then 1 else 0) +
  (if carriesB a && carriesB b then 2 else 0)
def unionMask (a b : Nat) : Nat :=
  (if carriesA a || carriesA b then 1 else 0) +
  (if carriesB a || carriesB b then 2 else 0)

def shape : State → Shape :=
  ![[[3, 3]],
    [[3], [3]],
    [[1, 2, 3]],
    [[1], [2, 3]],
    [[1, 2], [3]],
    [[1, 3], [2]],
    [[1], [2], [3]],
    [[1, 1, 2, 2]],
    [[1], [1, 2, 2]],
    [[1, 1], [2, 2]],
    [[1, 1, 2], [2]],
    [[1, 2], [1, 2]],
    [[1], [1], [2, 2]],
    [[1], [1, 2], [2]],
    [[1, 1], [2], [2]],
    [[1], [1], [2], [2]]]

def occupiedEvents (s : Shape) : List Shape :=
  (List.range s.length).flatMap fun i =>
    (List.range (s.getD i []).length).flatMap fun p =>
      ((List.range s.length).filter (fun j => j != i)).map fun j =>
        canonical ((s.modify i (fun g => g.eraseIdx p)).modify j
          (fun g => (s.getD i []).getD p 0 :: g))

def emptyEvents (s : Shape) : List Shape :=
  (List.range s.length).flatMap fun i =>
    (List.range (s.getD i []).length).map fun p =>
      canonical ((s.modify i (fun g => g.eraseIdx p)) ++ [[(s.getD i []).getD p 0]])

def recombinationEvents (s : Shape) : List Shape :=
  (List.range s.length).flatMap fun i =>
    ((List.range (s.getD i []).length).filter
      (fun p => (s.getD i []).getD p 0 == 3)).map fun p =>
        canonical (s.modify i (fun g => 1 :: 2 :: g.eraseIdx p))

def mergerEvents (s : Shape) : List (Nat × Shape) :=
  (List.range s.length).flatMap fun i =>
    (List.range (s.getD i []).length).flatMap fun p =>
      ((List.range (s.getD i []).length).filter (fun q => decide (p < q))).map fun q =>
        let a := (s.getD i []).getD p 0
        let b := (s.getD i []).getD q 0
        (overlap a b, canonical (s.modify i
          (fun g => unionMask a b :: (g.eraseIdx q).eraseIdx p)))

def coalescenceEvents (s : Shape) : List Shape :=
  ((mergerEvents s).filter (fun e => e.1 == 0)).map Prod.snd

def killedCount (s : Shape) : Nat :=
  (mergerEvents s).countP (fun e => e.1 != 0)

def rateCount (events : Shape → List Shape) (kill : Shape → Nat)
    (i j : State) : Int :=
  ((events (shape i)).countP (fun s => s == shape j) : Int) -
    if i = j then ((events (shape i)).length + kill (shape i) : Nat) else 0

def bTogether (s : Shape) : Bool :=
  s.any (fun g => g.countP (fun a => carriesB a) == 2)

def firstACount (s : Shape) : Nat :=
  (mergerEvents s).countP (fun e => e.1 == 1)

def firstAThenBCount (s : Shape) : Nat :=
  (mergerEvents s).countP (fun e => e.1 == 1 && bTogether e.2)

def occupiedTable : Matrix State State Int :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, -3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, -3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 2, 2, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, -4, 1, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -4, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, -4, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, -4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, -8, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 1, -6, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 4, -8, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 2, -12]]

def emptyTable : Matrix State State Int :=
  ![![-2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -3, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -4, 2, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 1, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 2, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 2, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def recombinationTable : Matrix State State Int :=
  ![![-2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def coalescenceTable : Matrix State State Int :=
  ![![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def occupiedDemes : State → Nat := ![1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3, 3, 3, 4]

def firstATable : State → Nat := ![0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0]

def firstAThenBTable : State → Nat := ![0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]

set_option maxSynthPendingDepth 16 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem event_tables_checked :
    (∀ i j, rateCount occupiedEvents (fun _ => 0) i j = occupiedTable i j) ∧
    (∀ i j, rateCount emptyEvents (fun _ => 0) i j = emptyTable i j) ∧
    (∀ i j, rateCount recombinationEvents (fun _ => 0) i j = recombinationTable i j) ∧
    (∀ i j, rateCount coalescenceEvents killedCount i j = coalescenceTable i j) ∧
    (∀ i, (shape i).length = occupiedDemes i) ∧
    (∀ i, firstACount (shape i) = firstATable i) ∧
    (∀ i, firstAThenBCount (shape i) = firstAThenBTable i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro i
    fin_cases i <;> decide

end Rhone.MarkovChain.Identifiability
