module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section


elab "clear_aux_proof_cache" : command => do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let ext ← unsafe Lean.Elab.Command.liftCoreM
    (Lean.evalConst (Lean.EnvExtension (Lean.PersistentHashMap Nat Nat))
      (Lean.Name.mkNum `_private.Lean.Meta.Match.Match 0 ++ `Lean.Meta.Match.matcherExt))
  Lean.modifyEnv fun env => ext.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

namespace Rhone.LinearAlgebra.Recursion

open Finset

variable {KA KB : ℕ}

def incf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i + 1)

def decf {ι : Type*} [DecidableEq ι] (f : ι → ℕ) (i : ι) : ι → ℕ :=
  Function.update f i (f i - 1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Config (KA KB : ℕ) where

  a : Fin KA → ℕ

  b : Fin KB → ℕ

  c : Fin KA → Fin KB → ℕ

namespace Config

def sumA (ξ : Config KA KB) : ℕ := ∑ i, ξ.a i

def sumB (ξ : Config KA KB) : ℕ := ∑ j, ξ.b j

def t (ξ : Config KA KB) : ℕ := ∑ i, ∑ j, ξ.c i j

def cRow (ξ : Config KA KB) (i : Fin KA) : ℕ := ∑ j, ξ.c i j

def cCol (ξ : Config KA KB) (j : Fin KB) : ℕ := ∑ i, ξ.c i j

def nA (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.t

def nB (ξ : Config KA KB) : ℕ := ξ.sumB + ξ.t

def n (ξ : Config KA KB) : ℕ := ξ.sumA + ξ.sumB + ξ.t

def incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (incf (m i) j)

def decC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) : Fin KA → Fin KB → ℕ :=
  Function.update m i (decf (m i) j)

def dropA (ξ : Config KA KB) (i : Fin KA) : Config KA KB := ⟨decf ξ.a i, ξ.b, ξ.c⟩

def dropB (ξ : Config KA KB) (j : Fin KB) : Config KA KB := ⟨ξ.a, decf ξ.b j, ξ.c⟩

def dropC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, ξ.b, decC ξ.c i j⟩

def mergeAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨decf ξ.a i, decf ξ.b j, incC ξ.c i j⟩

def killA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, incf ξ.b j, decC ξ.c i j⟩

def killB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, ξ.b, decC ξ.c i j⟩

def split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf ξ.a i, incf ξ.b j, decC ξ.c i j⟩

instance : Zero (Config KA KB) := ⟨⟨fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩

def eA (i : Fin KA) : Config KA KB := ⟨incf (fun _ => 0) i, fun _ => 0, fun _ _ => 0⟩

def eB (j : Fin KB) : Config KA KB := ⟨fun _ => 0, incf (fun _ => 0) j, fun _ _ => 0⟩

def eC (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, incC (fun _ _ => 0) i j⟩

end Config

end Rhone.LinearAlgebra.Recursion

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [CommRing F]

namespace Config

def coalA (ξ : Config KA KB) (i : Fin KA) : ℕ := ξ.a i * (ξ.a i - 1 + 2 * ξ.cRow i)

def coalB (ξ : Config KA KB) (j : Fin KB) : ℕ := ξ.b j * (ξ.b j - 1 + 2 * ξ.cCol j)

def coalC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := ξ.c i j * (ξ.c i j - 1)

def coalAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ℕ := 2 * (ξ.a i * ξ.b j)

end Config

def diag (θA θB ρ : F) (ξ : Config KA KB) : F :=
  ((ξ.n * (ξ.n - 1) : ℕ) : F) + θA * (ξ.nA : ℕ) + θB * (ξ.nB : ℕ) + ρ * (ξ.t : ℕ)

def rhs (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j))
    + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j))
    + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j))
    + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j))
    + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)

structure IsSolution (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) : Prop where

  empty : q 0 = 1

  bdryA : ∀ i, q (Config.eA i) = πA i

  bdryB : ∀ j, q (Config.eB j) = πB j

  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j

  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n → diag θA θB ρ ξ * q ξ = rhs θA θB ρ πA πB q ξ

end Rhone.LinearAlgebra.Recursion

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem exists_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  sorry

noncomputable def q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : Config KA KB → F :=
  Classical.choose (exists_isSolution (πA := πA) (πB := πB) hθA hθB hρ)

end Rhone.LinearAlgebra.Recursion

clear_aux_proof_cache
set_main_module Rhone.Computation.Config

namespace Rhone.Computation

structure Config where
  a : Array Nat
  b : Array Nat
  c : Array Nat
  deriving BEq, Inhabited

def Config.block (c : Config) : Nat × Nat :=
  let t := c.c.foldl (· + ·) 0
  (c.a.foldl (· + ·) t, c.b.foldl (· + ·) t)

def formatCounts (xs : Array Nat) : String :=
  "(" ++ String.intercalate "," (xs.toList.map toString) ++ ")"

def Config.key (c : Config) : String :=
  let rows := (List.range c.a.size).map fun i =>
    formatCounts ((List.range c.b.size).toArray.map fun j => c.c.getD (i*c.b.size+j) 0)
  s!"a={formatCounts c.a};b={formatCounts c.b};c=({String.intercalate "," rows})"
end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.Hierarchy

namespace Rhone.Computation

attribute [-instance] NPow.toPow

structure Params where
  thetaA : Rat
  thetaB : Rat
  rho : Rat
  piA : Array Rat
  piB : Array Rat
  deriving Inhabited

def Params.valid (p : Params) : Bool :=
  p.thetaA > 0 && p.thetaB > 0 && p.rho ≥ 0 &&
  p.piA.size == 2 && p.piB.size == 2 &&
  p.piA.all (· > 0) && p.piB.all (· > 0) &&
  p.piA.foldl (· + ·) 0 == 1 && p.piB.foldl (· + ·) 0 == 1

structure PhiTable where
  nb : Nat
  blocks : Array (Array Rat)
  deriving Inhabited

def PhiTable.get (tab : PhiTable) (i j t : Nat) : Rat :=
  if t > min i j then 0 else (tab.blocks.getD (i*(tab.nb+1)+j) #[]).getD t 0

def source (p : Params) (tab : PhiTable) (i j t : Nat) : Rat := Id.run do
  let ka := p.piA.getD 0 0 * p.piA.getD 1 0
  let kb := p.piB.getD 0 0 * p.piB.getD 1 0
  let ga := p.piA.getD 1 0 - p.piA.getD 0 0
  let gb := p.piB.getD 1 0 - p.piB.getD 0 0

  let terms := #[
    ((i-t)*(i-t-1), ka, i-2, j, t),
    (2*(i-t)*t, ka, i-2, j, t-1),
    ((i-t)*(i+t-1), ga, i-1, j, t),
    ((j-t)*(j-t-1), kb, i, j-2, t),
    (2*(j-t)*t, kb, i, j-2, t-1),
    ((j-t)*(j+t-1), gb, i, j-1, t),
    (t*(t-1), ka*kb, i-2, j-2, t-2),
    (t*(t-1), ka*gb, i-2, j-1, t-2),
    (t*(t-1), ga*kb, i-1, j-2, t-2),
    (t*(t-1), ga*gb, i-1, j-1, t-1)]
  let mut acc : Rat := 0
  for (coef, scale, bi, bj, bt) in terms do
    if coef > 0 then acc := acc + (coef : Rat)*scale*tab.get bi bj bt
  return acc

def rangeProduct (lo hi : Nat) : Nat := Id.run do
  let mut acc := 1
  for u in [lo+1:hi+1] do acc := acc*u
  return acc

def blockDiagonal (p : Params) (i j s : Nat) : Rat :=
  let n := i + j - s
  (n * (n - 1) : Rat) + (i : Rat) * p.thetaA + (j : Rat) * p.thetaB + (s : Rat) * p.rho

def blockBeta (p : Params) (i j s : Nat) : Rat :=
  (2 * s * (i + 1 - s) * (j + 1 - s) : Rat) * p.rho

def forwardContinuants (diag beta : Nat → Rat) (steps : Nat) : Array Rat := Id.run do
  let mut ps : Array Rat := #[0, 1]
  for s in [0:steps] do
    ps := ps.push (diag s * ps.getD (s+1) 0 - beta s * ps.getD s 0)
  return ps

def backwardContinuants (diag beta : Nat → Rat) (m : Nat) : Array Rat := Id.run do
  let mut qs : Array Rat := (Array.replicate (m+3) 0).set! (m+1) 1
  for k in [0:m+1] do
    let s := m-k
    qs := qs.set! s (diag s * qs.getD (s+1) 0 - beta (s+1) * qs.getD (s+2) 0)
  return qs

def blockInverseEntry (p : Params) (i j : Nat) (ps qs : Array Rat) (invDet : Rat)
    (t u : Nat) : Rat :=
  if t ≤ u then
    ((2^(u-t) * rangeProduct (i-u) (i-t) * rangeProduct (j-u) (j-t) : Nat) : Rat) *
      ps.getD (t+1) 0 * qs.getD (u+1) 0 * invDet
  else
    p.rho^(t-u) * (rangeProduct u t : Rat) *
      ps.getD (u+1) 0 * qs.getD (t+1) 0 * invDet

def applyBlockInverse (p : Params) (i j : Nat) (ps qs : Array Rat) (invDet : Rat)
    (rhs : Array Rat) : Array Rat := Id.run do
  let m := min i j
  let mut out := #[]
  for t in [0:m+1] do
    let mut acc : Rat := 0
    for u in [0:m+1] do
      let v := blockInverseEntry p i j ps qs invDet t u
      acc := acc + v * rhs.getD u 0
    out := out.push acc
  return out

def solveBlock (p : Params) (i j : Nat) (rhs : Array Rat) :
    Except String (Array Rat) := do
  let m := min i j
  let diag := blockDiagonal p i j
  let beta := blockBeta p i j

  let ps := forwardContinuants diag beta (m+1)
  let qs := backwardContinuants diag beta m
  let det := ps.getD (m+2) 0
  if det == 0 then throw s!"zero determinant at ({i},{j})"
  if det != qs.getD 0 0 then throw s!"continuants disagree at ({i},{j})"
  return applyBlockInverse p i j ps qs (1 / det) rhs

def hierarchyBlock (p : Params) (tab : PhiTable) (i j : Nat) :
    Except String (Array Rat) :=
  if i == 0 && j == 0 then pure #[1]
  else if i+j == 1 then pure #[0]
  else if i == 1 && j == 1 then
    pure #[source p tab 1 1 0 / (2+p.thetaA+p.thetaB), 0]
  else solveBlock p i j ((List.range (min i j+1)).toArray.map (source p tab i j))

def hierarchyStep (p : Params) (nb degree i : Nat) (tab : PhiTable) :
    Except String PhiTable := do
  if i > degree then return tab
  let j := degree-i
  if j > nb then return tab
  let block ← hierarchyBlock p tab i j
  return {tab with blocks := tab.blocks.set! (i*(nb+1)+j) block}

def phiTable (p : Params) (na nb : Nat) : Except String PhiTable := do
  let mut tab : PhiTable := ⟨nb, Array.replicate ((na+1)*(nb+1)) #[]⟩
  for degree in [0:na+nb+1] do
    for i in [0:na+1] do
      tab ← hierarchyStep p nb degree i tab
  return tab

abbrev Poly := Array ((Nat × Nat × Nat) × Rat)

def mulPoly (a b : Poly) : Poly := Id.run do
  let mut out : Std.HashMap (Nat × Nat × Nat) Rat := {}
  for ((i,j,t), x) in a do
    for ((k,l,u), y) in b do
      let key := (i+k,j+l,t+u)
      let v := out.getD key 0 + x*y
      out := if v == 0 then out.erase key else out.insert key v
  return out.toArray

def powPoly (a : Poly) (n : Nat) : Poly := Id.run do
  let mut out : Poly := #[((0,0,0),1)]
  for _ in [0:n] do out := mulPoly out a
  return out

def polynomial (p : Params) (c : Config) : Poly := Id.run do
  let mut out : Poly := #[((0,0,0),1)]
  for i in [0:2] do
    let sign : Rat := if i == 0 then 1 else -1
    let factor : Poly := #[((0,0,0), p.piA.getD i 0), ((1,0,0), sign)]
    for _ in [0:c.a.getD i 0] do out := mulPoly out factor
  for j in [0:2] do
    let sign : Rat := if j == 0 then 1 else -1
    let factor : Poly := #[((0,0,0), p.piB.getD j 0), ((0,1,0), sign)]
    for _ in [0:c.b.getD j 0] do out := mulPoly out factor
  for i in [0:2] do
    for j in [0:2] do
      let sa : Rat := if i == 0 then 1 else -1
      let sb : Rat := if j == 0 then 1 else -1
      let factor : Poly := #[((0,0,0), p.piA.getD i 0 * p.piB.getD j 0),
        ((1,0,0), sa*p.piB.getD j 0), ((0,1,0), p.piA.getD i 0*sb), ((1,1,1), sa*sb)]
      for _ in [0:c.c.getD (2*i+j) 0] do out := mulPoly out factor
  return out

def assemble (tab : PhiTable) (g : Poly) : Rat :=
  g.foldl (fun acc ((i,j,t), v) => acc + v*tab.get i j t) 0

def q (p : Params) (c : Config) : Except String Rat := do
  if !p.valid then throw "invalid parameters"
  if c.a.size != 2 || c.b.size != 2 || c.c.size != 4 then throw "K out of scope"
  let (na,nb) := c.block
  let tab ← phiTable p na nb
  return assemble tab (polynomial p c)

end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.Closure

namespace Rhone.Computation

def configOfCounts (a0 a1 b0 b1 c00 c01 c10 c11 : Nat) : Config :=
  ⟨#[a0, a1], #[b0, b1], #[c00, c01, c10, c11]⟩

def closureList (n : Nat) : List Config :=
  (List.range (n + 1)).flatMap fun c00 =>
    (List.range (n - c00 + 1)).flatMap fun c01 =>
      (List.range (n - c00 - c01 + 1)).flatMap fun c10 =>
        (List.range (n - c00 - c01 - c10 + 1)).flatMap fun c11 =>
          let linked := c00 + c01 + c10 + c11
          (List.range (n - linked + 1)).flatMap fun a0 =>
            (List.range (n - linked - a0 + 1)).flatMap fun a1 =>
              (List.range (n - linked + 1)).flatMap fun b0 =>
                (List.range (n - linked - b0 + 1)).map fun b1 =>
                  configOfCounts a0 a1 b0 b1 c00 c01 c10 c11

def closure (n : Nat) : Array Config := (closureList n).toArray

end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.CheckerRecursion

namespace Rhone.Computation

def decrementCounts (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.setIfInBounds i (xs.getD i 0 - 1)

def incrementCounts (xs : Array Nat) (i : Nat) : Array Nat :=
  xs.setIfInBounds i (xs.getD i 0 + 1)

def recursionRhsDirect (p : Params) (value : Config → Rat) (s : Config) : Rat :=
  let aTerm := fun i =>
    let a := s.a.getD i 0
    let row := s.c.getD (2 * i) 0 + s.c.getD (2 * i + 1) 0
    let lower := {s with a := decrementCounts s.a i}
    ((a * (a - 1 + 2 * row) : Nat) : Rat) * value lower +
      p.thetaA * p.piA.getD i 0 * (a : Rat) * value lower
  let bTerm := fun j =>
    let b := s.b.getD j 0
    let col := s.c.getD j 0 + s.c.getD (2 + j) 0
    let lower := {s with b := decrementCounts s.b j}
    ((b * (b - 1 + 2 * col) : Nat) : Rat) * value lower +
      p.thetaB * p.piB.getD j 0 * (b : Rat) * value lower
  let linkedTerm := fun i j =>
    let index := 2 * i + j
    let linked := s.c.getD index 0
    let a := s.a.getD i 0
    let b := s.b.getD j 0
    let lower := {s with c := decrementCounts s.c index}
    let joined : Config := ⟨decrementCounts s.a i, decrementCounts s.b j, incrementCounts s.c index⟩
    ((2 * a * b : Nat) : Rat) * value joined +
      ((linked * (linked - 1) : Nat) : Rat) * value lower +
      p.thetaA * p.piA.getD i 0 * (linked : Rat) *
        value {lower with b := incrementCounts s.b j} +
      p.thetaB * p.piB.getD j 0 * (linked : Rat) *
        value {lower with a := incrementCounts s.a i} +
      p.rho * (linked : Rat) *
        value {lower with a := incrementCounts s.a i, b := incrementCounts s.b j}
  aTerm 0 + aTerm 1 + bTerm 0 + bTerm 1 +
    linkedTerm 0 0 + linkedTerm 0 1 + linkedTerm 1 0 + linkedTerm 1 1

end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.CheckerRows

namespace Rhone.Computation

def checkerRowValid (n : Nat) (s : Config) : Bool :=
  s.a.size == 2 && s.b.size == 2 && s.c.size == 4 &&
    s.block.1 ≤ n && s.block.2 ≤ n

def insertTableRows (n : Nat) : List (Config × Rat) → Std.HashMap String Rat →
    Option (Std.HashMap String Rat)
  | [], table => some table
  | (s, v) :: rows, table =>
    if checkerRowValid n s && !table.contains s.key then
      insertTableRows n rows (table.insert s.key v)
    else none

end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.Checker

namespace Rhone.Computation

def recursionRhs (p : Params) (value : Config → Rat) (s : Config) : Rat :=
  recursionRhsDirect p value s

def factorial (n : Nat) : Nat := rangeProduct 0 n

def checkerLineages (s : Config) : Nat :=
  s.a.foldl (· + ·) 0 + s.b.foldl (· + ·) 0 + s.c.foldl (· + ·) 0

def checkerBoundary (p : Params) (s : Config) : Rat :=
  (s.a.getD 0 0 : Rat) * p.piA.getD 0 0 +
  (s.a.getD 1 0 : Rat) * p.piA.getD 1 0 +
  (s.b.getD 0 0 : Rat) * p.piB.getD 0 0 +
  (s.b.getD 1 0 : Rat) * p.piB.getD 1 0 +
  (s.c.getD 0 0 : Rat) * p.piA.getD 0 0 * p.piB.getD 0 0 +
  (s.c.getD 1 0 : Rat) * p.piA.getD 0 0 * p.piB.getD 1 0 +
  (s.c.getD 2 0 : Rat) * p.piA.getD 1 0 * p.piB.getD 0 0 +
  (s.c.getD 3 0 : Rat) * p.piA.getD 1 0 * p.piB.getD 1 0

def checkerDiagonal (p : Params) (s : Config) : Rat :=
  let total := checkerLineages s
  let (na, nb) := s.block
  let t : Nat := s.c.foldl (· + ·) 0
  ((total * (total - 1) : Nat) : Rat) + (na : Rat) * p.thetaA +
    (nb : Rat) * p.thetaB + (t : Rat) * p.rho

def checkerEquation (p : Params) (value : Config → Rat) (s : Config) : Bool :=
  (if checkerLineages s == 1 then value s == checkerBoundary p s else true) &&
    (if checkerLineages s ≥ 2 then
      checkerDiagonal p s * value s == recursionRhs p value s else true)

def checkerNormalization (value : Config → Rat) (states : Array Config) (size : Nat) : Rat :=
  states.foldl (fun mass s =>
    if s.a.all (· == 0) && s.b.all (· == 0) && s.block == (size, size) then
      let denominator := s.c.foldl (fun z count => z * factorial count) 1
      mass + ((factorial size : Rat) / (denominator : Rat)) * value s
    else mass) 0

def checkTable (p : Params) (n : Nat) (entries : Array (Rhone.Computation.Config × Rat)) : Bool :=
  if !p.valid then false else
    match insertTableRows n entries.toList {} with
    | none => false
    | some table =>
      let states := closure n
      let value := fun s => table.getD s.key 0
      entries.size == states.size &&
        states.all (fun s => table.contains s.key) &&
        value (configOfCounts 0 0 0 0 0 0 0 0) == 1 &&
        states.all (checkerEquation p value) &&
        (List.range (n + 1)).all (fun size => checkerNormalization value states size == 1)

end Rhone.Computation

clear_aux_proof_cache
set_main_module Rhone.Computation.CheckerEncodingProof

namespace Rhone.Computation.CheckerEncoding

open LinearAlgebra.Recursion

def decode (s : Rhone.Computation.Config) : Rhone.LinearAlgebra.Recursion.Config 2 2 :=
  ⟨fun i => s.a.getD i.val 0, fun j => s.b.getD j.val 0,
    fun i j => s.c.getD (2 * i.val + j.val) 0⟩

end Rhone.Computation.CheckerEncoding

namespace Rhone.Computation

theorem Params.valid_iff (p : Params) :
    p.valid = true ↔
      0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho ∧
      p.piA.size = 2 ∧ p.piB.size = 2 ∧
      (∀ i : Fin 2, 0 < p.piA.getD i.val 0) ∧
      (∀ i : Fin 2, 0 < p.piB.getD i.val 0) ∧
      (∑ i : Fin 2, p.piA.getD i.val 0) = 1 ∧
      (∑ i : Fin 2, p.piB.getD i.val 0) = 1 := by
  sorry

end Rhone.Computation

set_main_module Palomar.ComputeTwoLocus.Challenge

namespace Rhone.Palomar.ComputeTwoLocus

open Rhone.Computation

theorem q_correct (p : Params) (c : Rhone.Computation.Config) (hp : p.valid = true)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      Rhone.Computation.q p c = .ok (Rhone.LinearAlgebra.Recursion.q
        (πA := fun k : Fin 2 => p.piA.getD k.val 0)
        (πB := fun k : Fin 2 => p.piB.getD k.val 0)
        hθA hθB hρ (CheckerEncoding.decode c)) := by
  sorry

theorem checkTable_sound {p : Params} {n : Nat}
    {entries : Array (Rhone.Computation.Config × Rat)}
    (h : checkTable p n entries = true) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      ∀ entry ∈ entries, entry.2 =
        Rhone.LinearAlgebra.Recursion.q (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
          (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ
          (CheckerEncoding.decode entry.1) := by
  sorry

theorem checkTable_complete (p : Params) (hp : p.valid = true) (n : Nat) :
    checkTable p n ((closure n).map fun s => (s,
      Rhone.LinearAlgebra.Recursion.q
        (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
        (πB := fun (j : Fin 2) => p.piB.getD j.val 0)
        ((Params.valid_iff p).mp hp).1 ((Params.valid_iff p).mp hp).2.1
        ((Params.valid_iff p).mp hp).2.2.1 (CheckerEncoding.decode s))) = true := by
  sorry

end Rhone.Palomar.ComputeTwoLocus
