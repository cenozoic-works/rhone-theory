/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

public section

/-!
Local stand-in for Comparator (https://github.com/leanprover/comparator), which needs Linux.

Usage, from the repository root, after `lake build` of both modules:

    lake env lean --run tools/palomar/Check.lean Palomar/GaloisObstruction/comparator.json

It reads a Comparator configuration and checks, by comparing the two compiled environments:

1. every name in `theorem_names` is a theorem in both environments with the same universe
   parameters and the same type;
2. every other constant declared in the Challenge module that such a statement depends on
   exists in the Solution environment with an identical declaration, including the proof terms
   of theorems (Comparator compares those too, which covers the proofs Lean generates
   automatically inside definitions);
3. the Solution proofs depend on no axiom outside `permitted_axioms`.

This is a development check. The registry's own verification is authoritative.
-/

open Lean

namespace PalomarCheck

def loadEnv (m : Name) : IO Environment := do
  importModules #[{ module := m }] {} (trustLevel := 1024) (loadExts := false)

/-- Constants declared in the module `m` itself. -/
def declaredIn (env : Environment) (m : Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]! == m
  | none => false

def usedBy (ci : ConstantInfo) (withValue : Bool) : Array Name := Id.run do
  let mut used := ci.type.getUsedConstants
  if withValue then
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstants
    | .thmInfo t => used := used ++ t.value.getUsedConstants
    | .opaqueInfo o => used := used ++ o.value.getUsedConstants
    | _ => pure ()
  match ci with
  | .inductInfo i => used := used ++ i.ctors.toArray
  | .ctorInfo c => used := used.push c.induct
  | .recInfo r => used := used ++ r.all.toArray
  | _ => pure ()
  return used

/-- `true` for the automatically named proof constants `<decl>._proof_<n>` that Lean creates
when it abstracts a proof out of a definition body. Which declaration owns such a constant
depends on the order of elaboration within one file, so a single-file Challenge can refer to
`A._proof_1` where the multi-file library refers to `B._proof_1` with the same statement. -/
def isAuxProof (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

/-- Replace each automatically named proof constant by a constant named after the hash of its
statement, so that two values that differ only in which such constant they cite compare equal. -/
def normAux (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      if isAuxProof n then
        match env.find? n with
        | some ci => some (.const (Name.mkSimple s!"auxProof{hash ci.type}") ls)
        | none => none
      else none
    | _ => none

def sameDecl (a b : ConstantInfo) : Option String :=
  if a.levelParams != b.levelParams then some "universe parameters differ"
  else if a.type != b.type then some "types differ"
  else match a, b with
    | .defnInfo x, .defnInfo y => if x.value != y.value then some "definition values differ" else none
    | .opaqueInfo x, .opaqueInfo y => if x.value != y.value then some "opaque values differ" else none
    | .thmInfo x, .thmInfo y => if x.value != y.value then some "theorem proofs differ" else none
    | .axiomInfo _, .axiomInfo _ => none
    | .inductInfo x, .inductInfo y =>
      if x.ctors != y.ctors || x.numParams != y.numParams || x.numIndices != y.numIndices
        || x.all != y.all then some "inductive shapes differ" else none
    | .ctorInfo x, .ctorInfo y =>
      if x.cidx != y.cidx || x.numParams != y.numParams || x.numFields != y.numFields
        then some "constructor shapes differ" else none
    | .recInfo x, .recInfo y =>
      if x.rules.map (·.rhs) != y.rules.map (·.rhs) then some "recursor rules differ" else none
    | .quotInfo _, .quotInfo _ => none
    | _, _ => some "declaration kinds differ"

partial def axiomsOf (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut axs : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then axs := axs.insert n
    todo := todo ++ usedBy ci true
  return axs

def strArray (j : Json) (k : String) : IO (Array String) := do
  match j.getObjVal? k with
  | .ok (.arr xs) => xs.mapM fun x => IO.ofExcept x.getStr?
  | _ => return #[]

def main (args : List String) : IO UInt32 := do
  let [cfgPath] := args | do IO.eprintln "usage: Check.lean <comparator.json>"; return 2
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
  let chalMod := (← IO.ofExcept (cfg.getObjValAs? String "challenge_module")).toName
  let solMod := (← IO.ofExcept (cfg.getObjValAs? String "solution_module")).toName
  let thms := (← strArray cfg "theorem_names").map String.toName
  let permitted := (← strArray cfg "permitted_axioms").map String.toName
  initSearchPath (← findSysroot)
  let envC ← loadEnv chalMod
  let envS ← loadEnv solMod
  let mut errs : Array String := #[]
  -- 1. the compared theorems
  for t in thms do
    match envC.find? t, envS.find? t with
    | some (.thmInfo a), some (.thmInfo b) =>
      if a.levelParams != b.levelParams then errs := errs.push s!"{t}: universe parameters differ"
      if a.type != b.type then errs := errs.push s!"{t}: statements differ"
      unless declaredIn envC chalMod t do errs := errs.push s!"{t}: not declared in {chalMod}"
    | none, _ => errs := errs.push s!"{t}: missing from Challenge"
    | _, none => errs := errs.push s!"{t}: missing from Solution"
    | _, _ => errs := errs.push s!"{t}: not a theorem in both modules"
  -- 2. the statement closure inside the Challenge module
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[]
  for t in thms do
    if let some ci := envC.find? t then todo := todo ++ usedBy ci false
  let mut nDefs := 0
  let mut warns : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some a := envC.find? n | continue
    match envS.find? n with
    | none =>
      -- an automatically named proof constant need not exist under the same name
      unless isAuxProof n do
        errs := errs.push s!"{n}: used by the Challenge, missing from the Solution environment"
    | some b =>
      if declaredIn envC chalMod n then
        nDefs := nDefs + 1
        if let some msg := (if thms.contains n then none else sameDecl a b) then
          let relaxed : Bool := match a, b with
            | .defnInfo x, .defnInfo y =>
              a.levelParams == b.levelParams && a.type == b.type
                && normAux envC x.value == normAux envS y.value
            | _, _ => false
          if relaxed then
            errs := errs.push s!"{n}: differs only in the names of automatically generated proof constants (Comparator rejects this)"
          else errs := errs.push s!"{n}: {msg}"
        let isThm := match a with | .thmInfo _ => true | _ => false
        todo := todo ++ usedBy a (!isThm || !thms.contains n)
  -- 3. axioms
  let axs := axiomsOf envS thms
  for a in axs.toList do
    unless permitted.contains a do errs := errs.push s!"axiom not permitted: {a}"
  for w in warns do IO.println s!"WARN {w}"
  if errs.isEmpty then
    IO.println s!"OK {cfgPath}: {thms.size} theorems match; {nDefs} Challenge declarations identical in the Solution environment; axioms {axs.toList}"
    return 0
  else
    for e in errs do IO.eprintln s!"FAIL {e}"
    return 1

end PalomarCheck

def main (args : List String) : IO UInt32 := PalomarCheck.main args
