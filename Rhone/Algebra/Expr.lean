/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Expressions, evaluation, and `D`-admissibility -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

inductive Expr (F : Type*) : Type _
  | const : ℚ → Expr F
  | coeff : F → Expr F
  | thA : Expr F
  | thB : Expr F
  | rho : Expr F
  | add : Expr F → Expr F → Expr F
  | mul : Expr F → Expr F → Expr F
  | div : Expr F → Expr F → Expr F

namespace Expr

variable {F : Type*} [Field F]

noncomputable def eval (tA tB tR : RatFunc F) : Expr F → RatFunc F
  | .const q => (q : RatFunc F)
  | .coeff x => algebraMap F (RatFunc F) x
  | .thA => tA
  | .thB => tB
  | .rho => tR
  | .add x y => eval tA tB tR x + eval tA tB tR y
  | .mul x y => eval tA tB tR x * eval tA tB tR y
  | .div x y => eval tA tB tR x / eval tA tB tR y

@[simp] theorem eval_const (tA tB tR : RatFunc F) (q : ℚ) :
    eval tA tB tR (.const q) = (q : RatFunc F) := rfl

@[simp] theorem eval_coeff (tA tB tR : RatFunc F) (x : F) :
    eval tA tB tR (.coeff x) = algebraMap F (RatFunc F) x := rfl

@[simp] theorem eval_add (tA tB tR : RatFunc F) (x y : Expr F) :
    eval tA tB tR (.add x y) = eval tA tB tR x + eval tA tB tR y := rfl

@[simp] theorem eval_mul (tA tB tR : RatFunc F) (x y : Expr F) :
    eval tA tB tR (.mul x y) = eval tA tB tR x * eval tA tB tR y := rfl

@[simp] theorem eval_div (tA tB tR : RatFunc F) (x y : Expr F) :
    eval tA tB tR (.div x y) = eval tA tB tR x / eval tA tB tR y := rfl

def sumList : List (Expr F) → Expr F
  | [] => .const 0
  | e :: t => .add e (sumList t)

def prodList : List (Expr F) → Expr F
  | [] => .const 1
  | e :: t => .mul e (prodList t)

@[simp] theorem eval_sumList (tA tB tR : RatFunc F) :
    ∀ l : List (Expr F), eval tA tB tR (sumList l) = (l.map (eval tA tB tR)).sum
  | [] => by simp [sumList]
  | e :: t => by simp [sumList, eval_sumList tA tB tR t]

@[simp] theorem eval_prodList (tA tB tR : RatFunc F) :
    ∀ l : List (Expr F), eval tA tB tR (prodList l) = (l.map (eval tA tB tR)).prod
  | [] => by simp [prodList]
  | e :: t => by simp [prodList, eval_prodList tA tB tR t]

noncomputable def finsetSum {ι : Type*} (s : Finset ι) (f : ι → Expr F) : Expr F :=
  sumList (s.toList.map f)

noncomputable def finsetProd {ι : Type*} (s : Finset ι) (f : ι → Expr F) : Expr F :=
  prodList (s.toList.map f)

theorem eval_finsetSum {ι : Type*} (tA tB tR : RatFunc F) (s : Finset ι) (f : ι → Expr F) :
    eval tA tB tR (finsetSum s f) = ∑ i ∈ s, eval tA tB tR (f i) := by
  rw [finsetSum, eval_sumList, List.map_map]
  exact s.sum_map_toList _

theorem eval_finsetProd {ι : Type*} (tA tB tR : RatFunc F) (s : Finset ι) (f : ι → Expr F) :
    eval tA tB tR (finsetProd s f) = ∏ i ∈ s, eval tA tB tR (f i) := by
  rw [finsetProd, eval_prodList, List.map_map]
  exact s.prod_map_toList _

end Expr

inductive DAdm {F : Type*} [Field F] (tA tB tR : RatFunc F) (D : ℕ) : Expr F → Prop
  | const (q : ℚ) : DAdm tA tB tR D (.const q)
  | coeff (x : F) : DAdm tA tB tR D (.coeff x)
  | thA : DAdm tA tB tR D .thA
  | thB : DAdm tA tB tR D .thB
  | rho : DAdm tA tB tR D .rho
  | add {x y : Expr F} : DAdm tA tB tR D x → DAdm tA tB tR D y → DAdm tA tB tR D (.add x y)
  | mul {x y : Expr F} : DAdm tA tB tR D x → DAdm tA tB tR D y → DAdm tA tB tR D (.mul x y)
  | div {x g : Expr F} (hx : DAdm tA tB tR D x) (hg : DAdm tA tB tR D g)
      (p : Polynomial F) (hp : p ≠ 0) (hdeg : p.natDegree ≤ D)
      (hval : Expr.eval tA tB tR g = algebraMap (Polynomial F) (RatFunc F) p) :
      DAdm tA tB tR D (.div x g)

namespace DAdm

variable {F : Type*} [Field F] {tA tB tR : RatFunc F} {D : ℕ}

theorem sumList : ∀ {l : List (Expr F)}, (∀ e ∈ l, DAdm tA tB tR D e) →
    DAdm tA tB tR D (Expr.sumList l)
  | [], _ => .const 0
  | e :: t, h => .add (h e (by simp)) (sumList fun x hx => h x (by simp [hx]))

theorem prodList : ∀ {l : List (Expr F)}, (∀ e ∈ l, DAdm tA tB tR D e) →
    DAdm tA tB tR D (Expr.prodList l)
  | [], _ => .const 1
  | e :: t, h => .mul (h e (by simp)) (prodList fun x hx => h x (by simp [hx]))

theorem finsetSum {ι : Type*} {s : Finset ι} {f : ι → Expr F}
    (h : ∀ i ∈ s, DAdm tA tB tR D (f i)) : DAdm tA tB tR D (Expr.finsetSum s f) :=
  sumList (by simpa using fun i hi => h i (Finset.mem_toList.mp hi))

theorem finsetProd {ι : Type*} {s : Finset ι} {f : ι → Expr F}
    (h : ∀ i ∈ s, DAdm tA tB tR D (f i)) : DAdm tA tB tR D (Expr.finsetProd s f) :=
  prodList (by simpa using fun i hi => h i (Finset.mem_toList.mp hi))

end DAdm

end Rhone.Algebra
