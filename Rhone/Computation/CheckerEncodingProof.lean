/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Checker
public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Biallelic configuration representation -/

@[expose] public section

namespace Rhone.Computation.CheckerEncoding

open LinearAlgebra.Recursion

def encode (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) : Rhone.Computation.Config :=
  ⟨#[ξ.a 0, ξ.a 1], #[ξ.b 0, ξ.b 1], #[ξ.c 0 0, ξ.c 0 1, ξ.c 1 0, ξ.c 1 1]⟩

def decode (s : Rhone.Computation.Config) : Rhone.LinearAlgebra.Recursion.Config 2 2 :=
  ⟨fun i => s.a.getD i.val 0, fun j => s.b.getD j.val 0,
    fun i j => s.c.getD (2 * i.val + j.val) 0⟩

@[simp] theorem encode_sizes (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).a.size = 2 ∧ (encode ξ).b.size = 2 ∧ (encode ξ).c.size = 4 := by
  simp [encode]

@[simp] theorem encode_a (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i : Fin 2) :
    (encode ξ).a.getD i.val 0 = ξ.a i := by
  fin_cases i <;> rfl

@[simp] theorem encode_b (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (j : Fin 2) :
    (encode ξ).b.getD j.val 0 = ξ.b j := by
  fin_cases j <;> rfl

@[simp] theorem encode_c (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    (encode ξ).c.getD (2 * i.val + j.val) 0 = ξ.c i j := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem decode_encode (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    decode (encode ξ) = ξ := by
  apply Rhone.LinearAlgebra.Recursion.Config.ext
  · funext i
    exact encode_a ξ i
  · funext j
    exact encode_b ξ j
  · funext i j
    exact encode_c ξ i j

private theorem array_two (xs : Array Nat) (h : xs.size = 2) :
    #[xs.getD 0 0, xs.getD 1 0] = xs := by
  apply Array.ext (by simpa using h.symm)
  intro i hi _
  have : i < 2 := by simpa using hi
  interval_cases i <;> simp [h]

private theorem array_four (xs : Array Nat) (h : xs.size = 4) :
    #[xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0] = xs := by
  apply Array.ext (by simpa using h.symm)
  intro i hi _
  have : i < 4 := by simpa using hi
  interval_cases i <;> simp [h]

@[simp] theorem encode_decode (s : Rhone.Computation.Config)
    (ha : s.a.size = 2) (hb : s.b.size = 2) (hc : s.c.size = 4) :
    encode (decode s) = s := by
  cases s with
  | mk a b c =>
    change Rhone.Computation.Config.mk #[a.getD 0 0, a.getD 1 0]
      #[b.getD 0 0, b.getD 1 0]
      #[c.getD 0 0, c.getD 1 0, c.getD 2 0, c.getD 3 0] =
        Rhone.Computation.Config.mk a b c
    rw [array_two a ha, array_two b hb, array_four c hc]

theorem encode_injective : Function.Injective encode := by
  intro ξ η h
  have := congrArg decode h
  simpa only [decode_encode] using this

@[simp] theorem encode_linked (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).c.foldl (· + ·) 0 = ξ.t := by
  simp [encode, Config.t, Fin.sum_univ_two]
  omega

@[simp] theorem encode_sumA (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).a.foldl (· + ·) 0 = ξ.sumA := by
  simp [encode, Config.sumA, Fin.sum_univ_two]

@[simp] theorem encode_sumB (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).b.foldl (· + ·) 0 = ξ.sumB := by
  simp [encode, Config.sumB, Fin.sum_univ_two]

@[simp] theorem encode_block (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).block = (ξ.nA, ξ.nB) := by
  simp only [Rhone.Computation.Config.block, Config.nA, Config.nB]
  simp [encode, Config.sumA, Config.sumB, Config.t, Fin.sum_univ_two]
  omega

@[simp] theorem encode_lineages (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    (encode ξ).a.foldl (· + ·) 0 + (encode ξ).b.foldl (· + ·) 0 +
      (encode ξ).c.foldl (· + ·) 0 = ξ.n := by
  rw [encode_sumA, encode_sumB, encode_linked]
  rfl

theorem encode_diagonal (p : Params) (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    let s := encode ξ
    let t : Nat := s.c.foldl (· + ·) 0
    let total : Nat := s.a.foldl (· + ·) 0 + s.b.foldl (· + ·) 0 + t
    ((total * (total - 1) : Nat) : Rat) + (s.block.1 : Rat) * p.thetaA +
      (s.block.2 : Rat) * p.thetaB + (t : Rat) * p.rho =
        diag p.thetaA p.thetaB p.rho ξ := by
  dsimp only
  rw [encode_lineages, encode_block, encode_linked]
  simp only [diag]
  ring

end Rhone.Computation.CheckerEncoding
