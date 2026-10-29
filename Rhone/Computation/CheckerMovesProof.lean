/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerEncodingProof

/-! # Elementary moves in the executable representation -/

@[expose] public section

namespace Rhone.Computation.CheckerEncoding

open LinearAlgebra.Recursion

@[simp] theorem encode_dropA (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i : Fin 2) :
    encode (ξ.dropA i) = {encode ξ with a := decrement (encode ξ).a i.val} := by
  fin_cases i <;> rfl

@[simp] theorem encode_dropB (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (j : Fin 2) :
    encode (ξ.dropB j) = {encode ξ with b := decrement (encode ξ).b j.val} := by
  fin_cases j <;> rfl

@[simp] theorem encode_dropC (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    encode (ξ.dropC i j) =
      {encode ξ with c := decrement (encode ξ).c (2 * i.val + j.val)} := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem encode_mergeAB (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    encode (ξ.mergeAB i j) =
      ⟨decrement (encode ξ).a i.val, decrement (encode ξ).b j.val,
        increment (encode ξ).c (2 * i.val + j.val)⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem encode_killA (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    encode (ξ.killA i j) =
      ⟨(encode ξ).a, increment (encode ξ).b j.val,
        decrement (encode ξ).c (2 * i.val + j.val)⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem encode_killB (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    encode (ξ.killB i j) =
      ⟨increment (encode ξ).a i.val, (encode ξ).b,
        decrement (encode ξ).c (2 * i.val + j.val)⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem encode_split (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (i j : Fin 2) :
    encode (ξ.split i j) =
      ⟨increment (encode ξ).a i.val, increment (encode ξ).b j.val,
        decrement (encode ξ).c (2 * i.val + j.val)⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

end Rhone.Computation.CheckerEncoding
