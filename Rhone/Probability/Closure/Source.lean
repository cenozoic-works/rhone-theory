/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BilinearForm.Converse
public import Rhone.Analysis.RecombinationExpansion.Operator

/-! # The source identity at symbolic parameters -/

@[expose] public section

namespace Rhone.Probability.Closure

open Finset LinearAlgebra.Recursion Denominator

variable {K KA KB : ℕ} {F : Type*} [Field F]
variable {θ θA θB ρ : F} {π : Fin K → F} {πA : Fin KA → F} {πB : Fin KB → F}

alias qOne_recursion' := Rhone.LinearAlgebra.Recursion.qOne_recursion_gen

alias source_identity' := Rhone.Probability.Denominator.source_identity_gen

theorem LDelta' {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB)
    (hn : 2 ≤ ξ.n) (hdenA : rising θA ξ.nA ≠ 0) (hdenB : rising θB ξ.nB ≠ 0) :
    Analysis.RecombinationExpansion.Lop θA θB ρ πA πB (fun η => q η - qHat θA θB πA πB η) ξ
      = twoQ1 θA θB πA πB ξ := by
  rw [Analysis.RecombinationExpansion.Lop_sub,
      Analysis.RecombinationExpansion.Lop_eq_zero_of_isSolution hq ξ hn,
      Analysis.RecombinationExpansion.Lop,
    source_identity' ξ hdenA hdenB]
  ring

theorem exists_ne_qHat_of_twoQ1_ne_zero' {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (hn : 2 ≤ ξ.n)
    (hdenA : rising θA ξ.nA ≠ 0) (hdenB : rising θB ξ.nB ≠ 0)
    (hsrc : twoQ1 θA θB πA πB ξ ≠ 0) : ∃ η : Config KA KB, q η ≠ qHat θA θB πA πB η := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have hfun : q = qHat θA θB πA πB := funext hcon
  have h1 := hq.recursion ξ hn
  rw [hfun] at h1
  have h2 := source_identity' (ρ := ρ) (πA := πA) (πB := πB) ξ hdenA hdenB
  exact hsrc (by linear_combination -h1 - h2)

theorem exists_ne_qHat_gen {KA KB : ℕ} (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB)
    (ht : 2 ≤ ξ.t) {ρ : BilinearForm.genField KA KB}
    {q : Config KA KB → BilinearForm.genField KA KB}
    (hq : IsSolution (BilinearForm.genThA KA KB) (BilinearForm.genThB KA KB) ρ
      (BilinearForm.genPiA KA KB) (BilinearForm.genPiB KA KB) q) :
    ∃ η : Config KA KB, q η ≠ qHat (BilinearForm.genThA KA KB) (BilinearForm.genThB KA KB)
      (BilinearForm.genPiA KA KB) (BilinearForm.genPiB KA KB) η := by
  have hn : 2 ≤ ξ.n := by
    have h := ξ.t_le_nA
    have h2 : ξ.nA ≤ ξ.n := by simp only [Config.nA, Config.n]; omega
    omega
  exact exists_ne_qHat_of_twoQ1_ne_zero' hq ξ hn
    (BilinearForm.rising_genThA_ne_zero (by omega) _)
    (BilinearForm.rising_genThB_ne_zero (by omega) _)
    (BilinearForm.twoQ1_gen_ne_zero hKA hKB ξ ht)

end Rhone.Probability.Closure
