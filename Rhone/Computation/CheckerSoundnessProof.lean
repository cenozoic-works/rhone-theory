/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerAcceptanceProof
public import Rhone.Computation.CheckerClosureEnumerationProof
public import Rhone.Computation.CheckerBoundaryProof
public import Rhone.Computation.CheckerRecursionProof
public import Rhone.Computation.CheckerClosureSpec

/-! # Soundness of exact finite-table acceptance -/

@[expose] public section
namespace Rhone.Computation

open CheckerEncoding CheckerSpec LinearAlgebra.Recursion

theorem encode_mem_closure {n : Nat} (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    encode ξ ∈ closure n ↔ InClosure n ξ := by
  change configOfCounts (ξ.a 0) (ξ.a 1) (ξ.b 0) (ξ.b 1)
    (ξ.c 0 0) (ξ.c 0 1) (ξ.c 1 0) (ξ.c 1 1) ∈ closure n ↔ _
  rw [configOfCounts_mem_closure]
  simp only [InClosure, Rhone.LinearAlgebra.Recursion.Config.nA,
    Rhone.LinearAlgebra.Recursion.Config.nB, Rhone.LinearAlgebra.Recursion.Config.sumA,
    Rhone.LinearAlgebra.Recursion.Config.sumB, Rhone.LinearAlgebra.Recursion.Config.t,
    Fin.sum_univ_two]
  omega

theorem checkerRowValid_iff {n : Nat} {s : Rhone.Computation.Config} :
    checkerRowValid n s = true ↔ s.a.size = 2 ∧ s.b.size = 2 ∧ s.c.size = 4 ∧
      s.block.1 ≤ n ∧ s.block.2 ≤ n := by
  simp [checkerRowValid, and_assoc]

theorem checkTable_sound {p : Params} {n : Nat} {entries : Array (Rhone.Computation.Config × Rat)}
    (h : checkTable p n entries = true) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      ∀ entry ∈ entries, entry.2 =
        Rhone.LinearAlgebra.Recursion.q (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
          (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ (decode entry.1) := by
  obtain ⟨table, ht, hp, _, _, hempty, heq, _⟩ := checkTable_true_iff.mp h
  have hdomain : 0 < p.thetaA ∧ 0 < p.thetaB ∧ 0 ≤ p.rho := by
    simp only [Params.valid, Bool.and_eq_true_iff, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨hp.1.1.1.1.1.1.1.1, hp.1.1.1.1.1.1.1.2, hp.1.1.1.1.1.1.2⟩
  obtain ⟨hθA, hθB, hρ⟩ := hdomain
  refine ⟨hθA, hθB, hρ, ?_⟩
  let value := fun s : Rhone.Computation.Config => table.getD s.key 0
  let f := fun ξ : Rhone.LinearAlgebra.Recursion.Config 2 2 => value (encode ξ)
  have hsol := q_isSolution (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
    (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ
  have hf : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config 2 2, InClosure n ξ →
      f ξ = Rhone.LinearAlgebra.Recursion.q (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
        (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hθA hθB hρ ξ := by
    apply closure_eq_q hθA hθB hρ
    · intro ξ hc hn
      rcases Nat.eq_zero_or_pos ξ.n with hz | hz
      · have hzero := ξ.eq_zero_of_n_eq_zero hz
        subst ξ
        have h0 : f (0 : Rhone.LinearAlgebra.Recursion.Config 2 2) = 1 := by
          simpa [f, value, encode, configOfCounts] using hempty
        exact h0.trans hsol.empty.symm
      · have hone : ξ.n = 1 := by omega
        have hb := (Bool.and_eq_true_iff.mp (heq (encode ξ)
          (encode_mem_closure ξ |>.mpr hc))).1
        have hv : value (encode ξ) = checkerBoundary p (encode ξ) := by
          simpa [checkerEquation, checkerLineages_encode, hone] using hb
        exact hv.trans (checkerBoundary_encode_of_isSolution p _ hsol ξ hone)
    · intro ξ hc hn
      have hr := (Bool.and_eq_true_iff.mp (heq (encode ξ)
        (encode_mem_closure ξ |>.mpr hc))).2
      have hv : checkerDiagonal p (encode ξ) * value (encode ξ) =
          recursionRhs p value (encode ξ) := by
        simpa [checkerEquation, checkerLineages_encode, hn] using hr
      simpa only [checkerDiagonal_encode, recursionRhs, recursionRhsDirect_encode, f]
        using hv
  intro entry hm
  have hvalid := (insertTableRows_valid_novel ht entry (Array.mem_toList_iff.mpr hm)).1
  have hvalue := (insertTableRows_values ht entry (Array.mem_toList_iff.mpr hm)).2
  obtain ⟨ha, hb, hc, hna, hnb⟩ := checkerRowValid_iff.mp hvalid
  have henc := encode_decode entry.1 ha hb hc
  have hin : InClosure n (decode entry.1) := by
    have hblock := encode_block (decode entry.1)
    rw [henc] at hblock
    exact ⟨by simpa [hblock] using hna, by simpa [hblock] using hnb⟩
  have he := hf (decode entry.1) hin
  rw [show f (decode entry.1) = entry.2 by simpa [f, value, henc] using hvalue] at he
  exact he

end Rhone.Computation
