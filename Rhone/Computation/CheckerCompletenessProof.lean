/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerNormalizationFoldProof
public import Rhone.Computation.ParamsProof

/-! # Completeness of exact finite-table acceptance -/

@[expose] public section
namespace Rhone.Computation

open CheckerEncoding CheckerSpec LinearAlgebra.Recursion

private theorem checkerEquation_of_solution (p : Params) (n : Nat)
    (q : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rat)
    (hq : IsSolution p.thetaA p.thetaB p.rho
      (fun i => p.piA.getD i.val 0) (fun j => p.piB.getD j.val 0) q)
    (value : Rhone.Computation.Config → Rat)
    (hv : ∀ s ∈ closure n, value s = q (decode s))
    (s : Rhone.Computation.Config) (hs : s ∈ closure n) :
    checkerEquation p value s = true := by
  obtain ⟨ha, hb, hc⟩ := closureList_shape (by
    simpa only [closure, List.mem_toArray] using hs)
  let ξ := decode s
  have henc : encode ξ = s := encode_decode s ha hb hc
  have hin : InClosure n ξ := (encode_mem_closure ξ).mp (henc.symm ▸ hs)
  have hvalue : value (encode ξ) = q ξ := by simpa only [henc] using hv s hs
  have hline : checkerLineages s = ξ.n := by rw [← henc, checkerLineages_encode]
  have hbd : ξ.n = 1 → value s = checkerBoundary p s := by
    intro hn
    rw [← henc, hvalue]
    exact (checkerBoundary_encode_of_isSolution p q hq ξ hn).symm
  have hrec : 2 ≤ ξ.n → checkerDiagonal p s * value s = recursionRhs p value s := by
    intro hn
    rw [← henc, checkerDiagonal_encode, hvalue, recursionRhs, recursionRhsDirect_encode]
    apply (hq.recursion ξ hn).trans
    symm
    apply rhs_congr
    intro η hna hnb
    have hη : encode η ∈ closure n :=
      (encode_mem_closure η).mpr ⟨hna.trans hin.1, hnb.trans hin.2⟩
    simpa only [decode_encode] using hv (encode η) hη
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases hn : checkerLineages s = 1
    · simpa [hn] using hbd (hline ▸ hn)
    · simp [hn]
  · by_cases hn : 2 ≤ checkerLineages s
    · simpa [hn] using hrec (hline ▸ hn)
    · simp [hn]

theorem checkTable_complete (p : Params) (hp : p.valid = true) (n : Nat) :
    checkTable p n ((closure n).map fun s => (s,
      Rhone.LinearAlgebra.Recursion.q
        (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
        (πB := fun (j : Fin 2) => p.piB.getD j.val 0)
        ((Params.valid_iff p).mp hp).1 ((Params.valid_iff p).mp hp).2.1
        ((Params.valid_iff p).mp hp).2.2.1 (decode s))) = true := by
  let hd := (Params.valid_iff p).mp hp
  let qValue : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rat :=
    Rhone.LinearAlgebra.Recursion.q
      (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
      (πB := fun (j : Fin 2) => p.piB.getD j.val 0) hd.1 hd.2.1 hd.2.2.1
  have hsol : IsSolution p.thetaA p.thetaB p.rho
      (fun i => p.piA.getD i.val 0) (fun j => p.piB.getD j.val 0) qValue :=
    q_isSolution hd.1 hd.2.1 hd.2.2.1
  obtain ⟨table, ht⟩ := insertTableRows_closure n (fun s => qValue (decode s))
  have hlookup : ∀ s ∈ closure n, table.contains s.key = true ∧
      table.getD s.key 0 = qValue (decode s) := by
    intro s hs
    apply insertTableRows_closure_values ht
    simpa only [closure, List.mem_toArray] using hs
  have hvalues : ∀ s ∈ closure n, table.getD s.key 0 = qValue (decode s) :=
    fun s hs => (hlookup s hs).2
  apply checkTable_true_iff.mpr
  refine ⟨table, ?_, hp, ?_, fun s hs => (hlookup s hs).1, ?_, ?_, ?_⟩
  · simpa [closure, qValue, hd] using ht
  · simp
  · have hzero : configOfCounts 0 0 0 0 0 0 0 0 ∈ closure n :=
      configOfCounts_mem_closure.mpr (by simp)
    rw [hvalues _ hzero]
    change qValue (decode (encode (0 : Rhone.LinearAlgebra.Recursion.Config 2 2))) = 1
    rw [decode_encode]
    exact hsol.empty
  · exact checkerEquation_of_solution p n qValue hsol _ hvalues
  · intro size hsize
    rw [checkerNormalization_eq_weighted _ qValue hsize hvalues]
    exact sum_q_weighted hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2 size

end Rhone.Computation
