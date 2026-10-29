/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.TwoGameteBridge.Transfer
public import Rhone.Algebra.BlockTwoSymbolic.NoDegreeOneFormula
public import Rhone.Algebra.BlockTwoSymbolic.NoDegreeTwoFormula

/-! # Symbolic recursion in the two-gamete bridge at `n = 2` -/

@[expose] public section

namespace Rhone.Algebra.TwoGameteBridge

open KilledSystem LinearAlgebra.Recursion BlockTwoSymbolic

theorem piB_of_isSolution {tA tB r pa pb : GenericField.L SymbolicFrequencies.Kpi}
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : LinearAlgebra.Recursion.IsSolution tA tB r ![pa, 1 - pa] ![pb, 1 - pb] Q) :
    BlockTwoSymbolic.IsSolutionG tA tB r pa pb (fun s => Q (toConfig s)) := by
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionG] using finiteSystem_of_isSolution hQ

theorem piBπ_of_isSolution {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : LinearAlgebra.Recursion.IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    BlockTwoSymbolic.IsSolutionπ (fun s => Q (toConfig s)) :=
  piB_of_isSolution hQ

theorem no_degree_one_formula_symbolic_general
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : LinearAlgebra.Recursion.IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      DAdm (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) 1 e ∧
      Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e =
        Q (toConfig BlockTwoSymbolic.s22) :=
  BlockTwoSymbolic.no_degree_one_formula_pi_coalescent (piBπ_of_isSolution hQ)

theorem no_degree_two_formula_symbolic_general
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : LinearAlgebra.Recursion.IsSolution thAuπ thBuπ rhoUπ
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), DAdm thAuπ thBuπ rhoUπ 2 e ∧
      Expr.eval thAuπ thBuπ rhoUπ e = Q (toConfig BlockTwoSymbolic.s22) :=
  BlockTwoSymbolic.no_degree_two_formula_pi_coalescent (piB_of_isSolution hQ)

theorem eq_qSolπ_of_general {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : LinearAlgebra.Recursion.IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) (s : St) (hs : s ∈ closureList) :
    Q (toConfig s) = qSolπ s :=
  BlockTwoSymbolic.unique_of_isSolutionπ (piBπ_of_isSolution hQ) qSolπ_isSolutionπ s hs

theorem qSolπ_general_recursion (ξ : Config 2 2)
    (hA : ξ.nA ≤ 2) (hB : ξ.nB ≤ 2) (hn : 2 ≤ ξ.n) :
    diag (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
        (GenericField.rhoL SymbolicFrequencies.Kpi) ξ * qSolπ (ofConfig ξ) =
      rhs (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi)
        ![piAL, 1 - piAL] ![piBL, 1 - piBL] (fun ξ => qSolπ (ofConfig ξ)) ξ := by
  apply recursion_of_finiteSystem (ξ := ξ) ?_ hA hB hn
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionπ] using qSolπ_isSolutionπ

theorem qSolπ_n2IsSolution :
    N2IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] (fun ξ => qSolπ (ofConfig ξ)) := by
  apply n2IsSolution_of_finiteSystem
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionπ] using qSolπ_isSolutionπ

theorem eq_qSolπ_of_n2IsSolution {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : N2IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) (ξ : Config 2 2)
    (hA : ξ.nA ≤ 2) (hB : ξ.nB ≤ 2) (hne : 1 ≤ ξ.nA + ξ.nB) :
    Q ξ = qSolπ (ofConfig ξ) := by
  have hfin : BlockTwoSymbolic.IsSolutionπ (fun s => Q (toConfig s)) := by
    simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionπ] using finiteSystem_of_n2IsSolution hQ
  have hs : ofConfig ξ ∈ closureList := by
    apply (mem_closureList_iff (ofConfig ξ)).mpr
    simpa only [toConfig_ofConfig] using And.intro hA (And.intro hB hne)
  simpa only [toConfig_ofConfig] using
    BlockTwoSymbolic.unique_of_isSolutionπ hfin qSolπ_isSolutionπ (ofConfig ξ) hs

theorem exists_unique_n2_symbolic :
    ∃ Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi,
      N2IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
        ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q ∧
      ∀ Q', N2IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
        ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q' →
        ∀ ξ, ξ.nA ≤ 2 → ξ.nB ≤ 2 → 1 ≤ ξ.nA + ξ.nB → Q' ξ = Q ξ :=
  ⟨fun ξ => qSolπ (ofConfig ξ), qSolπ_n2IsSolution,
    fun _ hQ ξ hA hB hne => eq_qSolπ_of_n2IsSolution hQ ξ hA hB hne⟩

theorem no_degree_one_formula_symbolic_n2 {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : N2IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      DAdm (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) 1 e ∧
      Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e =
        Q (toConfig BlockTwoSymbolic.s22) := by
  apply BlockTwoSymbolic.no_degree_one_formula_pi_coalescent (q := fun s => Q (toConfig s))
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionπ] using finiteSystem_of_n2IsSolution hQ

theorem no_degree_two_formula_symbolic_n2 {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : N2IsSolution thAuπ thBuπ rhoUπ ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), DAdm thAuπ thBuπ rhoUπ 2 e ∧
      Expr.eval thAuπ thBuπ rhoUπ e = Q (toConfig BlockTwoSymbolic.s22) := by
  apply BlockTwoSymbolic.no_degree_two_formula_pi_coalescent (q := fun s => Q (toConfig s))
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionG] using finiteSystem_of_n2IsSolution hQ

theorem qSolUπ_n2IsSolution :
    N2IsSolution thAuπ thBuπ rhoUπ ![piAL, 1 - piAL] ![piBL, 1 - piBL]
      (fun ξ => qSolUπ (ofConfig ξ)) := by
  apply n2IsSolution_of_finiteSystem
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionG] using qSolUπ_isSolutionUπ

theorem eq_q22πU_of_n2IsSolution {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : N2IsSolution thAuπ thBuπ rhoUπ ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    Q (toConfig BlockTwoSymbolic.s22) = q22πU := by
  apply BlockTwoSymbolic.eq_q22πU_of_isSolutionUπ (q := fun s => Q (toConfig s))
  simpa [FiniteSystem, BlockTwoSymbolic.IsSolutionG] using finiteSystem_of_n2IsSolution hQ

end Rhone.Algebra.TwoGameteBridge
