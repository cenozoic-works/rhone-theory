/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.TwoGameteBridge.Transfer
public import Rhone.Algebra.KilledSystem.NoFormula
public import Rhone.Algebra.KilledSystemULast.NoFormula

/-! # Fixed-frequency solutions of the two-gamete recursion: no low-degree formula for `q22` -/

@[expose] public section

namespace Rhone.Algebra.TwoGameteBridge

open KilledSystem LinearAlgebra.Recursion

theorem killedSystem_isSolution_of_isSolution {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thA thB rhoL ![piA0, piA1] ![piB0, piB1] Q) :
    KilledSystem.IsSolution (fun s => Q (toConfig s)) := by
  simpa [FiniteSystem, KilledSystem.IsSolution] using finiteSystem_of_isSolution hQ

theorem killedSystemULast_isSolutionU_of_isSolution {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thAu thBu rhoU ![piA0, piA1] ![piB0, piB1] Q) :
    KilledSystemULast.IsSolutionU (fun s => Q (toConfig s)) := by
  simpa [FiniteSystem, KilledSystemULast.IsSolutionU] using finiteSystem_of_isSolution hQ

theorem no_degree_one_formula_general {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thA thB rhoL ![piA0, piA1] ![piB0, piB1] Q) :
    ¬ ∃ e : Expr Fuv, DAdm thA thB rhoL 1 e ∧
      Expr.eval thA thB rhoL e = Q (toConfig KilledSystem.s22) :=
  KilledSystem.no_degree_one_formula_coalescent (killedSystem_isSolution_of_isSolution hQ)

theorem no_degree_two_formula_general {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thAu thBu rhoU ![piA0, piA1] ![piB0, piB1] Q) :
    ¬ ∃ e : Expr Fuv, DAdm thAu thBu rhoU 2 e ∧
      Expr.eval thAu thBu rhoU e = Q (toConfig KilledSystem.s22) :=
  KilledSystemULast.no_degree_two_formula_coalescent
      (killedSystemULast_isSolutionU_of_isSolution hQ)

theorem no_degree_two_formula_total_general {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thAu thBu rhoU ![piA0, piA1] ![piB0, piB1] Q) :
    ¬ ∃ e : Expr Fuv, GenericField.TotalDAdmU 2 e ∧
      Expr.eval thAu thBu rhoU e = Q (toConfig KilledSystem.s22) :=
  KilledSystemULast.no_degree_two_formula_total_coalescent
      (killedSystemULast_isSolutionU_of_isSolution hQ)

theorem eq_q22_of_general {Q : Config 2 2 → L}
    (hQ : LinearAlgebra.Recursion.IsSolution thA thB rhoL ![piA0, piA1] ![piB0, piB1] Q) :
    Q (toConfig KilledSystem.s22) = q22 :=
  KilledSystem.eq_q22_of_isSolution (killedSystem_isSolution_of_isSolution hQ)

end Rhone.Algebra.TwoGameteBridge
