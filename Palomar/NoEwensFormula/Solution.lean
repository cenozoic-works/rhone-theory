module

public import Rhone.Algebra.BoundedDenominator
public import Rhone.Algebra.BlockTwoSymbolic.NoDegreeOneFormula
public import Rhone.Algebra.BlockTwoSymbolic.NoDegreeTwoFormula
public import Rhone.Algebra.BlockTwoSymbolic.TotalDegreeU
public import Rhone.Probability.SamplingUniform.NoFormula
public import Rhone.Probability.RecombinationDegree.NoFormula

@[expose] public section

namespace Rhone.Palomar.NoEwensFormula

open Rhone.Algebra Analysis Rhone.LinearAlgebra Probability Algebra.KilledSystem
open Algebra.BlockTwoSymbolic

theorem boundedDen_eval {F : Type*} [Field F] {D : ℕ} {tA tB tR : RatFunc F}
    (hA : BoundedDen D tA) (hB : BoundedDen D tB) (hR : BoundedDen D tR)
    {e : Expr F} (h : DAdm tA tB tR D e) : BoundedDen D (Expr.eval tA tB tR e) :=
  Algebra.boundedDen_eval hA hB hR h

theorem no_degree_one_formula {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      Rhone.Algebra.DAdm (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) 1 e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 :=
  no_degree_one_formula_pi_coalescent hq

theorem no_degree_one_formula_total {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), GenericField.TotalDAdm
        SymbolicFrequencies.Kpi 1 e ∧
        Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
            (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
            e = q s22 :=
  no_degree_one_formula_total_pi_coalescent hq

theorem no_degree_two_formula {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      Rhone.Algebra.DAdm thAuπ thBuπ rhoUπ 2 e ∧
        Expr.eval thAuπ thBuπ rhoUπ e = q s22 :=
  no_degree_two_formula_pi_coalescent hq

theorem no_degree_two_formula_total {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), TotalDAdmUπ 2 e
        ∧ Expr.eval thAuπ thBuπ rhoUπ e = q s22 :=
  no_degree_two_formula_total_pi_coalescent hq

theorem exists_isSolutionπ : ∃ q : St → GenericField.L SymbolicFrequencies.Kpi, IsSolutionπ q :=
  ⟨BlockTwoSymbolic.qSolπ, BlockTwoSymbolic.qSolπ_isSolutionπ⟩

theorem isSolutionπ_unique_s22 {q q' : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q)
    (hq' : IsSolutionπ q') : q s22 = q' s22 :=
  BlockTwoSymbolic.unique_of_isSolutionπ hq hq' s22 s22_mem_closureList

theorem no_bounded_degree_formula (D : ℕ)
    {q : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rhone.Probability.SamplingUniform.UniformField}
    (hq : Rhone.LinearAlgebra.Recursion.IsSolution
      Rhone.Probability.SamplingUniform.uniformA Rhone.Probability.SamplingUniform.uniformB
      Rhone.Probability.SamplingUniform.uniformRho
      (Rhone.Probability.SamplingUniform.piOf Rhone.Probability.SamplingUniform.uniformP)
      (Rhone.Probability.SamplingUniform.piOf
        Rhone.Probability.SamplingUniform.uniformR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr
        Rhone.Probability.SamplingUniform.UniformCoefficient,
      Rhone.Algebra.DAdm Rhone.Probability.SamplingUniform.uniformA
        Rhone.Probability.SamplingUniform.uniformB Rhone.Probability.SamplingUniform.uniformRho
        D e ∧
      Rhone.Algebra.Expr.eval Rhone.Probability.SamplingUniform.uniformA
        Rhone.Probability.SamplingUniform.uniformB Rhone.Probability.SamplingUniform.uniformRho
        e = q (Rhone.Probability.SamplingUniform.samplingMM m) :=
  SamplingUniform.no_bounded_degree_formula_sampling D hq

theorem existsUnique_uniform_solution :
    ∃! q : Rhone.LinearAlgebra.Recursion.Config 2 2 →
        Rhone.Probability.SamplingUniform.UniformField,
      Rhone.LinearAlgebra.Recursion.IsSolution
        Rhone.Probability.SamplingUniform.uniformA Rhone.Probability.SamplingUniform.uniformB
        Rhone.Probability.SamplingUniform.uniformRho
        (Rhone.Probability.SamplingUniform.piOf Rhone.Probability.SamplingUniform.uniformP)
        (Rhone.Probability.SamplingUniform.piOf
          Rhone.Probability.SamplingUniform.uniformR) q :=
  SamplingUniform.existsUnique_uniform_solution

theorem no_bounded_recombination_degree_formula (D : ℕ)
    {q : Recursion.Config 2 2 → RecombinationDegree.RecombField}
    (hq : Recursion.IsSolution
      RecombinationDegree.recombA RecombinationDegree.recombB
      RecombinationDegree.recombRho
      (SamplingUniform.piOf RecombinationDegree.recombP)
      (SamplingUniform.piOf RecombinationDegree.recombR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Expr RecombinationDegree.RecombCoefficient,
      DAdm RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho D e ∧
      Expr.eval RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho e = q (Rhone.Probability.SamplingUniform.samplingMM m) :=
  RecombinationDegree.no_bounded_recombination_degree_formula_sampling D hq

theorem existsUnique_recomb_solution :
    ∃! q : Recursion.Config 2 2 → RecombinationDegree.RecombField,
      Recursion.IsSolution
        RecombinationDegree.recombA RecombinationDegree.recombB
        RecombinationDegree.recombRho
        (SamplingUniform.piOf RecombinationDegree.recombP)
        (SamplingUniform.piOf RecombinationDegree.recombR) q :=
  RecombinationDegree.existsUnique_recomb_solution

end Rhone.Palomar.NoEwensFormula
