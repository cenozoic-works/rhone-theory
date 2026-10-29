/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.SamplingUniform.NoFormula
public import Rhone.Probability.SamplingNumerators.Obstruction
public import Rhone.Algebra.TwoGameteBridge.Symbolic
public import Rhone.Algebra.BlockTwoSymbolic.TotalDegreeU
public import Rhone.Algebra.GenericField.TotalDegree
public import Rhone.Coalescent.TwoLocusGenealogy.Limit

/-! # Two-locus non-existence of a bounded-degree formula, composed into single statements -/

@[expose] public section

namespace Rhone.Coalescent.NoBoundedDegreeFormula

open Polynomial Rhone.Algebra Analysis Rhone.LinearAlgebra Probability LinearAlgebra.Recursion
    LinearAlgebra.SlotDeletion Probability.SlotDeletion
open Algebra.SamplingUniform Probability.SamplingUniform

noncomputable def realEval {F : Type*} [Field F] (ι : RatFunc F →+* ℝ) (tA tB tR : RatFunc F) :
    Expr F → ℝ
  | .const q => (q : ℝ)
  | .coeff x => ι (algebraMap F (RatFunc F) x)
  | .thA => ι tA
  | .thB => ι tB
  | .rho => ι tR
  | .add x y => realEval ι tA tB tR x + realEval ι tA tB tR y
  | .mul x y => realEval ι tA tB tR x * realEval ι tA tB tR y
  | .div x y => realEval ι tA tB tR x / realEval ι tA tB tR y

theorem realEval_eq {F : Type*} [Field F] (ι : RatFunc F →+* ℝ) (tA tB tR : RatFunc F)
    (e : Expr F) : realEval ι tA tB tR e = ι (Expr.eval tA tB tR e) := by
  induction e with
  | const q => simp [realEval, Expr.eval]
  | coeff x => rfl
  | thA => rfl
  | thB => rfl
  | rho => rfl
  | add x y ihx ihy => simp [realEval, Expr.eval, ihx, ihy]
  | mul x y ihx ihy => simp [realEval, Expr.eval, ihx, ihy]
  | div x y ihx ihy => simp [realEval, Expr.eval, ihx, ihy]

structure IsAdmissiblePoint (ι : UniformField →+* ℝ) : Prop where
  thetaA_pos : 0 < ι uniformA
  thetaB_pos : 0 < ι uniformB
  rho_nonneg : 0 ≤ ι uniformRho
  p_nonneg : 0 ≤ ι uniformP
  p_le_one : ι uniformP ≤ 1
  r_nonneg : 0 ≤ ι uniformR
  r_le_one : ι uniformR ≤ 1

theorem exists_realPoint_in_box {a₁ a₂ b₁ b₂ c₁ c₂ p₁ p₂ r₁ r₂ : ℝ} (ha : a₁ < a₂)
    (hb : b₁ < b₂) (hc : c₁ < c₂) (hp : p₁ < p₂) (hr : r₁ < r₂) :
    ∃ ι : UniformField →+* ℝ, ι uniformA ∈ Set.Ioo a₁ a₂ ∧ ι uniformB ∈ Set.Ioo b₁ b₂ ∧
      ι uniformRho ∈ Set.Ioo c₁ c₂ ∧ ι uniformP ∈ Set.Ioo p₁ p₂ ∧
      ι uniformR ∈ Set.Ioo r₁ r₂ := by
  have h1 : Countable (RatFunc ℚ) := countable_ratFunc ℚ
  have h2 : Countable (RatFunc (RatFunc ℚ)) := countable_ratFunc _
  have h3 : Countable (RatFunc (RatFunc (RatFunc ℚ))) := countable_ratFunc _
  have h4 : Countable (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) := countable_ratFunc _
  obtain ⟨g1, -, hρ1, hρ2⟩ := exists_ratFunc_extension (algebraMap ℚ ℝ) hc
  obtain ⟨g2, hg2, hl1, hl2⟩ := exists_ratFunc_extension g1 ha
  obtain ⟨g3, hg3, hr1, hr2⟩ := exists_ratFunc_extension g2 hr
  obtain ⟨g4, hg4, hp1, hp2⟩ := exists_ratFunc_extension g3 hp
  obtain ⟨g5, hg5, hθ1, hθ2⟩ := exists_ratFunc_extension g4
    (show g2 RatFunc.X + b₁ < g2 RatFunc.X + b₂ by linarith)
  have hA : g5 uniformA = g2 RatFunc.X := by
    rw [uniformA, RatFunc.algebraMap_C, uniformLambda, hg5, hg4, hg3]
  have hB : g5 uniformB = g5 RatFunc.X - g2 RatFunc.X := by
    rw [uniformB, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_sub, uniformLambda,
      hg5, hg4, hg3]
  have hR : g5 uniformRho = g1 RatFunc.X := by
    rw [uniformRho, RatFunc.algebraMap_C]
    change g5 (RatFunc.C (RatFunc.C (RatFunc.C (RatFunc.C RatFunc.X)))) = _
    rw [hg5, hg4, hg3, hg2]
  have hP : g5 uniformP = g4 RatFunc.X := by
    rw [uniformP, RatFunc.algebraMap_C, hg5]
  have hRr : g5 uniformR = g3 RatFunc.X := by
    rw [uniformR, RatFunc.algebraMap_C, hg5, hg4]
  refine ⟨g5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA]; exact ⟨hl1, hl2⟩
  · rw [hB]; exact ⟨by linarith, by linarith⟩
  · rw [hR]; exact ⟨hρ1, hρ2⟩
  · rw [hP]; exact ⟨hp1, hp2⟩
  · rw [hRr]; exact ⟨hr1, hr2⟩

theorem exists_admissiblePoint : ∃ ι : UniformField →+* ℝ, IsAdmissiblePoint ι := by
  obtain ⟨ι, hA, hB, hR, hP, hRr⟩ := exists_realPoint_in_box (zero_lt_one' ℝ) (zero_lt_one' ℝ)
    (zero_lt_one' ℝ) (zero_lt_one' ℝ) (zero_lt_one' ℝ)
  exact ⟨ι, hA.1, hB.1, hR.1.le, hP.1.le, hP.2.le, hRr.1.le, hRr.2.le⟩

noncomputable def genericSolution : Config 2 2 → UniformField :=
  Rational.qOfDet uniform_detNeZero

theorem genericSolution_isSolution :
    IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) genericSolution :=
  Rational.qOfDet_isSolution uniform_detNeZero

theorem genericSolution_unique {q : Config 2 2 → UniformField}
    (hq : IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q) :
    q = genericSolution :=
  Rational.qOfDet_unique uniform_detNeZero hq

theorem piOf_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (i : Fin 2) : 0 ≤ piOf x i := by
  fin_cases i
  · simpa [piOf] using h0
  · simpa [piOf] using h1

theorem piOf_sum_univ (x : ℝ) : ∑ i, piOf x i = 1 := by
  simp [Fin.sum_univ_two, piOf]

theorem qProb_piOf_isSolution {θA θB ρ p r : ℝ} (hA : 0 < θA) (hB : 0 < θB) (hρ : 0 ≤ ρ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsSolution θA θB ρ (piOf p) (piOf r) (TwoLocusGenealogy.qProb θA θB ρ (piOf p) (piOf r)) :=
  TwoLocusGenealogy.qProb_isSolution hA hB hρ (piOf_nonneg hp0 hp1) (piOf_sum_univ p)
    (piOf_nonneg hr0 hr1) (piOf_sum_univ r)

theorem genericSolution_realPoint {ι : UniformField →+* ℝ} (h : IsAdmissiblePoint ι)
    (ξ : Config 2 2) :
    ι (genericSolution ξ) =
      TwoLocusGenealogy.qProb (ι uniformA) (ι uniformB) (ι uniformRho)
        (piOf (ι uniformP)) (piOf (ι uniformR)) ξ := by
  have h1 : IsSolution (ι uniformA) (ι uniformB) (ι uniformRho)
      (piOf (ι uniformP)) (piOf (ι uniformR)) (fun η => ι (genericSolution η)) := by
    have h := Rational.isSolution_map ι genericSolution_isSolution
    rwa [piOf_map, piOf_map] at h
  have h2 := qProb_piOf_isSolution h.thetaA_pos h.thetaB_pos h.rho_nonneg h.p_nonneg
    h.p_le_one h.r_nonneg h.r_le_one
  exact congrFun (IsSolution.unique h.thetaA_pos h.thetaB_pos h.rho_nonneg h1 h2) ξ

theorem no_bounded_degree_formula_genericSolution (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Expr UniformCoefficient,
      DAdm uniformA uniformB uniformRho D e ∧
      Expr.eval uniformA uniformB uniformRho e = genericSolution (samplingMM m) :=
  no_bounded_degree_formula_sampling D genericSolution_isSolution

theorem no_bounded_degree_formula_existsUnique :
    ∃ q : Config 2 2 → UniformField,
      IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q ∧
      (∀ q', IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q' →
        q' = q) ∧
      ∀ D : ℕ, ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Expr UniformCoefficient,
        DAdm uniformA uniformB uniformRho D e ∧
        Expr.eval uniformA uniformB uniformRho e = q (samplingMM m) :=
  ⟨genericSolution, genericSolution_isSolution, fun _ hq => genericSolution_unique hq,
    no_bounded_degree_formula_genericSolution⟩

theorem no_bounded_degree_formula_qProb (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ ι : UniformField →+* ℝ, IsAdmissiblePoint ι →
      ¬ ∃ e : Expr UniformCoefficient,
        DAdm uniformA uniformB uniformRho D e ∧
        realEval ι uniformA uniformB uniformRho e =
          TwoLocusGenealogy.qProb (ι uniformA) (ι uniformB) (ι uniformRho)
            (piOf (ι uniformP)) (piOf (ι uniformR)) (samplingMM m) := by
  obtain ⟨m, hm, h⟩ := no_bounded_degree_formula_genericSolution D
  refine ⟨m, hm, fun ι hι ⟨e, he, hv⟩ => h ⟨e, he, ringHom_injective_of_field ι ?_⟩⟩
  rw [← realEval_eq, hv, genericSolution_realPoint hι]

theorem qProb_samplingMM_eq_quotient {θA θB ρ p r : ℝ} (hA : 0 < θA) (hB : 0 < θB)
    (hρ : 0 ≤ ρ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (m : ℕ) :
    TwoLocusGenealogy.qProb θA θB ρ (piOf p) (piOf r) (samplingMM m) =
      samplingNumerator θA θB ρ p r m / Dfull θA θB ρ m m := by
  have h := map_samplingNumerator_eq_Dfull_mul_q hA hB hρ
    (qProb_piOf_isSolution hA hB hρ hp0 hp1 hr0 hr1) (RingHom.id ℝ) θA θB ρ p r
    rfl rfl rfl rfl rfl m
  rw [eq_div_iff (Denominator.Dfull_pos hA hB hρ m m).ne', mul_comm]
  exact h.symm

theorem genericSolution_samplingMM_eq_quotient (m : ℕ) :
    genericSolution (samplingMM m) =
      samplingNumerator uniformA uniformB uniformRho uniformP uniformR m /
        Dfull uniformA uniformB uniformRho m m := by
  obtain ⟨ι, hι⟩ := exists_admissiblePoint
  have h1 : IsSolution (ι uniformA) (ι uniformB) (ι uniformRho)
      (piOf (ι uniformP)) (piOf (ι uniformR)) (fun η => ι (genericSolution η)) := by
    have h := Rational.isSolution_map ι genericSolution_isSolution
    rwa [piOf_map, piOf_map] at h
  have hnum := map_samplingNumerator_eq_Dfull_mul_q hι.thetaA_pos hι.thetaB_pos hι.rho_nonneg h1 ι
    uniformA uniformB uniformRho uniformP uniformR rfl rfl rfl rfl rfl m
  have hpos := Denominator.Dfull_pos hι.thetaA_pos hι.thetaB_pos hι.rho_nonneg m m
  have hden : Dfull uniformA uniformB uniformRho m m ≠ 0 := by
    intro h0
    have := Dfull_map ι uniformA uniformB uniformRho m m
    rw [h0, map_zero] at this
    exact hpos.ne this
  refine (eq_div_iff hden).2 (ringHom_injective_of_field ι ?_)
  rw [map_mul, Dfull_map, hnum, mul_comm]

theorem no_bounded_degree_formula_universalQuotient (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧
      (∀ θA θB ρ p r : ℝ, 0 < θA → 0 < θB → 0 ≤ ρ → 0 ≤ p → p ≤ 1 → 0 ≤ r → r ≤ 1 →
        TwoLocusGenealogy.qProb θA θB ρ (piOf p) (piOf r) (samplingMM m) =
          samplingNumerator θA θB ρ p r m / Dfull θA θB ρ m m) ∧
      ¬ ∃ e : Expr UniformCoefficient,
        DAdm uniformA uniformB uniformRho D e ∧
        Expr.eval uniformA uniformB uniformRho e =
          samplingNumerator uniformA uniformB uniformRho uniformP uniformR m /
            Dfull uniformA uniformB uniformRho m m := by
  obtain ⟨m, hm, h⟩ := no_bounded_degree_formula_genericSolution D
  refine ⟨m, hm, fun θA θB ρ p r hA hB hρ hp0 hp1 hr0 hr1 =>
    qProb_samplingMM_eq_quotient hA hB hρ hp0 hp1 hr0 hr1 m, ?_⟩
  rw [← genericSolution_samplingMM_eq_quotient]
  exact h

section DegreeThree

open SamplingNumerators

theorem exists_sampling_realPoint :
    ∃ ι : SamplingField →+* ℝ, 0 < ι samplingB ∧ 0 < ι samplingRho := by
  have h1 : Countable (RatFunc ℚ) := countable_ratFunc ℚ
  obtain ⟨g1, -, hρ, -⟩ := exists_ratFunc_extension (algebraMap ℚ ℝ) (zero_lt_one' ℝ)
  obtain ⟨g2, hg2, hθ, -⟩ := exists_ratFunc_extension g1 (show (1 : ℝ) < 2 by norm_num)
  refine ⟨g2, ?_, ?_⟩
  · rw [samplingB, map_sub, RatFunc.algebraMap_X, map_one, map_sub, map_one]
    linarith
  · rw [samplingRho, RatFunc.algebraMap_C, hg2]
    exact hρ

theorem piThird_map {F : Type*} [Field F] (ι : F →+* ℝ) :
    (fun i => ι ((piThird : Fin 2 → F) i)) = piThird := by
  funext i
  fin_cases i
  · change ι (1 / 3) = 1 / 3
    rw [map_div₀, map_one, map_ofNat]
  · change ι (2 / 3) = 2 / 3
    rw [map_div₀, map_ofNat, map_ofNat]

theorem sampling_isSolution_map (ι : SamplingField →+* ℝ) {q : Config 2 2 → SamplingField}
    (hq : IsSolution samplingA samplingB samplingRho piThird piThird q) :
    IsSolution 1 (ι samplingB) (ι samplingRho) piThird piThird (fun η => ι (q η)) := by
  have h := Rational.isSolution_map ι hq
  rwa [piThird_map, show ι samplingA = 1 from map_one ι] at h

theorem sampling_detNeZero :
    Rational.DetNeZero samplingA samplingB samplingRho
      (piThird : Fin 2 → SamplingField) piThird := by
  obtain ⟨ι, hB, hR⟩ := exists_sampling_realPoint
  intro N
  exact Rational.det_bMat_ne_zero_of_hom ι
    (by rw [show ι samplingA = 1 from map_one ι]; exact one_pos) hB hR.le N

theorem existsUnique_sampling33_solution :
    ∃! q : Config 2 2 → SamplingField,
      IsSolution samplingA samplingB samplingRho piThird piThird q :=
  ⟨Rational.qOfDet sampling_detNeZero, Rational.qOfDet_isSolution sampling_detNeZero,
    fun _ hq => Rational.qOfDet_unique sampling_detNeZero hq⟩

theorem sampling33_eq_of_isSolution {q : Config 2 2 → SamplingField}
    (hq : IsSolution samplingA samplingB samplingRho piThird piThird q) :
    q sampling33 = sampling33Value := by
  obtain ⟨ι, hB, hR⟩ := exists_sampling_realPoint
  have h := sampling33_eq_quotient (zero_lt_one' ℝ) hB hR.le
    (sampling_isSolution_map ι hq)
  apply ringHom_injective_of_field ι
  rw [sampling33Value_eq_quotient, map_div₀,
    SamplingNumerators.samplingNumerator_map ι ι.map_rat_algebraMap, d33_map,
    show ι samplingA = 1 from map_one ι]
  exact h

theorem four_le_of_sampling33_isSolution {q : Config 2 2 → SamplingField}
    (hq : IsSolution samplingA samplingB samplingRho piThird piThird q) {D : ℕ}
    {e : Expr SamplingCoefficientField} (he : DAdm samplingA samplingB samplingRho D e)
    (hv : Expr.eval samplingA samplingB samplingRho e = q sampling33) : 4 ≤ D :=
  four_le_of_sampling33 he (hv.trans (sampling33_eq_of_isSolution hq))

theorem no_degree_three_formula_sampling33_isSolution {q : Config 2 2 → SamplingField}
    (hq : IsSolution samplingA samplingB samplingRho piThird piThird q) :
    ¬ ∃ e : Expr SamplingCoefficientField,
      DAdm samplingA samplingB samplingRho 3 e ∧
      Expr.eval samplingA samplingB samplingRho e = q sampling33 := by
  rintro ⟨e, he, hv⟩
  have := four_le_of_sampling33_isSolution hq he hv
  omega

theorem no_degree_three_formula_existsUnique :
    ∃ q : Config 2 2 → SamplingField,
      IsSolution samplingA samplingB samplingRho piThird piThird q ∧
      (∀ q', IsSolution samplingA samplingB samplingRho piThird piThird q' → q' = q) ∧
      ¬ ∃ e : Expr SamplingCoefficientField,
        DAdm samplingA samplingB samplingRho 3 e ∧
        Expr.eval samplingA samplingB samplingRho e = q sampling33 :=
  ⟨Rational.qOfDet sampling_detNeZero, Rational.qOfDet_isSolution sampling_detNeZero,
    fun _ hq => Rational.qOfDet_unique sampling_detNeZero hq,
    no_degree_three_formula_sampling33_isSolution (Rational.qOfDet_isSolution sampling_detNeZero)⟩

theorem piThird_nonneg (i : Fin 2) : 0 ≤ (piThird : Fin 2 → ℝ) i := by
  fin_cases i
  · change (0 : ℝ) ≤ 1 / 3
    norm_num
  · change (0 : ℝ) ≤ 2 / 3
    norm_num

theorem piThird_sum_univ : ∑ i, (piThird : Fin 2 → ℝ) i = 1 := by
  simp only [Fin.sum_univ_two, piThird, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem qProb_sampling33_on_slice {θ ρ : ℝ} (hθ : 1 < θ) (hρ : 0 ≤ ρ) :
    TwoLocusGenealogy.qProb 1 (θ - 1) ρ piThird piThird sampling33 =
      paramEval θ ρ numeratorP / paramEval θ ρ denominatorP :=
  sampling33_on_slice hθ hρ
    (TwoLocusGenealogy.qProb_isSolution one_pos (by linarith) hρ piThird_nonneg piThird_sum_univ
      piThird_nonneg piThird_sum_univ)

theorem no_degree_three_formula_qProb (ι : SamplingField →+* ℝ) (hB : 0 < ι samplingB)
    (hR : 0 ≤ ι samplingRho) :
    ¬ ∃ e : Expr SamplingCoefficientField,
      DAdm samplingA samplingB samplingRho 3 e ∧
      realEval ι samplingA samplingB samplingRho e =
        TwoLocusGenealogy.qProb 1 (ι samplingB) (ι samplingRho) piThird piThird sampling33 := by
  rintro ⟨e, he, hv⟩
  have hq := Rational.qOfDet_isSolution sampling_detNeZero
  have h2 : IsSolution 1 (ι samplingB) (ι samplingRho) piThird piThird
      (TwoLocusGenealogy.qProb 1 (ι samplingB) (ι samplingRho) piThird piThird) :=
    TwoLocusGenealogy.qProb_isSolution one_pos hB hR piThird_nonneg piThird_sum_univ
      piThird_nonneg piThird_sum_univ
  have h3 := congrFun (IsSolution.unique one_pos hB hR (sampling_isSolution_map ι hq) h2)
    sampling33
  refine no_degree_three_formula_sampling33_isSolution hq ⟨e, he, ringHom_injective_of_field ι ?_⟩
  rw [← realEval_eq, hv]
  exact h3.symm

end DegreeThree

section BlockTwoTwo

open BlockTwoSymbolic TwoGameteBridge KilledSystem

theorem no_degree_one_formula_block22_symbolic
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi),
      DAdm (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) 1 e ∧
      Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e =
        Q (toConfig s22) :=
  no_degree_one_formula_symbolic_general hQ

theorem no_degree_two_formula_block22_symbolic
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : IsSolution thAuπ thBuπ rhoUπ ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), DAdm thAuπ thBuπ rhoUπ 2 e ∧
      Expr.eval thAuπ thBuπ rhoUπ e = Q (toConfig s22) :=
  no_degree_two_formula_symbolic_general hQ

theorem no_degree_one_formula_total_block22_symbolic
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : IsSolution (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
      ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), GenericField.TotalDAdm
        SymbolicFrequencies.Kpi 1 e ∧
      Expr.eval (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) e =
        Q (toConfig s22) :=
  no_degree_one_formula_total_pi_coalescent (piBπ_of_isSolution hQ)

theorem no_degree_two_formula_total_block22_symbolic
    {Q : Config 2 2 → GenericField.L SymbolicFrequencies.Kpi}
    (hQ : IsSolution thAuπ thBuπ rhoUπ ![piAL, 1 - piAL] ![piBL, 1 - piBL] Q) :
    ¬ ∃ e : Expr (GenericField.Fuv SymbolicFrequencies.Kpi), TotalDAdmUπ 2 e ∧
      Expr.eval thAuπ thBuπ rhoUπ e = Q (toConfig s22) :=
  no_degree_two_formula_total_pi_coalescent (piB_of_isSolution hQ)

end BlockTwoTwo

section TotalDegree

variable {S : Type*} [CommRing S]

noncomputable def rateGenerators : Fin 3 → UniformPolynomial :=
  ![C uniformLambda, X - C uniformLambda, C (nestedConstant (RatFunc.X : UniformBase))]

noncomputable def rateEvalPoly (c : S →+* UniformCoefficient) :
    MvPolynomial (Fin 3) S →+* UniformPolynomial :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp c) rateGenerators

noncomputable def rateEval (c : S →+* UniformCoefficient) :
    MvPolynomial (Fin 3) S →+* UniformField :=
  (algebraMap UniformPolynomial UniformField).comp (rateEvalPoly c)

theorem rateEval_X_zero (c : S →+* UniformCoefficient) :
    rateEval c (MvPolynomial.X 0) = uniformA := by
  simp [rateEval, rateEvalPoly, rateGenerators, uniformA]

theorem rateEval_X_one (c : S →+* UniformCoefficient) :
    rateEval c (MvPolynomial.X 1) = uniformB := by
  simp [rateEval, rateEvalPoly, rateGenerators, uniformB]

theorem rateEval_X_two (c : S →+* UniformCoefficient) :
    rateEval c (MvPolynomial.X 2) = uniformRho := by
  simp [rateEval, rateEvalPoly, rateGenerators, uniformRho]

theorem rateGenerators_natDegree_le (i : Fin 3) : (rateGenerators i).natDegree ≤ 1 := by
  fin_cases i
  · simp [rateGenerators]
  · exact natDegree_X_sub_C_le uniformLambda
  · simp [rateGenerators]

theorem natDegree_rateEvalPoly_le (c : S →+* UniformCoefficient)
    (m : MvPolynomial (Fin 3) S) : (rateEvalPoly c m).natDegree ≤ m.totalDegree := by
  rw [rateEvalPoly, MvPolynomial.coe_eval₂Hom]
  exact GenericField.natDegree_eval₂_le _ (fun a => by simp) _ rateGenerators_natDegree_le m

inductive RateTotalDAdm (c : S →+* UniformCoefficient) (D : ℕ) :
    Expr UniformCoefficient → Prop
  | const (q : ℚ) : RateTotalDAdm c D (.const q)
  | coeff (x : UniformCoefficient) : RateTotalDAdm c D (.coeff x)
  | thA : RateTotalDAdm c D .thA
  | thB : RateTotalDAdm c D .thB
  | rho : RateTotalDAdm c D .rho
  | add {x y : Expr UniformCoefficient} :
      RateTotalDAdm c D x → RateTotalDAdm c D y → RateTotalDAdm c D (.add x y)
  | mul {x y : Expr UniformCoefficient} :
      RateTotalDAdm c D x → RateTotalDAdm c D y → RateTotalDAdm c D (.mul x y)
  | div {x g : Expr UniformCoefficient} (hx : RateTotalDAdm c D x) (hg : RateTotalDAdm c D g)
      (m : MvPolynomial (Fin 3) S) (hm : m.totalDegree ≤ D) (hne : rateEval c m ≠ 0)
      (hval : Expr.eval uniformA uniformB uniformRho g = rateEval c m) :
      RateTotalDAdm c D (.div x g)

theorem RateTotalDAdm.toDAdm {c : S →+* UniformCoefficient} {D : ℕ}
    {e : Expr UniformCoefficient} (h : RateTotalDAdm c D e) :
    DAdm uniformA uniformB uniformRho D e := by
  induction h with
  | const q => exact .const q
  | coeff x => exact .coeff x
  | thA => exact .thA
  | thB => exact .thB
  | rho => exact .rho
  | add _ _ ihx ihy => exact .add ihx ihy
  | mul _ _ ihx ihy => exact .mul ihx ihy
  | div _ _ m hm hne hval ihx ihg =>
      refine .div ihx ihg (rateEvalPoly c m) ?_
        (le_trans (natDegree_rateEvalPoly_le c m) hm) hval
      intro h0
      exact hne (by rw [rateEval, RingHom.comp_apply, h0, map_zero])

noncomputable def frequencyCoeff : MvPolynomial (Fin 2) ℚ →+* UniformCoefficient :=
  MvPolynomial.eval₂Hom (algebraMap ℚ UniformCoefficient)
    ![(RatFunc.X : UniformCoefficient), RatFunc.C RatFunc.X]

theorem frequencyCoeff_X_zero :
    algebraMap UniformPolynomial UniformField (C (frequencyCoeff (MvPolynomial.X 0))) =
      uniformP := by
  simp [frequencyCoeff, uniformP]

theorem frequencyCoeff_X_one :
    algebraMap UniformPolynomial UniformField (C (frequencyCoeff (MvPolynomial.X 1))) =
      uniformR := by
  simp [frequencyCoeff, uniformR]

theorem uniformB_ne_zero : uniformB ≠ 0 := by
  obtain ⟨ι, hι⟩ := exists_admissiblePoint
  intro h0
  have h := hι.thetaB_pos
  rw [h0, map_zero] at h
  exact lt_irrefl _ h

theorem rateTotalDAdm_div_thB {D : ℕ} (hD : 1 ≤ D) {x : Expr UniformCoefficient}
    (hx : RateTotalDAdm frequencyCoeff D x) :
    RateTotalDAdm frequencyCoeff D (.div x .thB) :=
  .div hx .thB (MvPolynomial.X 1) (by simpa using hD)
    (by rw [rateEval_X_one]; exact uniformB_ne_zero) (by rw [rateEval_X_one]; rfl)

theorem no_bounded_degree_formula_total_genericSolution (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Expr UniformCoefficient,
      RateTotalDAdm frequencyCoeff D e ∧
      Expr.eval uniformA uniformB uniformRho e = genericSolution (samplingMM m) := by
  obtain ⟨m, hm, h⟩ := no_bounded_degree_formula_genericSolution D
  exact ⟨m, hm, fun ⟨e, he, hv⟩ => h ⟨e, he.toDAdm, hv⟩⟩

theorem no_bounded_degree_formula_total_qProb (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ ι : UniformField →+* ℝ, IsAdmissiblePoint ι →
      ¬ ∃ e : Expr UniformCoefficient,
        RateTotalDAdm frequencyCoeff D e ∧
        realEval ι uniformA uniformB uniformRho e =
          TwoLocusGenealogy.qProb (ι uniformA) (ι uniformB) (ι uniformRho)
            (piOf (ι uniformP)) (piOf (ι uniformR)) (samplingMM m) := by
  obtain ⟨m, hm, h⟩ := no_bounded_degree_formula_qProb D
  exact ⟨m, hm, fun ι hι ⟨e, he, hv⟩ => h ι hι ⟨e, he.toDAdm, hv⟩⟩

end TotalDegree

end Rhone.Coalescent.NoBoundedDegreeFormula
