/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.Relatives
public import Rhone.Probability.FiniteProductMoments
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field

/-!
# Relative covariance under independent locus inheritance

Source: kempthorne1954, pp. 110–113. -/

@[expose] public section
namespace Rhone.Statistics

/--
Source: kempthorne1954, pp. 110–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
inductive RelativeKind | parentOffspring | halfSib | fullSib

/-- Source: kempthorne1954, p. 105; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def hwProbability (p : ℝ) : Fin 3 → ℝ := ![(1-p)^2,2*p*(1-p),p^2]

/--
Source: kempthorne1954, pp. 110–111; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def sharedJoint (p : ℝ) (pair : Fin 3 × Fin 3) : ℝ :=
  (1-p) * (![1-p,p,0] pair.1) * (![1-p,p,0] pair.2) +
  p * (![0,1-p,p] pair.1) * (![0,1-p,p] pair.2)

/--
Source: kempthorne1954, pp. 110–111; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def relativeJoint (kind : RelativeKind) (p : ℝ)
    (pair : Fin 3 × Fin 3) : ℝ :=
  match kind with
  | .parentOffspring => sharedJoint p pair
  | .halfSib => (hwProbability p pair.1 * hwProbability p pair.2 + sharedJoint p pair)/2
  | .fullSib => (hwProbability p pair.1 * hwProbability p pair.2 + 2*sharedJoint p pair +
      if pair.1 = pair.2 then hwProbability p pair.1 else 0)/4

/-- Source: kempthorne1954, p. 111; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def productRelativeMean {κ : Type*} [Fintype κ]
    (kind : RelativeKind) (p : κ → ℝ) (f : (κ → Fin 3 × Fin 3) → ℝ) : ℝ :=
by
  classical
  exact ∑ ω, (∏ j, relativeJoint kind (p j) (ω j)) * f ω

/-- Source: kempthorne1954, p. 111; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
noncomputable def productRelativeCov {κ : Type*} [Fintype κ]
    (kind : RelativeKind) (p : κ → ℝ) (f g : (κ → Fin 3 × Fin 3) → ℝ) : ℝ :=
  productRelativeMean kind p (fun ω => f ω * g ω) -
    productRelativeMean kind p f * productRelativeMean kind p g

/-- Source: fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq. (IX-51), p. 428. -/
private theorem relative_joint_nonneg (kind : RelativeKind) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (pair : Fin 3 × Fin 3) :
    0 ≤ relativeJoint kind p pair := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  rcases pair with ⟨i,j⟩
  cases kind <;> fin_cases i <;> fin_cases j <;>
    dsimp [relativeJoint, sharedJoint, hwProbability] <;> positivity

/-- Source: fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq. (IX-51), p. 428. -/
private theorem relative_joint_total (kind : RelativeKind) (p : ℝ) :
    ∑ pair, relativeJoint kind p pair = 1 := by
  cases kind <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three,
    relativeJoint, sharedJoint, hwProbability] <;> ring

/-- Source: fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq. (IX-51), p. 428. -/
private theorem relative_joint_first_marginal (kind : RelativeKind) (p : ℝ) (i : Fin 3) :
    ∑ j, relativeJoint kind p (i,j) = hwProbability p i := by
  cases kind <;> fin_cases i <;> simp [Fin.sum_univ_three,
    relativeJoint, sharedJoint, hwProbability] <;> ring

/-- Source: fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq. (IX-51), p. 428. -/
private theorem relative_joint_second_marginal (kind : RelativeKind) (p : ℝ) (j : Fin 3) :
    ∑ i, relativeJoint kind p (i,j) = hwProbability p j := by
  cases kind <;> fin_cases j <;> simp [Fin.sum_univ_three,
    relativeJoint, sharedJoint, hwProbability] <;> ring

/-- Source: kempthorne1954, p. 112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
private theorem relative_joint_covariance (kind : RelativeKind) (p : ℝ) (G : Fin 3 → ℝ) :
    (∑ pair, relativeJoint kind p pair * (G pair.1 * G pair.2)) -
      (∑ pair, relativeJoint kind p pair * G pair.1) *
      (∑ pair, relativeJoint kind p pair * G pair.2) =
      match kind with
      | .parentOffspring => parentOffspringCov p G
      | .halfSib => halfSibCov p G
      | .fullSib => fullSibCov p G := by
  cases kind <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three,
    relativeJoint, sharedJoint, hwProbability, parentOffspringCov, halfSibCov,
    fullSibCov, sharedAlleleCov, sharedAlleleProduct, genoMean, hwExp] <;> ring

/--
Source: kempthorne1954, pp. 110–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
theorem independent_locus_parent_offspring_covariance_general
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (G : κ → Fin 3 → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    productRelativeCov .parentOffspring p
      (fun ω => ∑ j, G j (ω j).1) (fun ω => ∑ j, G j (ω j).2) =
      (∑ j, varA (p j) (G j))/2 := by
  classical
  change Rhone.Probability.FiniteProductMoments.cov
    (fun j => relativeJoint .parentOffspring (p j)) _ _ = _
  rw [Rhone.Probability.FiniteProductMoments.cov_additive
    (fun j => relativeJoint _ (p j))
    (fun j pair => G j pair.1) (fun j pair => G j pair.2)
    (fun j => relative_joint_total .parentOffspring (p j))]
  simp_rw [relative_joint_covariance]
  simp only [parent_offspring_covariance _ _ (hp0 _) (hp1 _), Finset.sum_div]

/--
Source: kempthorne1954, pp. 110–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
theorem independent_locus_half_sib_covariance_general
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (G : κ → Fin 3 → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    productRelativeCov .halfSib p
      (fun ω => ∑ j, G j (ω j).1) (fun ω => ∑ j, G j (ω j).2) =
      (∑ j, varA (p j) (G j))/4 := by
  classical
  change Rhone.Probability.FiniteProductMoments.cov
    (fun j => relativeJoint .halfSib (p j)) _ _ = _
  rw [Rhone.Probability.FiniteProductMoments.cov_additive
    (fun j => relativeJoint _ (p j))
    (fun j pair => G j pair.1) (fun j pair => G j pair.2)
    (fun j => relative_joint_total .halfSib (p j))]
  simp_rw [relative_joint_covariance]
  simp only [half_sib_covariance _ _ (hp0 _) (hp1 _), Finset.sum_div]

/--
Source: kempthorne1954, pp. 110–112; fisher1918, pp. 405–406; felsenstein_teg2019, sec. IX.5, eq.
(IX-51), p. 428. -/
theorem independent_locus_full_sib_covariance_general
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (G : κ → Fin 3 → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) :
    productRelativeCov .fullSib p
      (fun ω => ∑ j, G j (ω j).1) (fun ω => ∑ j, G j (ω j).2) =
      (∑ j, varA (p j) (G j))/2 + (∑ j, varD (p j) (G j))/4 := by
  classical
  change Rhone.Probability.FiniteProductMoments.cov
    (fun j => relativeJoint .fullSib (p j)) _ _ = _
  rw [Rhone.Probability.FiniteProductMoments.cov_additive
    (fun j => relativeJoint _ (p j))
    (fun j pair => G j pair.1) (fun j pair => G j pair.2)
    (fun j => relative_joint_total .fullSib (p j))]
  simp_rw [relative_joint_covariance]
  simp only [full_sib_covariance _ _ (hp0 _) (hp1 _), Finset.sum_div,
    Finset.sum_add_distrib]

end Rhone.Statistics
