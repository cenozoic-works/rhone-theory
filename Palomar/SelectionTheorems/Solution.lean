module

public import Rhone.Statistics.Fisher
public import Rhone.Statistics.MultilevelPrice
public import Rhone.Statistics.LandeArnoldRegression
public import Rhone.MarkovChain.GeiringerConvergence

@[expose] public section

namespace Rhone.Palomar.SelectionTheorems

open Rhone.Dynamics MarkovChain Statistics MarkovChain.Geiringer Finset
open scoped BigOperators

theorem fisher_fundamental_theorem
    {G : Type*} [Fintype G] {L : Type*} {A : L → Type*} [∀ l, Fintype (A l)]
    [Fintype L] [Nonempty L]
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hW0 : ∀ g, 0 ≤ W g) (hbar : 0 < wMean P W)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) :
    fisherPartial P W X β = fisherAdditiveVar P W X β / wMean P W :=
  Rhone.Statistics.fisher_fundamental_theorem P W X β hp0 hp1 hW0 hbar hX0 hcopies hfit

theorem fisher_partial_nonneg
    {G : Type*} [Fintype G] {L : Type*} {A : L → Type*} [∀ l, Fintype (A l)]
    [Fintype L] [Nonempty L]
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hW0 : ∀ g, 0 ≤ W g) (hbar : 0 < wMean P W)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) : 0 ≤ fisherPartial P W X β :=
  Rhone.Statistics.fisher_partial_nonneg P W X β hp0 hp1 hW0 hbar hX0 hcopies hfit

section Multilevel

variable {G : Type*} [Fintype G] {J : G → Type*} [∀ g, Fintype (J g)]

theorem grouped_covariance_decomposition (p : G → ℝ) (q w z : ∀ g, J g → ℝ) :
    groupedMean p q (fun g i => w g i * z g i) -
      groupedMean p q w * groupedMean p q z =
    wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
      wMean p (fun g => wCov (q g) (w g) (z g)) :=
  Rhone.Statistics.grouped_covariance_decomposition p q w z

theorem multilevel_price_equation (p : G → ℝ) (q w z z' : ∀ g, J g → ℝ)
    (hw : groupedMean p q w ≠ 0) :
    groupedNextMean p q w z' - groupedMean p q z =
      (wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
        wMean p (fun g => wCov (q g) (w g) (z g)) +
        groupedMean p q (fun g i => w g i * (z' g i - z g i))) /
        groupedMean p q w :=
  Rhone.Statistics.multilevel_price_equation p q w z z' hw

end Multilevel

section Kin

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem hamilton_from_leastSquares (w z y : ι → ℝ) (β : Fin 3 → ℝ)
    (hw : 0 < popMean w) (hz : 0 < popCov z z)
    (hfit : IsFisherLeastSquares kinParentWeight w (kinSocialDesign z y) β) :
    nextMean w z - popMean z = popCov z z * (β 2 * relatedness y z + β 1) / popMean w ∧
    (0 < nextMean w z - popMean z ↔ 0 < β 2 * relatedness y z + β 1) :=
  Rhone.Statistics.hamilton_from_leastSquares w z y β hw hz hfit

end Kin

section LandeArnold

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

theorem lande_arnold_gradient_exists [DecidableEq κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (hw : 0 < popMean w)
    (hdet : Matrix.det (phenotypeCovariance z) ≠ 0) :
    ∃ γ : Option κ → ℝ,
      IsFisherLeastSquares kinParentWeight (landeArnoldRelativeFitness w)
      (landeArnoldDesign z) γ ∧
      γ none = 1 ∧ (fun j => γ (some j)) =
        Matrix.mulVec (phenotypeCovariance z : Matrix κ κ ℝ)⁻¹
          (fun j => selectionDifferential w (fun i => z i j)) :=
  Rhone.Statistics.lande_arnold_gradient_exists w z hw hdet

end LandeArnold

theorem geiringer_recombination_converges
    {κ Ω : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j) :
    Filter.Tendsto (fun t : ℕ => (recombination ρ)^[t] p) Filter.atTop
      (nhds (fun h => ∏ l, marginal p {l} h)) :=
  Rhone.MarkovChain.Geiringer.geiringer_recombination_converges ρ p hρ0 hρ hp0 hp hsep

end Rhone.Palomar.SelectionTheorems
