module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Rhone.Dynamics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

def wMean (p f : ι → F) : F := ∑ i, p i * f i

def wCov (p f g : ι → F) : F := wMean p (fun i => f i * g i) - wMean p f * wMean p g

def haploidStep (p w : ι → F) : ι → F := fun i => p i * w i / wMean p w

end Rhone.Dynamics

clear_aux_proof_cache

namespace Rhone.Statistics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

def popMean (f : ι → F) : F := (∑ i, f i) / (Fintype.card ι : F)

def popCov (f g : ι → F) : F := popMean (fun i => f i * g i) - popMean f * popMean g

def nextMean (w z' : ι → F) : F := popMean (fun i => w i * z' i) / popMean w

def selectionDifferential (w m : ι → F) : F := nextMean w m - popMean m

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.Statistics
open Rhone.Dynamics

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def relatedness (y z : ι → ℝ) : ℝ := popCov y z / popCov z z

noncomputable def kinParentWeight (_i : ι) : ℝ := 1 / (Fintype.card ι)

noncomputable def kinSocialDesign (z y : ι → ℝ) (i : ι) : Fin 3 → ℝ := ![1,z i,y i]

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {G K : Type*} [Fintype G] [Fintype K]

noncomputable def fisherScore (X : G → K → ℝ) (β : K → ℝ) (g : G) : ℝ :=
  ∑ k, X g k * β k

noncomputable def fisherLoss (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  wMean P (fun g => (W g - fisherScore X β g) ^ 2)

def IsFisherLeastSquares (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : Prop :=
  ∀ γ, fisherLoss P W X β ≤ fisherLoss P W X γ

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {G K : Type*} [Fintype G]

noncomputable def fisherAlleleFreq [Fintype K]
    (P : G → ℝ) (X : G → K → ℝ) (k : K) : ℝ :=
  wMean P (fun g => X g k) / 2

variable [Fintype K]

noncomputable def fisherSelectedAlleleFreq
    (P W : G → ℝ) (X : G → K → ℝ) (k : K) : ℝ :=
  fisherAlleleFreq (haploidStep P W) X k

noncomputable def fisherAdditiveVar
    (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  wMean P (fun g => (fisherScore X β g - wMean P W) ^ 2)

noncomputable def fisherPartial
    (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  2 * ∑ k, (fisherSelectedAlleleFreq P W X k - fisherAlleleFreq P X k) * β k

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators

noncomputable def phenotypeCovariance {ι κ : Type*} [Fintype ι]
    (z : ι → κ → ℝ) (j k : κ) : ℝ :=
  popCov (fun i => z i j) (fun i => z i k)

clear_aux_proof_cache

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

noncomputable def landeArnoldRelativeFitness (w : ι → ℝ) (i : ι) : ℝ :=
  w i / popMean w

noncomputable def landeArnoldDesign (z : ι → κ → ℝ) (i : ι) : Option κ → ℝ
  | none => 1
  | some j => z i j - popMean (fun i => z i j)

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.Statistics
open Rhone.Dynamics Finset

variable {G : Type*} [Fintype G] {J : G → Type*} [∀ g, Fintype (J g)]

noncomputable def groupedMean (p : G → ℝ) (q z : ∀ g, J g → ℝ) : ℝ :=
  wMean p (fun g => wMean (q g) (z g))

noncomputable def groupedNextMean (p : G → ℝ) (q w z' : ∀ g, J g → ℝ) : ℝ :=
  groupedMean p q (fun g i => w g i * z' g i) / groupedMean p q w

end Rhone.Statistics

clear_aux_proof_cache

namespace Rhone.MarkovChain.Geiringer
open Finset

noncomputable def assemble {κ Ω : Type*} [DecidableEq κ]
    (mask : Finset κ) (p q : κ → Ω) (l : κ) : Ω :=
  if l ∈ mask then p l else q l

noncomputable def recombination {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ) (h : κ → Ω) : ℝ :=
  ∑ mask, ρ mask * ∑ parent, ∑ other,
    p parent * p other * (if assemble mask parent other = h then 1 else 0)

noncomputable def marginal {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (p : (κ → Ω) → ℝ) (B : Finset κ) (h : κ → Ω) : ℝ :=
  ∑ other, p other * (if ∀ l ∈ B, other l = h l then 1 else 0)

noncomputable def separationProbability {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (i j : κ) : ℝ :=
  ∑ mask, ρ mask * (if (i ∈ mask ∧ j ∉ mask) ∨ (i ∉ mask ∧ j ∈ mask) then 1 else 0)

end Rhone.MarkovChain.Geiringer

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
    fisherPartial P W X β = fisherAdditiveVar P W X β / wMean P W := by
  sorry

theorem fisher_partial_nonneg
    {G : Type*} [Fintype G] {L : Type*} {A : L → Type*} [∀ l, Fintype (A l)]
    [Fintype L] [Nonempty L]
    (P W : G → ℝ) (X : G → (Σ l, A l) → ℝ) (β : (Σ l, A l) → ℝ)
    (hp0 : ∀ g, 0 ≤ P g) (hp1 : ∑ g, P g = 1)
    (hW0 : ∀ g, 0 ≤ W g) (hbar : 0 < wMean P W)
    (hX0 : ∀ g k, 0 ≤ X g k)
    (hcopies : ∀ g l, ∑ a, X g ⟨l, a⟩ = 2)
    (hfit : IsFisherLeastSquares P W X β) : 0 ≤ fisherPartial P W X β := by
  sorry

section Multilevel

variable {G : Type*} [Fintype G] {J : G → Type*} [∀ g, Fintype (J g)]

theorem grouped_covariance_decomposition (p : G → ℝ) (q w z : ∀ g, J g → ℝ) :
    groupedMean p q (fun g i => w g i * z g i) -
      groupedMean p q w * groupedMean p q z =
    wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
      wMean p (fun g => wCov (q g) (w g) (z g)) := by
  sorry

theorem multilevel_price_equation (p : G → ℝ) (q w z z' : ∀ g, J g → ℝ)
    (hw : groupedMean p q w ≠ 0) :
    groupedNextMean p q w z' - groupedMean p q z =
      (wCov p (fun g => wMean (q g) (w g)) (fun g => wMean (q g) (z g)) +
        wMean p (fun g => wCov (q g) (w g) (z g)) +
        groupedMean p q (fun g i => w g i * (z' g i - z g i))) /
        groupedMean p q w := by
  sorry

end Multilevel

section Kin

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem hamilton_from_leastSquares (w z y : ι → ℝ) (β : Fin 3 → ℝ)
    (hw : 0 < popMean w) (hz : 0 < popCov z z)
    (hfit : IsFisherLeastSquares kinParentWeight w (kinSocialDesign z y) β) :
    nextMean w z - popMean z = popCov z z * (β 2 * relatedness y z + β 1) / popMean w ∧
    (0 < nextMean w z - popMean z ↔ 0 < β 2 * relatedness y z + β 1) := by
  sorry

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
          (fun j => selectionDifferential w (fun i => z i j)) := by
  sorry

end LandeArnold

theorem geiringer_recombination_converges
    {κ Ω : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (ρ : Finset κ → ℝ) (p : (κ → Ω) → ℝ)
    (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hp0 : ∀ h, 0 ≤ p h) (hp : ∑ h, p h = 1)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j) :
    Filter.Tendsto (fun t : ℕ => (recombination ρ)^[t] p) Filter.atTop
      (nhds (fun h => ∏ l, marginal p {l} h)) := by
  sorry

end Rhone.Palomar.SelectionTheorems
