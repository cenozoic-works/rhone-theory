module

public import Rhone.Diffusion.WrightFisherGeneratorLimit
public import Rhone.Diffusion.WrightFisherGeneratorLimitForces
public import Rhone.Dynamics.MutationSelection

@[expose] public section

namespace Rhone.Palomar.WrightFisherGeneratorLimit

open Finset Filter Topology Diffusion MarkovChain Analysis

theorem wf_eq_binomial (N : ℕ) (i j : Fin (N + 1)) :
    wf N i j =
      (N.choose j : ℝ) * ((i : ℝ) / N) ^ (j : ℕ) * (1 - (i : ℝ) / N) ^ (N - (j : ℕ)) :=
  rfl

theorem wf_nonneg_and_row_sum (N : ℕ) :
    (∀ i j, 0 ≤ wf N i j) ∧ ∀ i, ∑ j, wf N i j = 1 :=
  Rhone.MarkovChain.wf_isStochastic N

theorem wfChain_expect_eq (N : ℕ) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (wfChain N).expect f i = ∑ j, wf N i j * f j :=
  rfl

theorem wfDiploid_eq_wf (N : ℕ) : wfDiploid N = wf (2 * N) :=
  Rhone.MarkovChain.wfDiploid_eq_haploid N

theorem wfChain_generatorError_eq (f : ℝ → ℝ) (N : ℕ) (i : Fin (N + 1)) :
    generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
        (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator f N i =
      (N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * deriv (deriv f) ((i : ℝ) / N) :=
  rfl

theorem hapMutSelStep_eq (s μ x : ℝ) :
    Rhone.Dynamics.hapMutSelStep s μ x = μ + (1 - μ) * (x * (1 - s) / (1 - s * x)) :=
  rfl

theorem wf_expect_freq_sub {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => (j : ℝ) / N - (i : ℝ) / N) i = 0 :=
  Rhone.MarkovChain.wf_expect_freq_sub hN i

theorem wf_expect_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) / N :=
  Rhone.MarkovChain.wf_expect_freq_sub_sq hN i

theorem wf_expect_freq_sub_cube {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 3) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) * (1 - 2 * ((i : ℝ) / N)) / (N : ℝ) ^ 2 :=
  Rhone.MarkovChain.wf_expect_freq_sub_cube hN i

theorem wf_expect_freq_sub_pow_four {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N)
        * (1 + 3 * ((N : ℝ) - 2) * ((i : ℝ) / N) * (1 - (i : ℝ) / N)) / (N : ℝ) ^ 3 :=
  Rhone.MarkovChain.wf_expect_freq_sub_pow_four hN i

theorem wf_expect_freq_sub_pow_four_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i ≤ 3 / (16 * (N : ℝ) ^ 2) :=
  Rhone.MarkovChain.wf_expect_freq_sub_pow_four_le hN i

theorem wf_expect_abs_freq_sub_cube_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => |(j : ℝ) / N - (i : ℝ) / N| ^ 3) i ≤
      7 / (32 * (N * √(N : ℝ))) :=
  Rhone.MarkovChain.wf_expect_abs_freq_sub_cube_le hN i

theorem wf_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |(N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * f'' ((i : ℝ) / N)|
      ≤ 7 * L / (192 * √(N : ℝ)) :=
  Rhone.Diffusion.wf_generator_error_le hf hf' hL hN i

theorem wfDiploid_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (2 * N + 1)) :
    |((2 * N : ℕ) : ℝ) * ((wfDiploid N).expect (fun j => f ((j : ℝ) / (2 * N : ℕ))) i
          - f ((i : ℝ) / (2 * N : ℕ)))
        - (i : ℝ) / (2 * N : ℕ) * (1 - (i : ℝ) / (2 * N : ℕ)) / 2
          * f'' ((i : ℝ) / (2 * N : ℕ))|
      ≤ 7 * L / (192 * √((2 * N : ℕ) : ℝ)) :=
  Rhone.Diffusion.wfDiploid_generator_error_le hf hf' hL hN i

theorem wfChain_generatorError_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (deriv f)) x| ≤ M)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
        (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator f N i| ≤ 7 * M / (192 * √(N : ℝ)) :=
  Rhone.Diffusion.wfChain_generatorError_le hf hM hN i

theorem wf_generatorLimit :
    GeneratorLimit (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
      (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator {f | ContDiff ℝ 3 f} :=
  Rhone.Diffusion.wf_generatorLimit

theorem wf_generator_eventually_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin (N + 1),
      |(N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * deriv (deriv f) ((i : ℝ) / N)| ≤ ε := by
  filter_upwards [Rhone.Diffusion.wf_generatorLimit.eventually_le
    (f := f) (show f ∈ {f | ContDiff ℝ 3 f} from hf) hε] with N h i
  exact h i

theorem sum_binomRow_freq_sub {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) = q - x :=
  Rhone.Diffusion.sum_binomRow_freq_sub hN q x

theorem sum_binomRow_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) ^ 2 =
      q * (1 - q) / N + (q - x) ^ 2 :=
  Rhone.Diffusion.sum_binomRow_freq_sub_sq hN q x

theorem hapMutSel_drift_error_le {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {N : ℕ} (hN : 2 * σ ≤ N) (hN1 : 1 ≤ N) :
    |(N : ℝ) * (∑ j ∈ range (N + 1),
          binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
            * ((j : ℝ) / N - x))
        - (1 - x) * (ν - σ * x)| ≤ 2 * σ * (ν + σ) / N :=
  Rhone.Diffusion.hapMutSel_drift_error_le hσ hν hx hN hN1

theorem hapMutSel_drift_tendsto {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => (N : ℝ) * (∑ j ∈ range (N + 1),
        binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
          * ((j : ℝ) / N - x)))
      atTop (𝓝 ((1 - x) * (ν - σ * x))) :=
  Rhone.Diffusion.hapMutSel_drift_tendsto hσ hν hx

end Rhone.Palomar.WrightFisherGeneratorLimit
