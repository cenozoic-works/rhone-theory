module

public import Rhone.MarkovChain.WrightFisherSpectrum
public import Rhone.Dynamics.MutationStepwise
public import Rhone.MarkovChain.MoranMutationStationary

@[expose] public section

namespace Rhone.Palomar.FiniteChains

open MarkovChain Rhone.Dynamics

theorem wf_charpoly (N : ℕ) :
  Matrix.charpoly (wf N) =
    ∏ k : Fin (N + 1), (Polynomial.X - Polynomial.C (wfEigenvalue N k)) :=
  Rhone.MarkovChain.wf_charpoly N

theorem integer_stepwise_no_stationary (u : ℝ) (hu : 0 < u)
    (p : ℤ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (hbalance : ∀ n, p n = (1 - u) * p n + (u / 2) * p (n - 1) + (u / 2) * p (n + 1)) :
    False :=
  Rhone.Dynamics.MutationModels.integer_stepwise_no_stationary u hu p hp hsum hbalance

theorem moran_mutation_stationary {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (j : Fin (N + 1)) :
    ∑ i, moranMutationLaw N u i * moranMutationRow N u i j = moranMutationLaw N u j :=
  Rhone.MarkovChain.moran_mutation_stationary hN hu0 hu1 j

theorem moran_mutation_probability {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i, 0 ≤ moranMutationLaw N u i) ∧ ∑ i, moranMutationLaw N u i = 1 :=
  Rhone.MarkovChain.moran_mutation_probability hN hu0 hu1

theorem moran_mutation_markov {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i j, 0 ≤ moranMutationRow N u i j) ∧
    (∀ i, ∑ j, moranMutationRow N u i j = 1) :=
  Rhone.MarkovChain.moran_mutation_markov hN hu0 hu1

end Rhone.Palomar.FiniteChains
