module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Rhone.MarkovChain

abbrev CountKernel (N : ℕ) : Type := Fin (N + 1) → Fin (N + 1) → ℝ

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.MarkovChain

open Finset

def binomRow (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

noncomputable def wfRow (N i j : ℕ) : ℝ := binomRow N ((i : ℝ) / N) j

noncomputable def wf (N : ℕ) : CountKernel N := fun i j => wfRow N i j

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.MarkovChain
open Finset
open scoped Matrix

noncomputable def wfEigenvalue (N k : ℕ) : ℝ :=
  (N.descFactorial k : ℝ) / (N : ℝ)^k

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.MarkovChain
open scoped BigOperators

noncomputable def moranMutationUp (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ((1 - u) * (i : ℝ) + u * ((N : ℝ) - i)) * ((N : ℝ) - i) / (N : ℝ) ^ 2

noncomputable def moranMutationDown (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ((1 - u) * ((N : ℝ) - i) + u * (i : ℝ)) * (i : ℝ) / (N : ℝ) ^ 2

noncomputable def moranMutationRow (N : ℕ) (u : ℝ) (i j : Fin (N + 1)) : ℝ :=
  (if j = i then 1 - moranMutationUp N u i - moranMutationDown N u i else 0) +
  (if j.val = i.val + 1 then moranMutationUp N u i else 0) +
  (if i.val = j.val + 1 then moranMutationDown N u i else 0)

noncomputable def moranMutationWeight (N : ℕ) (u : ℝ) (i : ℕ) : ℝ :=
  ∏ k ∈ Finset.range i, moranMutationUp N u k / moranMutationDown N u (k + 1)

noncomputable def moranMutationLaw (N : ℕ) (u : ℝ) (i : Fin (N + 1)) : ℝ :=
  moranMutationWeight N u i / (∑ j : Fin (N + 1), moranMutationWeight N u j)

end Rhone.MarkovChain

namespace Rhone.Palomar.FiniteChains

open MarkovChain

theorem wf_charpoly (N : ℕ) :
  Matrix.charpoly (wf N) =
    ∏ k : Fin (N + 1), (Polynomial.X - Polynomial.C (wfEigenvalue N k)) := by
  sorry

theorem integer_stepwise_no_stationary (u : ℝ) (hu : 0 < u)
    (p : ℤ → ℝ) (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (hbalance : ∀ n, p n = (1 - u) * p n + (u / 2) * p (n - 1) + (u / 2) * p (n + 1)) :
    False := by
  sorry

theorem moran_mutation_stationary {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) (j : Fin (N + 1)) :
    ∑ i, moranMutationLaw N u i * moranMutationRow N u i j = moranMutationLaw N u j := by
  sorry

theorem moran_mutation_probability {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i, 0 ≤ moranMutationLaw N u i) ∧ ∑ i, moranMutationLaw N u i = 1 := by
  sorry

theorem moran_mutation_markov {N : ℕ} {u : ℝ}
    (hN : 0 < N) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ i j, 0 ≤ moranMutationRow N u i j) ∧
    (∀ i, ∑ j, moranMutationRow N u i j = 1) := by
  sorry

end Rhone.Palomar.FiniteChains
