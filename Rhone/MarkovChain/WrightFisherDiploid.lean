/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisher

/-!
# Diploid Wright–Fisher allele counts

Source: ewens2004, sec. 3.2. -/

@[expose] public section

namespace Rhone.MarkovChain

/-- Source: ewens2004, sec. 3.2. -/
noncomputable def wfDiploid (N : ℕ) : CountKernel (2 * N) := wf (2 * N)

/-- Source: ewens2004, sec. 3.2. -/
theorem wfDiploid_eq_haploid (N : ℕ) : wfDiploid N = wf (2 * N) := rfl

/-- Source: ewens2004, sec. 3.2. -/
theorem wfDiploid_isStochastic (N : ℕ) : (wfDiploid N).IsStochastic :=
  wf_isStochastic (2 * N)

/-- Source: ewens2004, sec. 3.2. -/
theorem wfDiploid_expect_id (N : ℕ) (i : Fin (2 * N + 1)) :
    (wfDiploid N).expect (fun j => (j : ℝ)) i = i := wf_expect_id (2 * N) i

/-- Source: ewens2004, sec. 3.2. -/
theorem wfDiploid_variance (N : ℕ) (i : Fin (2 * N + 1)) :
    (wfDiploid N).expect (fun j => ((j : ℝ) - i) ^ 2) i =
      (2 * N : ℕ) * ((i : ℝ) / (2 * N : ℕ)) *
        (1 - (i : ℝ) / (2 * N : ℕ)) := wf_variance (2 * N) i

end Rhone.MarkovChain
