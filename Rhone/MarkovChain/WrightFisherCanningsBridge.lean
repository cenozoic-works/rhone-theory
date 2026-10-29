/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisherCannings
public import Rhone.MarkovChain.CanningsCountChain

/-!
# The uniform-parent Cannings model has the Wright–Fisher count chain

Source: cannings1974, sec. 3.1, pp. 268–269. -/

@[expose] public section
namespace Rhone.MarkovChain

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfModel_countKernel (N : ℕ) : (wfModel N).countKernel = wf N := by
  classical
  funext i j
  have h := wfModel_count_law N
    (Finset.univ.filter (fun k : Fin N => k.val < i.val)) j.val
  have hc : (Finset.univ.filter (fun k : Fin N => k.val < i.val)).card = i.val := by
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]
  change (∑ ω : Fin N → Fin N,
    if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val),
      wfOffspring N ω k) = j.val then (wfModel N).w ω else 0) =
    binomRow N ((i.val : ℝ) / N) j.val
  simpa only [hc] using h

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfModel_countChain (N : ℕ) : (wfModel N).countChain = wfChain N := by
  have hext : ∀ (C D : Rhone.MarkovChain.FinChain (Fin (N + 1))), C.P = D.P → C = D := by
    intro C D h
    cases C
    cases D
    cases h
    rfl
  apply hext
  exact wfModel_countKernel N

end Rhone.MarkovChain
