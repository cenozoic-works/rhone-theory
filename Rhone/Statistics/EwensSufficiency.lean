/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.Ewens

/-!
# Sufficiency of the number of alleles

Source: ewens1972, eq. (29)–(30), pp. 100–102; durrett2008, Thm 1.13, eq. (1.14). -/

@[expose] public section
namespace Rhone.Statistics
open Finset Polynomial Rhone.Combinatorics Probability

/-- Source: ewens1972, eq. (29)–(30), pp. 100–102; durrett2008, Thm 1.13, eq. (1.14). -/
theorem esf_conditional_card {n : ℕ} {θ : ℚ} (hθ : 0 < θ)
    (p : Nat.Partition n) :
    esf θ p /
        (∑ q ∈ (Finset.univ : Finset (Nat.Partition n)).filter
          (fun q => q.parts.card = p.parts.card), esf θ q) =
      (n.factorial : ℚ) * partWeight ℚ p.parts /
        (Nat.stirlingFirst n p.parts.card : ℚ) := by
  rw [sum_esf_card]
  have hP : (ascPochhammer ℚ n).eval θ ≠ 0 := (ascPochhammer_pos n θ hθ).ne'
  have hpow : θ ^ p.parts.card ≠ 0 := pow_ne_zero _ hθ.ne'
  unfold esf
  by_cases hs : (Nat.stirlingFirst n p.parts.card : ℚ) = 0
  · simp [hs]
  · field_simp

end Rhone.Statistics
