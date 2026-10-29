/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AsymmetricPairDesign.Observation

/-! # Three-stratum obstruction: no common observed law for the asymmetric source -/

@[expose] public section

namespace Rhone.Statistics.AsymmetricPairDesign
open PairObservationChannel DependenceBudget
variable {K : ℕ} {H : Type*} [Fintype H]

theorem reportedPairLaw_separation (E : Channel K H) (_hK : 2 ≤ K) (hE : Informative E)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 < k) :
    reportedPairLaw E ha hb hc hd hk.le 1 ≠ reportedPairLaw E ha hb hc hd hk.le 0 ∨
      reportedPairLaw E ha hb hc hd hk.le 1 ≠ reportedPairLaw E ha hb hc hd hk.le 2 := by
  have hinj : ∀ i j : Fin 3,
      reportedPairLaw E ha hb hc hd hk.le i = reportedPairLaw E ha hb hc hd hk.le j →
      laplace a b c d k i = laplace a b c d k j := by
    intro i j hij
    apply informative_agreement_injective E hE
    apply Finset.sum_congr rfl
    intro y _
    exact congrArg (fun P : Law (H × H) => P.mass (y, y)) hij
  rcases laplace_separation ha hb hc hd hk with h | h
  · exact Or.inl (fun he => h.ne (hinj 1 0 he))
  · exact Or.inr (fun he => h.ne (hinj 1 2 he))

theorem reportedPairLaw_no_common_law (E : Channel K H) (hK : 2 ≤ K) (hE : Informative E)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 < k) :
    ¬ ∃ Q : Law (H × H), ∀ i : Fin 3, reportedPairLaw E ha hb hc hd hk.le i = Q := by
  rintro ⟨Q, hQ⟩
  rcases reportedPairLaw_separation E hK hE ha hb hc hd hk with h | h
  · exact h ((hQ 1).trans (hQ 0).symm)
  · exact h ((hQ 1).trans (hQ 2).symm)

theorem maximum_laplace_gap {a b c d k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    k * laplace a b c d k 1 / (a + b) ≤
      max (laplace a b c d k 0 - laplace a b c d k 1)
        (laplace a b c d k 2 - laplace a b c d k 1) := by
  exact maximum_gap ha hb (laplace_balance ha hb hc hd hk.le)

end Rhone.Statistics.AsymmetricPairDesign
