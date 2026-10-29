module

public import Rhone.Statistics.EwensUrn

@[expose] public section

namespace Rhone.Palomar.EwensUrn

open Probability Statistics Rhone.Combinatorics Finset Polynomial

section Formula

variable {F : Type*} [Field F]

theorem sum_esf [CharZero F] (θ : F) (n : ℕ) (h : (ascPochhammer F n).eval θ ≠ 0) :
    ∑ p : Nat.Partition n, esf θ p = 1 :=
  Rhone.Probability.sum_esf θ n h

theorem esf_eq_prod (θ : F) {n : ℕ} (p : Nat.Partition n) :
    esf θ p = (n.factorial : F) / (ascPochhammer F n).eval θ *
      ∏ j ∈ Icc 1 n, (θ / j) ^ p.parts.count j / (p.parts.count j).factorial :=
  Rhone.Probability.esf_eq_prod θ p

end Formula

theorem ewensUrnLaw_apply (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (p : Nat.Partition n) :
    ewensUrnLaw θ hθ n p = ENNReal.ofReal (esf θ p) :=
  Rhone.Statistics.ewensUrnLaw_apply θ hθ n p

theorem esf_conditional_card_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (p : Nat.Partition n) :
    esf θ p /
        (∑ q ∈ (Finset.univ : Finset (Nat.Partition n)).filter
          (fun q => q.parts.card = p.parts.card), esf θ q) =
      (n.factorial : ℝ) * partWeight ℝ p.parts /
        (Nat.stirlingFirst n p.parts.card : ℝ) :=
  Rhone.Statistics.esf_conditional_card_real hθ p

theorem esf_deletion_consistent_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) :
    ∑ p : Nat.Partition (n + 1), esf θ p * (deletionWeight p q : ℝ) = esf θ q :=
  Rhone.Statistics.esf_deletion_consistent_real hθ q

end Rhone.Palomar.EwensUrn
