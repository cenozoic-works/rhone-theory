/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Cannings
public import Rhone.MarkovChain.WrightFisherMultialleleSubset

/-!
# Wright–Fisher as a concrete Cannings model

Source: cannings1974, sec. 3.1, pp. 268–269; ewens2004, sec. 3.3. -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
noncomputable def wfOffspring (N : ℕ) (ω : Fin N → Fin N) (k : Fin N) : ℕ :=
  (Finset.univ.filter (fun t => ω t = k)).card

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
noncomputable def wfModel (N : ℕ) : CanningsModel N (Fin N → Fin N) where
  w := fun _ => 1 / (N : ℝ) ^ N
  ν := wfOffspring N
  w_nonneg := fun _ => by positivity
  sum_w := by
    have hden : (N : ℝ) ^ N ≠ 0 := by
      by_cases hN : N = 0
      · simp [hN]
      · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hN)
    simp [nsmul_eq_mul, Nat.cast_pow, hden]
  sum_ν := fun ω => (wfAlleleAllocationCounts N N ω).sum
  exchangeable := by
    classical
    intro σ f
    let e : (Fin N → Fin N) ≃ (Fin N → Fin N) :=
      Equiv.piCongrRight fun _ => σ.symm
    have hv (ω : Fin N → Fin N) :
        (fun k => wfOffspring N ω (σ k)) = wfOffspring N (e ω) := by
      funext k
      simp [wfOffspring, e, Equiv.symm_apply_eq]
    simp_rw [hv]
    exact e.sum_comp (fun ω => (1 / (N : ℝ) ^ N) * f (wfOffspring N ω))

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfModel_weight (N : ℕ) (ω : Fin N → Fin N) :
    (wfModel N).w ω = 1 / (N : ℝ) ^ N := rfl

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfModel_offspring (N : ℕ) (ω : Fin N → Fin N) (k : Fin N) :
    (wfModel N).ν ω k = wfOffspring N ω k := rfl

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfModel_count_law (N : ℕ) (S : Finset (Fin N)) (j : ℕ) :
    (∑ ω : Fin N → Fin N,
      if (∑ k ∈ S, wfOffspring N ω k) = j then (wfModel N).w ω else 0) =
      binomRow N ((S.card : ℝ) / N) j := by
  classical
  let a : AlleleCounts N N := ⟨(fun _ => 1), Finset.mem_piAntidiag.mpr ⟨by simp, by simp⟩⟩
  have hw (ω : Fin N → Fin N) :
      wfMultialleleAllocationWeight N N a ω = (wfModel N).w ω := by
    simp [wfMultialleleAllocationWeight, a, wfModel, one_div]
  have h := WrightFisherAllocationSupport.expect N N a
    (fun b => if (∑ k ∈ S, b.val k) = j then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [wfMultiallele_subset_count] at h
  have h' : binomRow N ((S.card : ℝ) / N) j =
      ∑ ω : Fin N → Fin N,
        if (∑ k ∈ S, wfOffspring N ω k) = j
        then wfMultialleleAllocationWeight N N a ω else 0 := by
    have hf : (∑ k ∈ S, (a.val k : ℝ)) = S.card := by simp [a]
    rw [hf] at h
    exact h
  rw [h']
  apply Finset.sum_congr rfl
  intro ω _
  rw [hw]

end Rhone.MarkovChain
