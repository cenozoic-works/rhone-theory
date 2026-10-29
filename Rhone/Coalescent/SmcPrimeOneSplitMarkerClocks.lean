/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitExtraction
/-! # Old history state and marker times agree in the total extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractionStep_history_clock {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState)
    (hz : ∀ k : Fin N, (z.oldHistory k).2.1 = (z.oldHistory k).1.1) :
    ∀ k : Fin N, ((extractionStep z pre next).oldHistory k).2.1 =
      ((extractionStep z pre next).oldHistory k).1.1 := by
  classical
  intro k
  cases he : next.2.2 with
  | inl e => simpa only [extractionStep, he] using hz k
  | inr e =>
    cases e with
    | inr ix => simpa only [extractionStep, he] using hz k
    | inl ij =>
      let a := liveLabelAt pre.1 ij.1
      let b := liveLabelAt pre.1 ij.2
      by_cases hd : ∃ d, z.detached = some d ∧ (d = a ∨ d = b)
      · simpa only [extractionStep, he, a, b, hd, ite_true] using hz k
      · by_cases hj : z.mergers + 1 < N
        · by_cases hk : k = ⟨z.mergers + 1, hj⟩
          · subst k
            simp only [extractionStep, he, a, b, hd, ite_false, hj, dite_true,
              Function.update_self, rebuildCoal, atTime]
          · simpa only [extractionStep, he, a, b, hd, ite_false, hj, dite_true,
              Function.update_of_ne hk] using hz k
        · simpa only [extractionStep, he, a, b, hd, ite_false, hj, dite_false] using hz k

theorem extractionRun_history_clock (N : ℕ) (h : ARGPrefix (N + 1)) (n : ℕ) :
    ∀ k : Fin N, ((extractionRun N h n).oldHistory k).2.1 =
      ((extractionRun N h n).oldHistory k).1.1 := by
  have hfold : ∀ l : List (Fin (N + 1)), ∀ z : OneSplitExtractionState N,
      (∀ k : Fin N, (z.oldHistory k).2.1 = (z.oldHistory k).1.1) →
      ∀ k : Fin N, ((l.foldl (fun z j => extractionStep z
        (h ⟨j.val, Finset.mem_Iic.mpr (by omega)⟩)
        (h ⟨j.val + 1, Finset.mem_Iic.mpr j.isLt⟩)) z).oldHistory k).2.1 =
        ((l.foldl (fun z j => extractionStep z
          (h ⟨j.val, Finset.mem_Iic.mpr (by omega)⟩)
          (h ⟨j.val + 1, Finset.mem_Iic.mpr j.isLt⟩)) z).oldHistory k).1.1 := by
    intro l
    induction l with
    | nil => intro z hz; exact hz
    | cons j l ih =>
      intro z hz
      exact ih _ (extractionStep_history_clock z _ _ hz)
  exact hfold _ (extractionInitial N) (fun _ => rfl)

theorem extractOneSplitSkeleton_history_clock (N : ℕ) (h : ARGPrefix (N + 1)) :
    ∀ k : Fin N, ((extractOneSplitSkeleton N h).1 k).2.1 =
      ((extractOneSplitSkeleton N h).1 k).1.1 :=
  extractionRun_history_clock N h (N + 1)
end Rhone.Coalescent.SmcPrime
