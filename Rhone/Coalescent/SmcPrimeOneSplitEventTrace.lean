/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitExtraction
/-!
# Classification of the extracted one-split events into a chronological trace

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
noncomputable def extractionRebuildEvent (N : ℕ) (z : OneSplitExtractionState N)
    (pre next : AugmentedState) : RebuildEvent N := by
  classical
  exact match next.2.2 with
    | .inr (.inr _) => .inr false
    | .inr (.inl ij) =>
      if ∃ d, z.detached = some d ∧
          (d = liveLabelAt pre.1 ij.1 ∨ d = liveLabelAt pre.1 ij.2) then .inr true
      else if hm : z.mergers < N - 1 then .inl ⟨z.mergers, hm⟩ else .inr false
    | .inl _ => .inr false
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
noncomputable def extractionRebuildTrace (N : ℕ) (h : ARGPrefix (N + 1)) :
    List (RebuildEvent N) :=
  (List.finRange (N + 1)).map (fun k => extractionRebuildEvent N
    (extractionRun N h k.val)
    (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
    (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩))
end Rhone.Coalescent.SmcPrime
