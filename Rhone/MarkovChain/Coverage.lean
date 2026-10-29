/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.CountedChain

/-! # Coverage classes for chains with an allele count -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory

class PositiveSize (N : ℕ) : Prop where
  pos : 0 < N

instance (n : ℕ) : PositiveSize (n + 1) := ⟨Nat.succ_pos n⟩

variable {S : Type*} [Fintype S] {N : ℕ}

class IsNeutralCounted (C : CountedChain S N) : Prop where
  neutral : C.IsNeutral

class HasClosedBoundary [DecidableEq S] (C : CountedChain S N) : Prop where
  closed : C.HasAbsorbingBoundary

class ReachesBoundary [DecidableEq S] (C : CountedChain S N) : Prop where
  reaches : C.toFinChain.Reaches C.boundary

class HasMartingaleCount (C : FinChain (Fin (N + 1))) : Prop where
  martingale : ∀ i, C.expect (fun j => (j : ℝ)) i = i

variable [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem fixation_real_of_coverage (C : CountedChain S N) [hN : PositiveSize N]
    [hn : IsNeutralCounted C] [hb : HasClosedBoundary C] [hR : ReachesBoundary C] (s : S) :
    (C.toFinChain.pathLaw s).real {ω | ∃ n, C.count (ω n) = Fin.last N} =
      ((C.count s : ℕ) : ℝ) / N :=
  CountedChain.fixation_real hN.pos hn.neutral hb.closed hR.reaches s

theorem loss_real_of_coverage (C : CountedChain S N) [hN : PositiveSize N]
    [hn : IsNeutralCounted C] [hb : HasClosedBoundary C] [hR : ReachesBoundary C] (s : S) :
    (C.toFinChain.pathLaw s).real {ω | ∃ n, C.count (ω n) = 0} =
      1 - ((C.count s : ℕ) : ℝ) / N :=
  CountedChain.loss_real hN.pos hn.neutral hb.closed hR.reaches s

end Rhone.MarkovChain
