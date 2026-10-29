/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootFibreMap
/-!
# Exact history and shape transport between equal leaf sizes

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem historyAt_castCard {m n : ℕ} (hmn : m = n)
    (h : Combinatorics.RankedLabelledHistory m) (r : ℕ) :
    Combinatorics.historyAt (ADR11.singletonForest n) (n - 1)
      (Equiv.cast (congrArg Combinatorics.RankedLabelledHistory hmn) h) r =
    forestEmbed (finCongr hmn).toEmbedding
      (Combinatorics.historyAt (ADR11.singletonForest m) (m - 1) h r) := by
  subst n
  change _ = forestEmbed (Function.Embedding.refl _) _
  rw [forestEmbed_refl]
  rfl
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem interleavingLeft_castFirst {a b c d : ℕ}
    (s : Combinatorics.FirstHistoryInterleaving a b) (ha : a = c) (hb : b = d) (r : ℕ) :
    Combinatorics.interleavingLeft
        (Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving ha hb) s).1 r =
      Combinatorics.interleavingLeft s.1 r := by
  cases ha
  cases hb
  rfl
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem interleavingRight_castFirst {a b c d : ℕ}
    (s : Combinatorics.FirstHistoryInterleaving a b) (ha : a = c) (hb : b = d) (r : ℕ) :
    Combinatorics.interleavingRight
        (Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving ha hb) s).1 r =
      Combinatorics.interleavingRight s.1 r := by
  cases ha
  cases hb
  rfl

/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem quotient_mk_castCard {m n : ℕ} (hmn : m = n)
    (h : Combinatorics.RankedLabelledHistory m) :
    Quotient.mk (Combinatorics.rankedShapeSetoid n)
        (Equiv.cast (congrArg Combinatorics.RankedLabelledHistory hmn) h) =
      Equiv.cast (congrArg Combinatorics.RankedShape hmn)
          (Quotient.mk (Combinatorics.rankedShapeSetoid m) h) := by
  cases hmn
  rfl
end Rhone.Coalescent
