/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryProjection
public import Rhone.Combinatorics.KingmanShapeInterleavingRange
/-!
# An interleaved history determines its subtree histories and slot choice

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
private theorem shape_interleave_forests {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h h' : Combinatorics.RankedForestHistory F a) (g g' : Combinatorics.RankedForestHistory H b)
    (s s' : Combinatorics.HistoryInterleaving a b)
    (he : historyInterleave F H hF hH a b h g s = historyInterleave F H hF hH a b h' g' s')
    (k : ℕ) (hk : k ≤ a + b) :
    Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s k) = Combinatorics.historyAt F a
        h'
        (Combinatorics.interleavingLeft s' k) ∧
      Combinatorics.historyAt H b g (Combinatorics.interleavingRight s k) = Combinatorics.historyAt
          H b g'
          (Combinatorics.interleavingRight s' k) := by
  have htrace := congrArg (fun z => Combinatorics.historyAt _ (a + b) z k) he
  rw [historyAt_historyInterleave _ _ _ _ _ _ _ _ _ _ hk,
    historyAt_historyInterleave _ _ _ _ _ _ _ _ _ _ hk] at htrace
  constructor
  · have hl := congrArg (fun W => forestPreimage (Function.Embedding.inl : L ↪ L ⊕ M)
      (W.filter (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl))) htrace
    rw [history_sum_left_projection _ _ (historyAt_isForest H hH b g _),
      history_sum_left_projection _ _ (historyAt_isForest H hH b g' _)] at hl
    exact hl
  · have hr := congrArg (fun W => forestPreimage (Function.Embedding.inr : M ↪ L ⊕ M)
      (W.filter (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr))) htrace
    rw [history_sum_right_projection _ _ (historyAt_isForest F hF a h _),
      history_sum_right_projection _ _ (historyAt_isForest F hF a h' _)] at hr
    exact hr
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem historyInterleave_injective {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ) :
    Function.Injective (fun p :
      (Combinatorics.RankedForestHistory F a × Combinatorics.RankedForestHistory H b) ×
          Combinatorics.HistoryInterleaving a b =>
      historyInterleave F H hF hH a b p.1.1 p.1.2 p.2) := by
  classical
  rintro ⟨⟨h, g⟩, s⟩ ⟨⟨h', g'⟩, s'⟩ he
  have hforests := shape_interleave_forests F H hF hH a b h h' g g' s s' he
  have hcounts (k : ℕ) (hk : k ≤ a + b) :
      Combinatorics.interleavingLeft s k = Combinatorics.interleavingLeft s' k ∧
      Combinatorics.interleavingRight s k = Combinatorics.interleavingRight s' k := by
    have hleft := congrArg (fun X => (ADR11.roots X).card) (hforests k hk).1
    have hrank := historyAt_root_count F hF a h _ (Combinatorics.interleavingLeft_le s k)
    have hrank' := historyAt_root_count F hF a h' _ (Combinatorics.interleavingLeft_le s' k)
    have hsum := Combinatorics.interleaving_counts_sum s k hk
    have hsum' := Combinatorics.interleaving_counts_sum s' k hk
    omega
  have hs : s = s' := by
    apply Subtype.ext
    ext k
    have hnow := (hcounts k.val k.isLt.le).1
    have hnext := (hcounts (k.val + 1) k.isLt).1
    have hc := Combinatorics.interleaving_counts_succ s k
    have hc' := Combinatorics.interleaving_counts_succ s' k
    by_cases hm : k ∈ s.1 <;> by_cases hm' : k ∈ s'.1
    all_goals simp only [hm, hm', ite_true, ite_false] at hc hc' ⊢
    all_goals omega
  subst s'
  have hh : h = h' := by
    apply Combinatorics.historyAt_history_ext F a h h'
    intro j hj
    obtain ⟨k, hk, hkj⟩ := Combinatorics.interleavingLeft_range s j hj
    have hf := (hforests k hk).1
    rw [hkj] at hf
    exact hf
  have hg : g = g' := by
    apply Combinatorics.historyAt_history_ext H b g g'
    intro j hj
    obtain ⟨k, hk, hkj⟩ := Combinatorics.interleavingRight_range s j hj
    have hf := (hforests k hk).2
    rw [hkj] at hf
    exact hf
  subst h'
  subst g'
  rfl
end Rhone.Coalescent
