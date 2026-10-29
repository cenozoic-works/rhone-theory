/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ADR11.Introduction.Counts
/-!
# Thin count wrappers for The-Anh Vu-Le's formalization of ADR11

Uses `lean4-adr11` (https://github.com/vltanh/lean4-adr11, Apache-2.0, commit `2db7f81`) by The-Anh
Vu-Le.

Source: felsenstein2004, ch. 3, pp. 20–25; allman_degnan_rhodes2011, sec. 1. -/
@[expose] public section
namespace Rhone.Combinatorics.External.ADR11
open Finset
open scoped Classical in
/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: felsenstein2004, ch. 3, pp. 20–24;
allman_degnan_rhodes2011, sec. 1. -/
theorem card_rooted_binary_labelled (n : ℕ) (hn : 1 ≤ n) :
    #{G : Finset (Finset (Fin n)) | _root_.ADR11.IsBinaryHierarchy G} =
      (2 * n - 3).doubleFactorial :=
  _root_.ADR11.section1_card_rooted n hn
open scoped Classical in
/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: felsenstein2004, ch. 3, p. 24;
allman_degnan_rhodes2011, sec. 1. -/
theorem card_binary_rootings (n : ℕ) (hn : 2 ≤ n) (G₀ : Finset (Finset (Fin n)))
    (hG₀ : _root_.ADR11.IsBinaryHierarchy G₀) :
    #{G : Finset (Finset (Fin n)) | _root_.ADR11.IsBinaryHierarchy G ∧
      _root_.ADR11.unroot G = _root_.ADR11.unroot G₀} = 2 * n - 3 :=
  _root_.ADR11.section1_card_rootings n hn G₀ hG₀
open scoped Classical in
/-- Re-exported from `lean4-adr11` by The-Anh Vu-Le. Source: felsenstein2004, ch. 3, pp. 24–25;
allman_degnan_rhodes2011, sec. 1. -/
theorem card_unrooted_binary_labelled (n : ℕ) (hn : 3 ≤ n) :
    #(({G : Finset (Finset (Fin n)) | _root_.ADR11.IsBinaryHierarchy G} : Finset _).image
      _root_.ADR11.unroot) = (2 * n - 5).doubleFactorial :=
  _root_.ADR11.section1_card_unrooted n hn
end Rhone.Combinatorics.External.ADR11
