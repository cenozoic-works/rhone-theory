/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Float64Kernel
public import Rhone.Computation.TableFloatError

/-! # The core-library binary64 checks equal the Mathlib ones -/

@[expose] public section
namespace Rhone.Computation.Float64Kernel

theorem pow2_eq (e : Int) : pow2 e = (2 : Rat) ^ e := by
  unfold pow2
  split
  · rename_i h
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp [zpow_natCast]
  · rename_i h
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (Int.le_of_lt (Int.not_le.mp h))
    subst hn
    simp [zpow_neg, zpow_natCast]

theorem absRat_eq (x : Rat) : absRat x = |x| := by
  unfold absRat
  split
  · rename_i h; exact (abs_of_neg h).symm
  · rename_i h; exact (abs_of_nonneg (not_lt.mp h)).symm

theorem floor_eq (x : Rat) : x.floor = ⌊x⌋ := by
  rw [Rat.floor_def', Rat.floor_def]

theorem nearestEven_eq (x : Rat) : nearestEven x = RatRounding.nearestEven x := by
  simp only [nearestEven, RatRounding.nearestEven, floor_eq]

theorem quantize_eq (step x : Rat) : quantize step x = RatRounding.quantize step x := by
  simp only [quantize, RatRounding.quantize, nearestEven_eq]

theorem decodeNormal_eq (bits : Nat) : decodeNormal bits = Binary64Normal.decode bits := by
  simp only [decodeNormal, Binary64Normal.decode, pow2_eq]

theorem decodeFinite_eq (bits : Nat) :
    decodeFinite bits = Binary64FiniteNearest.decodeFinite bits := by
  simp only [decodeFinite, Binary64FiniteNearest.decodeFinite, decodeNormal_eq, pow2_eq]

theorem acceptedPositive_eq (x : Rat) (bits : Nat) (e : Int) :
    acceptedPositive x bits e = Binary64Normal.acceptedPositive x bits e := by
  simp only [acceptedPositive, Binary64Normal.acceptedPositive, pow2_eq, decodeNormal_eq,
    quantize_eq]

theorem guardedAccepted_eq (x : Rat) (bits : Nat) (e : Int) :
    guardedAccepted x bits e = Binary64Scientific.guardedAccepted x bits e := by
  simp only [guardedAccepted, Binary64Scientific.guardedAccepted, accepted,
    Binary64Scientific.accepted, acceptedPositive_eq]

theorem guarded_decode {x : Rat} {bits : Nat} {e : Int}
    (h : guardedAccepted x bits e = true) : ∃ y, decodeFinite bits = some y := by
  rw [decodeFinite_eq]
  exact TableFloatError.Cell.accepted_decode (cell := ⟨x, bits, e⟩)
    (by simpa [TableFloatError.Cell.accepted, guardedAccepted_eq] using h)

theorem guarded_nearest {x y z : Rat} {e : Int} {bits other : Nat}
    (h : guardedAccepted x bits e = true) (hy : decodeFinite bits = some y)
    (hz : decodeFinite other = some z) : |y - x| ≤ |z - x| := by
  rw [guardedAccepted_eq] at h
  rw [decodeFinite_eq] at hy hz
  exact Binary64Scientific.guarded_nearest h hy hz

theorem guarded_relative {x y : Rat} {e : Int} {bits : Nat}
    (h : guardedAccepted x bits e = true) (hy : decodeFinite bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 := by
  rw [guardedAccepted_eq] at h
  rw [decodeFinite_eq] at hy
  exact Binary64Scientific.guarded_relative h hy

def Cell.toSpec (cell : Cell) : TableFloatError.Cell :=
  ⟨cell.original, cell.word, cell.exponent⟩

theorem Cell.accepted_eq (cell : Cell) : cell.accepted = cell.toSpec.accepted := by
  simp only [Cell.accepted, TableFloatError.Cell.accepted, Cell.toSpec, guardedAccepted_eq]

theorem Cell.relativeError_eq (cell : Cell) :
    cell.relativeError = cell.toSpec.relativeError := by
  unfold Cell.relativeError TableFloatError.Cell.relativeError Cell.toSpec
  rw [decodeFinite_eq]
  cases Binary64FiniteNearest.decodeFinite cell.word <;> simp [absRat_eq]

theorem maxRelativeError_eq (cells : List Cell) :
    maxRelativeError cells = TableFloatError.maxRelativeError (cells.map Cell.toSpec) := by
  simp only [maxRelativeError, TableFloatError.maxRelativeError, List.map_map]
  congr 1
  exact List.map_congr_left fun cell _ => Cell.relativeError_eq cell

theorem cellsAccepted_eq (cells : List Cell) :
    cellsAccepted cells = TableFloatError.accepted (cells.map Cell.toSpec) := by
  simp only [cellsAccepted, TableFloatError.accepted, List.all_map]
  congr 1
  funext cell
  simp [Cell.accepted_eq]

end Rhone.Computation.Float64Kernel
