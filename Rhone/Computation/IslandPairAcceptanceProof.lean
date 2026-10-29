/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.IslandPairProof

/-! # Acceptance by the island-pair checker against the jump-and-hold law -/

@[expose] public section
namespace Rhone.Computation.IslandPair
open MeasureTheory

structure Request where
  demes : Nat
  migration : Rat
  coalescence : Rat

def Request.valid (q : Request) : Bool :=
  decide (2 ≤ q.demes ∧ q.demes ≤ 65535 ∧ 0 < q.migration ∧ 0 < q.coalescence)

def Request.check (q : Request) (claim : Array Rat) : Bool :=
  IslandPair.check q.demes q.migration q.coalescence claim

theorem Request.valid_iff (q : Request) :
    q.valid = true ↔
      2 ≤ q.demes ∧ q.demes ≤ 65535 ∧ 0 < q.migration ∧ 0 < q.coalescence := by
  simp [Request.valid]

private theorem array_eq_of_getD {a b : Array Rat} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.getD i 0 = b.getD i 0) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simpa [Array.getD, h1, h2] using this

theorem Request.check_sound (q : Request) (claim : Array Rat)
    (hvalid : q.valid = true) (accepted : q.check claim = true)
    (hm : 0 ≤ (q.migration : Real)) (hc : 0 ≤ (q.coalescence : Real)) :
    claim.size = 3 ∧
    0 ≤ (claim.getD 0 0 : Real) ∧
    0 ≤ (claim.getD 1 0 : Real) ∧
    (∀ a : Fin q.demes,
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).timeBefore
          {none} p
        ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).jumpHoldLaw
          (some (a, a)) = ENNReal.ofReal (claim.getD 0 0 : Real)) ∧
    (∀ a b : Fin q.demes, a ≠ b →
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).timeBefore
          {none} p
        ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).jumpHoldLaw
          (some (a, b)) = ENNReal.ofReal (claim.getD 1 0 : Real)) ∧
    (∀ a b : Fin q.demes, a ≠ b →
      (claim.getD 2 0 : Real) =
        ((∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, b))).toReal -
          (∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, a))).toReal) /
          (∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, b))).toReal) := by
  obtain ⟨d, m, c⟩ := q
  obtain ⟨hd, -, hm0, hc0⟩ := (Request.valid_iff _).mp hvalid
  dsimp only at hd hm0 hc0 hm hc ⊢
  have hmR : 0 < (m : Real) := by exact_mod_cast hm0
  have hcR : 0 < (c : Real) := by exact_mod_cast hc0
  have h : claim = values d m c := (IslandPair.check_iff _ _ _ _).mp accepted
  subst h
  have e0 : (values d m c).getD 0 0 = sameTime d c := rfl
  have e1 : (values d m c).getD 1 0 = differentTime d m c := rfl
  have e2 : (values d m c).getD 2 0 = timeContrast d m c := rfl
  rw [e0, e1, e2]
  have hs0 : 0 ≤ (sameTime d c : Real) := by
    rw [sameTime_cast, Rhone.Coalescent.IslandPair.sameTime]
    positivity
  have hd0 : 0 ≤ (differentTime d m c : Real) := by
    rw [differentTime_cast, Rhone.Coalescent.IslandPair.differentTime,
      Rhone.Coalescent.IslandPair.sameTime]
    positivity
  have hT := Rhone.Coalescent.IslandPair.lintegral_timeBefore d hd m c hmR hcR
  have hsame : ∀ a : Fin d,
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain d m c hm hc).timeBefore {none} p
        ∂(Rhone.Coalescent.IslandPair.chain d m c hm hc).jumpHoldLaw (some (a, a)) =
        ENNReal.ofReal (sameTime d c : Real) := by
    intro a
    rw [hT, sameTime_cast]
    simp [Rhone.Coalescent.IslandPair.meanTime]
  have hdiff : ∀ a b : Fin d, a ≠ b →
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain d m c hm hc).timeBefore {none} p
        ∂(Rhone.Coalescent.IslandPair.chain d m c hm hc).jumpHoldLaw (some (a, b)) =
        ENNReal.ofReal (differentTime d m c : Real) := by
    intro a b hab
    rw [hT, differentTime_cast]
    simp [Rhone.Coalescent.IslandPair.meanTime, hab]
  refine ⟨rfl, hs0, hd0, hsame, hdiff, ?_⟩
  intro a b hab
  rw [hdiff a b hab, hsame a, ENNReal.toReal_ofReal hs0, ENNReal.toReal_ofReal hd0,
    timeContrast_eq d hd m c hm0 hc0]
  push_cast
  rfl

theorem Request.check_complete (q : Request) (claim : Array Rat)
    (hvalid : q.valid = true)
    (hm : 0 ≤ (q.migration : Real)) (hc : 0 ≤ (q.coalescence : Real))
    (hsize : claim.size = 3)
    (h0 : 0 ≤ (claim.getD 0 0 : Real))
    (h1 : 0 ≤ (claim.getD 1 0 : Real))
    (hsame : ∀ a : Fin q.demes,
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).timeBefore
          {none} p
        ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).jumpHoldLaw
          (some (a, a)) = ENNReal.ofReal (claim.getD 0 0 : Real))
    (hdiff : ∀ a b : Fin q.demes, a ≠ b →
      ∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).timeBefore
          {none} p
        ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence hm hc).jumpHoldLaw
          (some (a, b)) = ENNReal.ofReal (claim.getD 1 0 : Real))
    (hcontrast : ∀ a b : Fin q.demes, a ≠ b →
      (claim.getD 2 0 : Real) =
        ((∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, b))).toReal -
          (∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, a))).toReal) /
          (∫⁻ p, (Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).timeBefore {none} p
            ∂(Rhone.Coalescent.IslandPair.chain q.demes q.migration q.coalescence
              hm hc).jumpHoldLaw (some (a, b))).toReal) :
    q.check claim = true := by
  obtain ⟨vsize, v0, v1, vsame, vdiff, vcontrast⟩ := Request.check_sound q
    (values q.demes q.migration q.coalescence) hvalid (IslandPair.check_complete _ _ _) hm hc
  obtain ⟨hd, -, -, -⟩ := (Request.valid_iff _).mp hvalid
  let a : Fin q.demes := ⟨0, by omega⟩
  let b : Fin q.demes := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have e0 : claim.getD 0 0 = (values q.demes q.migration q.coalescence).getD 0 0 := by
    have := (ENNReal.ofReal_eq_ofReal_iff h0 v0).mp ((hsame a).symm.trans (vsame a))
    exact_mod_cast this
  have e1 : claim.getD 1 0 = (values q.demes q.migration q.coalescence).getD 1 0 := by
    have := (ENNReal.ofReal_eq_ofReal_iff h1 v1).mp
      ((hdiff a b hab).symm.trans (vdiff a b hab))
    exact_mod_cast this
  have e2 : claim.getD 2 0 = (values q.demes q.migration q.coalescence).getD 2 0 := by
    have := (hcontrast a b hab).trans (vcontrast a b hab).symm
    exact_mod_cast this
  refine (IslandPair.check_iff _ _ _ _).mpr (array_eq_of_getD (hsize.trans vsize.symm) ?_)
  intro i hi
  rw [hsize] at hi
  interval_cases i
  · exact e0
  · exact e1
  · exact e2

theorem Request.zero_migration (d : Nat) (c : Rat) :
    (⟨d, 0, c⟩ : Request).valid = false ∧
      (values d 0 c).getD 1 0 = (values d 0 c).getD 0 0 := by
  refine ⟨by simp [Request.valid], ?_⟩
  simp [values, differentTime]

theorem Request.zero_migration_contrast (d : Nat) (c : Rat) (hd : 2 ≤ d) (hc : c ≠ 0) :
    (values d 0 c).getD 2 0 = 1 := by
  have hn : ((d - 1 : Nat) : Rat) ≠ 0 := by
    have : d - 1 ≠ 0 := by omega
    exact_mod_cast this
  simp [values, timeContrast, hc, hn]

theorem Request.zero_coalescence (d : Nat) (m : Rat) :
    (⟨d, m, 0⟩ : Request).valid = false ∧ (values d m 0).getD 0 0 = 0 := by
  refine ⟨by simp [Request.valid], ?_⟩
  simp [values, sameTime]

theorem Request.one_deme (m c : Rat) :
    (⟨1, m, c⟩ : Request).valid = false ∧
      (values 1 m c).getD 1 0 = (values 1 m c).getD 0 0 ∧
      (values 1 m c).getD 2 0 = 0 := by
  refine ⟨by simp [Request.valid], ?_, ?_⟩
  · simp [values, differentTime]
  · simp [values, timeContrast]

end Rhone.Computation.IslandPair
