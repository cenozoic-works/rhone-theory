/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseBlocks

/-! # Exact first-event insertion for arbitrary locally-L1 two-stage histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.IntegrablePhase
variable {n m : ℕ}

def postRow (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (a : ℝ) (i : Fin n) (t : ℝ) (j : Fin m) : ℝ :=
  inhomogeneousTransition N a t (Fin.castAdd m i) (Fin.natAdd n j)

def entryRow (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (F : ℝ → Matrix (Fin n) (Fin m) ℝ) (a : ℝ) (i : Fin n) (t : ℝ) : Fin m → ℝ :=
  (inhomogeneousTransition A a t * F t) i

lemma postRow_ae_hasDerivAt
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (B : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (F : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
    (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hpl : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.natAdd n j) = F t i j)
    (hll : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.natAdd n j) = B t i j)
    (a : ℝ) (i : Fin n) :
    ∀ᵐ t, ∀ j, HasDerivAt (fun s => postRow N a i s j)
      ((postRow N a i t ᵥ* B t + entryRow A F a i t) j) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right N hN, hpl, hll]
    with t ht hpt hlt j
  have he := ht a (Fin.castAdd m i) (Fin.natAdd n j)
  simpa only [Matrix.mul_apply, Fin.sum_univ_add, hpt, hlt,
    pre_transition N A hN hA hpp hlp, Matrix.vecMul, dotProduct, Pi.add_apply,
    postRow, entryRow, add_comm] using he

lemma postRow_initial
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume) (a : ℝ) (i : Fin n) :
    postRow N a i a = 0 := by
  funext j
  have hne : Fin.castAdd m i ≠ Fin.natAdd n j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp [postRow, integrableTransition_self N hN, hne]

lemma post_duhamel
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (B : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (F : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
    (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hpl : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.natAdd n j) = F t i j)
    (hll : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.natAdd n j) = B t i j)
    (a b : ℝ) (i : Fin n) (j : Fin m) :
    postRow N a i b j = ∫ s in a..b,
      (entryRow A F a i s ᵥ* inhomogeneousTransition B s b) j := by
  have hd := postRow_ae_hasDerivAt N A B F hN hA hpp hlp hpl hll a i
  have he := finiteRow_integrable_duhamel B hB (postRow N a i) (entryRow A F a i) a b
    (fun j => integrableTransition_entry_ac_right N hN a a b _ _)
    (by filter_upwards [hd] with t ht _; exact ht)
  rw [postRow_initial N hN, Matrix.zero_vecMul, zero_add] at he
  exact congrFun he j

end Rhone.Statistics.Identifiability.IntegrablePhase
