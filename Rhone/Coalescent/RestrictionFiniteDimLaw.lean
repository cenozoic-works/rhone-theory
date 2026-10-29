/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FiniteDimLaw
public import Rhone.Coalescent.LambdaRestriction

/-!
# Consistency of coalescents under restriction, for finite-dimensional laws

Source: kingman1982, Thm 3; pitman1999, Thm 6. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain
open scoped NNReal

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Source: kingman1982, Thm 3. -/
theorem map_partitionChain_fdd_restrictAlong (f : α → β) {k : ℕ} {t : Fin k → ℝ}
    (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i) (π : Finpartition (univ : Finset β)) :
    ((partitionChain β).fdd π t).map (fun y i => restrictAlong f (y i)) =
      (partitionChain α).fdd (restrictAlong f π) t :=
  (partitionChain_lumps_restrictAlong f).map_fdd π hmono h0

/-- Source: kingman1982, Thm 3. -/
theorem map_partitionChain_fdd_bot {f : α → β} (hf : Function.Injective f) {k : ℕ}
    {t : Fin k → ℝ} (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i) :
    ((partitionChain β).fdd ⊥ t).map (fun y i => restrictAlong f (y i)) =
      (partitionChain α).fdd ⊥ t := by
  have h := map_partitionChain_fdd_restrictAlong f hmono h0 ⊥
  rwa [restrictAlong_bot hf] at h

/-- Source: kingman1982, Thm 3. -/
theorem map_partitionChain_fdd_restrictLast (n : ℕ) {k : ℕ} {t : Fin k → ℝ}
    (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i) :
    ((partitionChain (Fin (n + 1))).fdd ⊥ t).map (fun y i => restrictLast (y i)) =
      (partitionChain (Fin n)).fdd ⊥ t := by
  have h : (restrictLast : Finpartition (univ : Finset (Fin (n + 1))) → _) =
      restrictAlong Fin.castSucc := funext restrictLast_eq_restrictAlong
  rw [h]
  exact map_partitionChain_fdd_bot (Fin.castSucc_injective n) hmono h0

theorem partitionChain_hasFDD_restrictAlong (f : α → β) {π : Finpartition (univ : Finset β)}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → Finpartition (univ : Finset β)} (hX : (partitionChain β).HasFDD π P X) :
    (partitionChain α).HasFDD (restrictAlong f π) P fun t ω => restrictAlong f (X t ω) :=
  (partitionChain_lumps_restrictAlong f).hasFDD_comp hX

/-- Source: kingman1982, Thm 3. -/
theorem partitionChain_hasFDD_restrictLast (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → Finpartition (univ : Finset (Fin (n + 1)))}
    (hX : (partitionChain (Fin (n + 1))).HasFDD ⊥ P X) :
    (partitionChain (Fin n)).HasFDD ⊥ P fun t ω => restrictLast (X t ω) := by
  have h := partitionChain_hasFDD_restrictAlong (Fin.castSucc : Fin n → Fin (n + 1)) hX
  rw [restrictAlong_bot (Fin.castSucc_injective n)] at h
  have hr : (fun (t : ℝ≥0) (ω : Ω) => restrictLast (X t ω)) =
      fun t ω => restrictAlong Fin.castSucc (X t ω) :=
    funext fun t => funext fun ω => restrictLast_eq_restrictAlong (X t ω)
  rw [hr]
  exact h

/-- Source: pitman1999, Thm 6. -/
theorem map_lambdaPartitionChain_fdd_restrictAlong {Λ : Measure ℝ} (hΛ : Λ (Set.Icc 0 1) ≠ ⊤)
    (f : α → β) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i)
    (π : Finpartition (univ : Finset β)) :
    ((lambdaPartitionChain β Λ).fdd π t).map (fun y i => restrictAlong f (y i)) =
      (lambdaPartitionChain α Λ).fdd (restrictAlong f π) t :=
  (lambdaPartitionChain_lumps_restrictAlong hΛ f).map_fdd π hmono h0

/-- Source: pitman1999, Thm 6. -/
theorem map_lambdaPartitionChain_fdd_bot {Λ : Measure ℝ} (hΛ : Λ (Set.Icc 0 1) ≠ ⊤)
    {f : α → β} (hf : Function.Injective f) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t)
    (h0 : ∀ i, 0 ≤ t i) :
    ((lambdaPartitionChain β Λ).fdd ⊥ t).map (fun y i => restrictAlong f (y i)) =
      (lambdaPartitionChain α Λ).fdd ⊥ t := by
  have h := map_lambdaPartitionChain_fdd_restrictAlong hΛ f hmono h0 ⊥
  rwa [restrictAlong_bot hf] at h

/-- Source: pitman1999, Thm 6. -/
theorem lambdaPartitionChain_hasFDD_restrictAlong {Λ : Measure ℝ} (hΛ : Λ (Set.Icc 0 1) ≠ ⊤)
    (f : α → β) {π : Finpartition (univ : Finset β)} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → Finpartition (univ : Finset β)}
    (hX : (lambdaPartitionChain β Λ).HasFDD π P X) :
    (lambdaPartitionChain α Λ).HasFDD (restrictAlong f π) P fun t ω =>
      restrictAlong f (X t ω) :=
  (lambdaPartitionChain_lumps_restrictAlong hΛ f).hasFDD_comp hX

end Rhone.Coalescent
