/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Process
public import Mathlib.MeasureTheory.Constructions.Projective

/-! # Projection of a measurable Markov trajectory -/
@[expose] public section
open MeasureTheory ProbabilityTheory Finset Preorder
namespace Rhone.Coalescent.SmcSupport
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

private def prefixMap (f : S → T) (n : ℕ) (u : Iic n → S) : Iic n → T := fun i => f (u i)

private theorem prefixMap_measurable (f : S → T) (hf : Measurable f) (n : ℕ) :
    Measurable (prefixMap f n) := measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

private def appendLast (n : ℕ) (u : Iic n → S) (y : S) (i : Iic (n + 1)) : S :=
  if h : i.val ≤ n then u ⟨i.val, mem_Iic.mpr h⟩ else y

private theorem appendLast_measurable (n : ℕ) (u : Iic n → S) : Measurable (appendLast n u) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : i.val ≤ n
  · simp [appendLast, h]
  · simp only [appendLast, dite_eq_right h]
    exact measurable_id

private theorem extension_apply (P : Rhone.MarkovChain.DiscreteProcess S) (n : ℕ) (u : Iic n → S) :
    Kernel.partialTraj (X := fun _ => S) P.stepSeq n (n + 1) u =
      (P.step (u ⟨n, mem_Iic.mpr le_rfl⟩)).map (appendLast n u) := by
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _
    (measurable_IicProdIoc (X := fun _ => S) (m := n) (n := n + 1)),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (measurable_IicProdIoc (X := fun _ => S) (m := n) (n := n + 1))
      measurable_prodMk_left,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ => S) n).measurable,
    Measure.map_map
      ((measurable_IicProdIoc (X := fun _ => S) (m := n) (n := n + 1)).comp measurable_prodMk_left)
      (MeasurableEquiv.piSingleton (X := fun _ => S) n).measurable]
  congr 1
  funext y i
  dsimp [appendLast, Function.comp_def, IicProdIoc]
  split_ifs with h
  · rfl
  · simp [MeasurableEquiv.piSingleton]

private theorem extension_projection (P : Rhone.MarkovChain.DiscreteProcess S)
    (Q : Rhone.MarkovChain.DiscreteProcess T) (f : S → T) (hf : Measurable f)
    (hstep : ∀ x, (P.step x).map f = Q.step (f x)) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => S) P.stepSeq n (n + 1)).map (prefixMap f (n + 1)) =
      (Kernel.partialTraj (X := fun _ => T) Q.stepSeq n (n + 1)).comap
        (prefixMap f n) (prefixMap_measurable f hf n) := by
  ext1 u
  rw [Kernel.map_apply _ (prefixMap_measurable f hf (n + 1)),
    Kernel.comap_apply, extension_apply, extension_apply,
    Measure.map_map (prefixMap_measurable f hf (n + 1)) (appendLast_measurable n u)]
  have hcomp : prefixMap f (n + 1) ∘ appendLast n u =
      appendLast n (prefixMap f n u) ∘ f := by
    funext y i
    dsimp [prefixMap, appendLast, Function.comp_def]
    split_ifs <;> rfl
  rw [hcomp, ← Measure.map_map (appendLast_measurable n (prefixMap f n u)) hf, hstep]
  rfl

private theorem partial_projection (P : Rhone.MarkovChain.DiscreteProcess S)
    (Q : Rhone.MarkovChain.DiscreteProcess T) (f : S → T) (hf : Measurable f)
    (hstep : ∀ x, (P.step x).map f = Q.step (f x)) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => S) P.stepSeq 0 n).map (prefixMap f n) =
      (Kernel.partialTraj (X := fun _ => T) Q.stepSeq 0 n).comap
        (prefixMap f 0) (prefixMap_measurable f hf 0) := by
  induction n with
  | zero => simp [Kernel.id_map, Kernel.id_comap, prefixMap_measurable f hf]
  | succ n ih =>
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.map_comp,
      extension_projection P Q f hf hstep n, ← Kernel.comp_map _ _
        (prefixMap_measurable f hf n), ih,
      ← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_assoc,
      Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
      Kernel.comp_deterministic_eq_comap]

private theorem measure_eq_of_prefix {μ ν : Measure (ℕ → T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  refine IsProjectiveLimit.unique (P := fun I => ν.map I.restrict) (fun I => ?_) fun I => rfl
  have hn : I ⊆ Finset.Iic (I.sup id) := fun i hi =>
    Finset.mem_Iic.mpr (Finset.le_sup (f := id) hi)
  have hcomp : (I.restrict : (ℕ → T) → _) =
      Finset.restrict₂ hn ∘ (frestrictLe (I.sup id)) := rfl
  change μ.map I.restrict = ν.map I.restrict
  rw [hcomp, ← Measure.map_map (Finset.measurable_restrict₂ hn)
    (measurable_frestrictLe _), h,
    Measure.map_map (Finset.measurable_restrict₂ hn) (measurable_frestrictLe _)]

theorem process_map_pathLaw (P : Rhone.MarkovChain.DiscreteProcess S)
    (Q : Rhone.MarkovChain.DiscreteProcess T) (f : S → T) (hf : Measurable f)
    (hstep : ∀ x, (P.step x).map f = Q.step (f x)) (x : S) :
    (P.pathLaw x).map (fun ω k => f (ω k)) = Q.pathLaw (f x) := by
  have hF : Measurable (fun (ω : ℕ → S) k => f (ω k)) :=
    measurable_pi_iff.mpr fun k => hf.comp (measurable_pi_apply k)
  apply measure_eq_of_prefix
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) hF]
  have hcomp : (frestrictLe (π := fun _ => T) n ∘ (fun (ω : ℕ → S) k => f (ω k))) =
      prefixMap f n ∘ (frestrictLe n) := rfl
  rw [hcomp, ← Measure.map_map (prefixMap_measurable f hf n) (measurable_frestrictLe n),
    P.pathLaw_eq, Kernel.traj_map_frestrictLe_apply,
    ← Kernel.map_apply _ (prefixMap_measurable f hf n),
    partial_projection P Q f hf hstep, Kernel.comap_apply,
    Q.pathLaw_eq, Kernel.traj_map_frestrictLe_apply]
  rfl

end Rhone.Coalescent.SmcSupport
