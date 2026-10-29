/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeProposalMeas
public import Rhone.Coalescent.FiniteIntervalMaterialKernel

/-!
# Measurability of SMC′ regrafting

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory ProbabilityTheory

theorem finiteBranch_measurable (N : ℕ) :
    Measurable (fun p : Finset (Fin N) × ℝ × ℝ => finiteBranch p.1 p.2.1 p.2.2) := by
  classical
  have hs : MeasurableSet {p : Finset (Fin N) × ℝ × ℝ |
      p.1 = ∅ ∨ p.1 = Finset.univ} :=
    (measurableSet_eq_fun measurable_fst measurable_const).union
      (measurableSet_eq_fun measurable_fst measurable_const)
  exact measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.fst.piecewise hs (measurable_snd.fst.max measurable_snd.snd)))

theorem belowCut_measurable (N : ℕ) :
    Measurable (fun p : Branch N × ℝ => belowCut p.1 p.2) :=
  (finiteBranch_measurable N).comp (measurable_fst.fst.prodMk
    (measurable_fst.snd.fst.prodMk (measurable_fst.snd.snd.min measurable_snd)))

theorem betweenCutAttachment_measurable (N : ℕ) :
    Measurable (fun p : Branch N × Finset (Fin N) × ℝ × ℝ =>
      betweenCutAttachment p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Measurable (fun p : Finset (Fin N) × Finset (Fin N) => p.1 \ p.2) :=
    measurable_of_countable _
  exact (finiteBranch_measurable N).comp
    ((hc.comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
      ((measurable_fst.snd.fst.max measurable_snd.snd.fst).prodMk
        (measurable_fst.snd.snd.min measurable_snd.snd.snd)))

theorem aboveAttachment_measurable (N : ℕ) :
    Measurable (fun p : Branch N × Finset (Fin N) × Finset (Fin N) × ℝ =>
      aboveAttachment p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  classical
  have hc : Measurable (fun p : Finset (Fin N) × Finset (Fin N) × Finset (Fin N) =>
      (p.1 \ p.2.1) ∪ if (p.1 ∩ p.2.2).Nonempty then p.2.1 else ∅) :=
    measurable_of_countable _
  exact (finiteBranch_measurable N).comp
    ((hc.comp (measurable_fst.fst.prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd.fst))).prodMk
        ((measurable_fst.snd.fst.max measurable_snd.snd.snd).prodMk measurable_fst.snd.snd))

theorem treeOfList_map_measurable {α δ : Type*} [MeasurableSpace δ] (N : ℕ)
    (l : List α) (f : α → δ → Branch N) (hf : ∀ a ∈ l, Measurable (f a)) :
    Measurable (fun p => treeOfList (l.map (fun a => f a p))) := by
  have hg : Measurable (fun p : δ => fun i : Fin l.length => f (l.get i) p) :=
    measurable_pi_iff.mpr (fun i => hf _ (List.get_mem l i))
  convert (measurable_sigma_mk (β := fun m => Fin m → Branch N) l.length).comp hg using 1
  funext p
  apply Sigma.ext (List.length_map (fun a => f a p))
  apply (Fin.heq_fun_iff (List.length_map (fun a => f a p))).mpr
  intro i
  simp [treeOfList, List.get_eq_getElem]

abbrev RegraftIndex (m : ℕ) := ((Fin m ⊕ Fin m) ⊕ Fin m) ⊕ Bool

abbrev RegraftArgs (N m : ℕ) :=
  (Fin m → Branch N) × Finset (Fin N) × Finset (Fin N) × ℝ × ℝ

def regraftIndices (m : ℕ) : List (RegraftIndex m) :=
  (List.finRange m).map (fun i => .inl (.inl (.inl i))) ++
  (List.finRange m).map (fun i => .inl (.inl (.inr i))) ++
  (List.finRange m).map (fun i => .inl (.inr i)) ++ [.inr false, .inr true]

noncomputable def regraftPiece {N m : ℕ} (z : RegraftIndex m)
    (p : RegraftArgs N m) : Branch N :=
  match z with
  | .inl (.inl (.inl i)) => belowCut (p.1 i) p.2.2.2.1
  | .inl (.inl (.inr i)) => betweenCutAttachment (p.1 i) p.2.1 p.2.2.2.1 p.2.2.2.2
  | .inl (.inr i) => aboveAttachment (p.1 i) p.2.1 p.2.2.1 p.2.2.2.2
  | .inr false => finiteBranch p.2.1 p.2.2.2.1 p.2.2.2.2
  | .inr true => finiteBranch (Finset.univ \ p.2.1) (rootHeight ⟨m, p.1⟩) p.2.2.2.2

theorem regraftPiece_measurable (N m : ℕ) (z : RegraftIndex m) :
    Measurable (@regraftPiece N m z) := by
  have hi (j : Fin m) : Measurable (fun p : RegraftArgs N m => p.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hs : Measurable (fun p : RegraftArgs N m => p.2.1) := measurable_snd.fst
  have htarg : Measurable (fun p : RegraftArgs N m => p.2.2.1) := measurable_snd.snd.fst
  have ht : Measurable (fun p : RegraftArgs N m => p.2.2.2.1) := measurable_snd.snd.snd.fst
  have ha : Measurable (fun p : RegraftArgs N m => p.2.2.2.2) := measurable_snd.snd.snd.snd
  rcases z with ((i | i) | i) | b
  · convert (belowCut_measurable N).comp ((hi i).prodMk ht) using 1
    funext p
    simp [regraftPiece]
  · convert (betweenCutAttachment_measurable N).comp
      ((hi i).prodMk (hs.prodMk (ht.prodMk ha))) using 1
    funext p
    simp [regraftPiece]
  · convert (aboveAttachment_measurable N).comp
      ((hi i).prodMk (hs.prodMk (htarg.prodMk ha))) using 1
    funext p
    simp [regraftPiece]
  · cases b with
    | false =>
      convert (finiteBranch_measurable N).comp (hs.prodMk (ht.prodMk ha)) using 1
      funext p
      simp [regraftPiece]
    | true =>
      have hc : Measurable (fun s : Finset (Fin N) => Finset.univ \ s) :=
        measurable_of_countable _
      convert (finiteBranch_measurable N).comp ((hc.comp hs).prodMk
        (((rootHeightFiber_measurable N m).comp measurable_fst).prodMk ha)) using 1
      funext p
      simp [regraftPiece]

theorem regraftFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × Finset (Fin N) × Finset (Fin N) × ℝ × ℝ =>
      regraft ⟨m, p.1⟩ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  convert treeOfList_map_measurable N (regraftIndices m) (@regraftPiece N m)
    (fun z _ => regraftPiece_measurable N m z) using 1
  funext p
  simp only [regraft, regraftIndices, List.map_append, List.map_map,
    List.map_cons, List.map_nil]
  rfl

end Rhone.Coalescent.SmcPrime
