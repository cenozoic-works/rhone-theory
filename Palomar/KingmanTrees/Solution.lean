module

public import Rhone.Combinatorics.KingmanHistories
public import Rhone.Combinatorics.KingmanShapeBases
public import Rhone.Coalescent.KingmanShapeRankedRecurrence
public import Rhone.Coalescent.KingmanUnrankedShapeRootCount
public import Rhone.Coalescent.KingmanTopologyProbability
public import Rhone.Coalescent.KingmanRootSplit
public import Rhone.Coalescent.KingmanRootSamplingLimit
public import Rhone.Coalescent.KingmanCollessExpectation
public import Rhone.Coalescent.KingmanSackin
public import Rhone.Coalescent.KingmanForestHistoryBridge

@[expose] public section

namespace Rhone.Palomar.KingmanTrees

open Finset Coalescent Rhone.Combinatorics MarkovChain

theorem card_ranked_labelled_history (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (RankedLabelledHistory n) =
      n.factorial * (n - 1).factorial / 2 ^ (n - 1) :=
  Rhone.Combinatorics.card_ranked_labelled_history n hn

theorem ranked_labelled_history_mass (n : ℕ) (hn : 1 ≤ n)
    (h : RankedLabelledHistory n) :
    historyMass (ADR11.singletonForest n) (n - 1) h =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * ((n - 1).factorial : ℝ)) :=
  Rhone.Combinatorics.ranked_labelled_history_mass n hn h

theorem card_ranked_shape_one : Fintype.card (RankedShape 1) = 1 :=
  Rhone.Combinatorics.card_ranked_shape_one

theorem card_ranked_shape_two : Fintype.card (RankedShape 2) = 1 :=
  Rhone.Combinatorics.card_ranked_shape_two

theorem card_unranked_shape_one : Fintype.card (UnrankedShape 1) = 1 :=
  Rhone.Combinatorics.card_unranked_shape_one

theorem card_unranked_shape_two : Fintype.card (UnrankedShape 2) = 1 :=
  Rhone.Combinatorics.card_unranked_shape_two

theorem card_ranked_shape_recurrence (n : ℕ) (hn : 3 ≤ n) :
    2 * Fintype.card (RankedShape n) =
      ∑ k ∈ Ico 1 n, (n - 2).choose (k - 1) *
        Fintype.card (RankedShape k) * Fintype.card (RankedShape (n - k)) :=
  Rhone.Coalescent.card_ranked_shape_recurrence n hn

theorem card_unranked_shape_recurrence (n : ℕ) (hn : 2 ≤ n) :
  Fintype.card (UnrankedShape n) =
    (∑ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1),
      Fintype.card (UnrankedShape k) * Fintype.card (UnrankedShape (n - k))) +
    if Even n then
      Fintype.card (UnrankedShape (n / 2)) *
        (Fintype.card (UnrankedShape (n / 2)) + 1) / 2
    else 0 :=
  Rhone.Coalescent.card_unranked_shape_recurrence n hn

theorem kingman_topology_probability_of_clade_factors (n : ℕ) (hn : 1 ≤ n)
    (T : LabelledTopology n) :
    topologyWeight n T =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * (coalescentTopologyCladeProduct T : ℝ)) :=
  Rhone.Coalescent.kingman_topology_probability_of_clade_factors n hn T

theorem root_split_mass (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA0 : 0 < A.card) (hAn : A.card < n) :
    rootSplitMass n A = (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) :=
  Rhone.Coalescent.root_split_mass n hn A hA0 hAn

theorem sample_population_root_probability (N : ℕ) (hN : 2 ≤ N)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    samplePopulationRootMass N S =
      ((S.card - 1 : ℕ) : ℝ) * (N + 1 : ℕ) /
        (((S.card + 1 : ℕ) : ℝ) * (N - 1 : ℕ)) :=
  Rhone.Coalescent.sample_population_root_probability N hN S hS

theorem tendsto_sample_population_root_probability (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun N => samplePopulationRootMass N
        (Finset.univ.filter (fun x : Fin N => x.val < n)))
      Filter.atTop (nhds (((n - 1 : ℕ) : ℝ) / (n + 1 : ℕ))) :=
  Rhone.Coalescent.tendsto_sample_population_root_probability n hn

theorem kingman_colless_expectation (n : ℕ) (hn : 1 ≤ n) :
    historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeColless G : ℝ)) =
      (n : ℝ) * (((harmonic (n / 2) : ℚ) : ℝ)) - 2 * (n / 2 : ℕ) :=
  Rhone.Coalescent.kingman_colless_expectation n hn

theorem kingman_sackin_expectation (n : ℕ) (hn : 1 ≤ n) :
    historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeSackin G : ℝ)) =
      2 * (n : ℝ) * (((harmonic n : ℚ) : ℝ) - 1) :=
  Rhone.Coalescent.kingman_sackin_expectation n hn

theorem historyPayoff_roots_eq_partition_stepN {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : ADR11.IsForest F) (π : Finpartition (univ : Finset L))
    (hπ : π.parts = ADR11.roots F) (t : ℕ) (ht : t ≤ (ADR11.roots F).card - 1)
    (f : Finset (Finset L) → ℝ) :
    historyPayoff F t (fun G => f (ADR11.roots G)) =
      ∑ σ : Finpartition (univ : Finset L),
        (partitionChain L).jumpChain.stepN t π σ * f σ.parts :=
  Rhone.Coalescent.historyPayoff_roots_eq_partition_stepN hF π hπ t ht f

theorem sum_jumpMatrix_roots_eq_partitionJump {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : ADR11.IsForest F)
    (π σ : Finpartition (univ : Finset L)) (hπ : π.parts = ADR11.roots F) :
    (∑ G ∈ univ.filter (fun G : Finset (Finset L) => ADR11.roots G = σ.parts),
        ADR11.jumpMatrix F G) =
      (partitionChain L).jumpChain.P π σ :=
  Rhone.Coalescent.External.ADR11.sum_jumpMatrix_roots_eq_partitionJump hF π σ hπ

end Rhone.Palomar.KingmanTrees
