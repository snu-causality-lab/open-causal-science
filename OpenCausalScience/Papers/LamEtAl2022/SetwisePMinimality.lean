module
public import OpenCausalScience.Papers.LamEtAl2022.ChickeringSequence
public import OpenCausalScience.Papers.Chickering2002.DeletionIndependence

/-! # Setwise Markovness and P-minimality

The algorithm queries singleton endpoints. The recursive-basis theorem
connects its Markov test to the paper's full CI relation on vertex sets. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Moralization Probability.CI RaskuttiUhler2018 Chickering2002
open KimEtAl2026.BayesBallCorrectness VermaPearl1990.DAGEquivalence VermaPearl1990.Equivalence

@[expose] public section

variable {n : Nat}

def setQuery (G : DAG n) (X Y Z : Mask n) : Query G := ⟨X, Y, Conditioning.ofPredicate G Z⟩

def SetwiseMarkov (J : Relation n) (G : DAG n) : Prop :=
  ∀ X Y Z, Disjoint3 X Y Z → ¬ (setQuery G X Y Z).DConnection → J X Y Z

def SetwiseSeparationSubset (G H : DAG n) : Prop :=
  ∀ X Y Z, Disjoint3 X Y Z → ¬ (setQuery G X Y Z).DConnection → ¬ (setQuery H X Y Z).DConnection

def SetwisePMinimal (J : Relation n) (G : DAG n) : Prop :=
  SetwiseMarkov J G ∧ ∀ H, SetwiseMarkov J H → SetwiseSeparationSubset G H → SetwiseSeparationSubset H G

private theorem disjoint_singletons {x y : Fin n} (different : x ≠ y) : Disjoint (single x) (single y) := by
  intro v member
  have same : v = x := beq_iff_eq.mp member
  subst v
  simpa [single] using different

private theorem singleton_outside {x : Fin n} {Z : Mask n} (outside : Z x = false) : Disjoint (single x) Z := by
  intro v member
  have same : v = x := beq_iff_eq.mp member
  simpa [same] using outside

private theorem no_pair_connection_iff {G : DAG n} {x y : Fin n} {Z : Mask n} :
    ¬ (setQuery G (single x) (single y) Z).DConnection ↔
      ¬ DConnected (Conditioning.ofPredicate G Z) x y := by
  constructor
  · intro none path
    exact none ⟨x, y, by simp [setQuery, single], by simp [setQuery, single], path⟩
  · intro none
    rintro ⟨u, v, left, right, path⟩
    have uSame : u = x := beq_iff_eq.mp left
    have vSame : v = y := beq_iff_eq.mp right
    exact none (uSame ▸ vSame ▸ path)

theorem markov_iff_setwise_markov {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (G : DAG n) :
    IsMarkov G independent ↔ SetwiseMarkov J G := by
  constructor
  · intro localMarkov X Y Z apart separated
    let order := (topologicalOrder G).idxOf
    have unique := idxOf_injective (topological_order_perm G)
    have topo := topological_order_increases G
    let H : DAG n := ⟨G.edge, order, topo⟩
    have same : SameDConnections H G := same_dConnections_of_edge_eq rfl
    have localH : OrderedLocalMarkov H H.rank J :=
      ordered_local_of_markov (G := G) g agrees order unique topo localMarkov
    apply localH.global_independence g.toSemigraphoid unique (setQuery H X Y Z) apart.2.1 apart.2.2
    rintro ⟨u, v, left, right, path⟩
    exact separated ⟨u, v, left, right, (same Z u v).mp path⟩
  · intro all x y Z distinct left right separated
    apply (agrees x y Z distinct left right).mpr
    apply all (single x) (single y) Z
      ⟨disjoint_singletons distinct, singleton_outside left, singleton_outside right⟩
    exact no_pair_connection_iff.mpr ((graphOracle_eq_true_iff G x y Z left right).mp separated)

theorem separation_subset_iff_setwise {G H : DAG n} : SeparationSubset G H ↔ SetwiseSeparationSubset G H := by
  constructor
  · intro subset X Y Z _ separated
    rintro ⟨u, v, left, right, path⟩
    exact separated ⟨u, v, left, right, IndependenceMap.dConnection subset Z u v path⟩
  · intro subset x y Z distinct left right separated
    apply (graphOracle_eq_true_iff H x y Z left right).mpr
    apply no_pair_connection_iff.mp
    apply subset (single x) (single y) Z
      ⟨disjoint_singletons distinct, singleton_outside left, singleton_outside right⟩
    exact no_pair_connection_iff.mpr ((graphOracle_eq_true_iff G x y Z left right).mp separated)

/-- The P-minimality used by the algorithm is the setwise definition in
Definition 3.7 when singleton queries agree with the graphoid relation. -/
theorem p_minimal_iff_setwise_p_minimal {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (G : DAG n) :
    PMinimal independent G ↔ SetwisePMinimal J G := by
  rw [PMinimal, SetwisePMinimal, markov_iff_setwise_markov g agrees G]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro H
  rw [markov_iff_setwise_markov g agrees H, separation_subset_iff_setwise, separation_subset_iff_setwise]

end

end OpenCausalScience.Papers.LamEtAl2022
