module
public import OpenCausalScience.Papers.LamEtAl2022.GRaSP
public import OpenCausalScience.Papers.LamEtAl2022.CoveredProjection
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap

/-! # Graph relations in the comparison of TSP and GRaSP

Singleton-endpoint d-separation implies separation between vertex sets
by checking every pair of endpoints. The inclusion transformation below
is the hypothesis supplied by Chickering's Theorem 4 (2002). -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Chickering1995.CoveredReversal Chickering2002 RaskuttiUhler2018

@[expose] public section

variable {n : Nat}

def ArrowSubset (G H : DAG n) : Prop := ∀ u v, G.edge u v = true → H.edge u v = true

def SeparationSubset (G H : DAG n) : Prop := IndependenceMap H G

theorem SeparationSubset.refl (G : DAG n) : SeparationSubset G G := IndependenceMap.refl G

theorem SeparationSubset.trans {G H K : DAG n} (a : SeparationSubset G H)
    (b : SeparationSubset H K) : SeparationSubset G K := IndependenceMap.trans b a

theorem SeparationSubset.of_edge_subset {G H : DAG n} (h : ArrowSubset H G) :
    SeparationSubset G H := IndependenceMap.of_edge_subset h

theorem SeparationSubset.of_edge_eq {G H : DAG n} (same : G.edge = H.edge) : SeparationSubset G H :=
  .of_edge_subset fun u v arrow => by rw [same]; exact arrow

theorem SeparationSubset.of_reversal {G H : DAG n} {a b : Fin n} (r : Reversal G H a b) :
    SeparationSubset G H :=
  fun x y c _ p q h => (graph_oracle_eq_of_covered_reversal r x y c p q).symm.trans h

theorem markov_of_separation_subset {G H : DAG n} {independent : CIOracle n}
    (sub : SeparationSubset G H) (h : IsMarkov H independent) : IsMarkov G independent :=
  fun x y c d p q r => h x y c d p q (sub x y c d p q r)

/-- A DAG is SGS-minimal when no proper spanning subgraph is Markov. -/
def SGSMinimal (independent : CIOracle n) (G : DAG n) : Prop :=
  IsMarkov G independent ∧ ∀ H, ArrowSubset H G → IsMarkov H independent → H.edge = G.edge

/-- A P-minimal DAG is Markov and has no Markov graph entailing strictly more CI statements. -/
def PMinimal (independent : CIOracle n) (G : DAG n) : Prop :=
  IsMarkov G independent ∧ ∀ H, IsMarkov H independent → SeparationSubset G H → SeparationSubset H G

/-- A proper edge subset has strictly fewer arrows. -/
theorem arrow_count_lt_of_proper_subset {G H : DAG n} (sub : ArrowSubset G H)
    (proper : G.edge ≠ H.edge) : arrowCount G < arrowCount H :=
  Nat.lt_of_le_of_ne (arrow_count_le_of_subset sub)
    (fun count => proper (edge_eq_of_subset_of_arrow_count_eq sub count))

end

end OpenCausalScience.Papers.LamEtAl2022
