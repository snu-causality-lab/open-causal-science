module
public import OpenCausalScience.Papers.LamEtAl2022.EdgeCount
public import OpenCausalScience.Papers.LamEtAl2022.Tuck
public import OpenCausalScience.Papers.RaskuttiUhler2018.Minimality

/-! Lemma B.8(b–d) of Lam, Andrews and Ramsey, UAI 2022. The DAG induced
from the tucked order is a subgraph of the covered reversal. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Moralization RaskuttiUhler2018
open Chickering1995.CoveredReversal
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {G H : DAG n}

private theorem earlier_of_causal_order {xs : List (Fin n)} (order : CausalOrder G xs)
    {u v : Fin n} (source : u ∈ xs) (target : v ∈ xs) (edge : G.edge u v = true) :
    xs.idxOf u < xs.idxOf v := by
  induction xs with
  | nil => cases source
  | cons a xs ih =>
    have ⟨before, rest⟩ := List.pairwise_cons.mp order
    have distinct : u ≠ v := by
      intro eq
      subst v
      exact G.no_directed_cycle u (.single edge)
    by_cases sourceFirst : a = u
    · subst a
      simp [List.idxOf_cons, distinct]
    · have sourceRest := (List.mem_cons.mp source).resolve_left (Ne.symm sourceFirst)
      by_cases targetFirst : a = v
      · subst a
        have impossible := before u sourceRest
        rw [edge] at impossible
        contradiction
      · have targetRest := (List.mem_cons.mp target).resolve_left (Ne.symm targetFirst)
        simpa [List.idxOf_cons, sourceFirst, targetFirst] using ih rest sourceRest targetRest

private theorem rank_unique {xs : List (Fin n)} (covers : ∀ u, u ∈ xs)
    (u v : Fin n) (same : xs.idxOf u = xs.idxOf v) : u = v := by
  have uBound := List.idxOf_lt_length_iff.mpr (covers u)
  have vBound := List.idxOf_lt_length_iff.mpr (covers v)
  have lookup : xs[xs.idxOf u]'uBound = xs[xs.idxOf v]'vBound := by
    simp only [same]
  simpa only [List.getElem_idxOf] using lookup

theorem graph_oracle_eq_of_covered_reversal {a b : Fin n} (R : Reversal G H a b)
    (x y : Fin n) (condition : Fin n → Bool)
    (outsideX : condition x = false) (outsideY : condition y = false) :
    graphOracle G x y condition = graphOracle H x y condition := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  let T : Query H := ⟨(· == x), (· == y), Conditioning.ofPredicate H condition⟩
  have qLeft : ∀ v, Q.left v = true → Q.condition.member v = false := by
    intro v hv
    change (v == x) = true at hv
    simpa [Q, Conditioning.ofPredicate, beq_iff_eq.mp hv] using outsideX
  have qRight : ∀ v, Q.right v = true → Q.condition.member v = false := by
    intro v hv
    change (v == y) = true at hv
    simpa [Q, Conditioning.ofPredicate, beq_iff_eq.mp hv] using outsideY
  have tLeft : ∀ v, T.left v = true → T.condition.member v = false := qLeft
  have tRight : ∀ v, T.right v = true → T.condition.member v = false := qRight
  change Q.dagMoralSeparated = T.dagMoralSeparated
  apply Bool.eq_iff_iff.mpr
  rw [Q.dagMoralSeparated_eq_true_iff qLeft qRight, T.dagMoralSeparated_eq_true_iff tLeft tRight]
  exact not_congr (R.dConnection_iff Q T rfl rfl rfl qLeft qRight)

theorem markov_of_covered_reversal {a b : Fin n} {independent : CIOracle n}
    (R : Reversal G H a b) (markov : IsMarkov G independent) : IsMarkov H independent := by
  intro x y condition distinct outsideX outsideY separated
  exact markov x y condition distinct outsideX outsideY
    ((graph_oracle_eq_of_covered_reversal R x y condition outsideX outsideY).trans separated)

/-- The new order can omit arrows of the covered reversal when reinducing
its DAG by the CI oracle. The original DAG is assumed Markov for that oracle. -/
theorem covered_tuck_subgraph {independent : CIOracle n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (nodup : s.original.Nodup) (cov : Covered G s.tailVertex s.headVertex)
    (ancestor : Fin n → Bool)
    (ancestorCorrect : ∀ u, ancestor u = true ↔ G.DirectedWalk u s.headVertex)
    (markov : IsMarkov G independent) {u v : Fin n}
    (arrow : (orderDAG ((s.tuck (G.edge s.tailVertex s.headVertex) ancestor).idxOf)
      independent).edge u v = true) :
    (Reversal.flip G s.tailVertex s.headVertex cov.arrow cov.parents).edge u v = true := by
  have perm := s.tuck_perm (G.edge s.tailVertex s.headVertex) ancestor
  have newCovers (w : Fin n) := perm.mem_iff.mpr (covers w)
  have sequence := covered_tuck_is_causal_order s order covers nodup cov ancestor ancestorCorrect
  have rev := Reversal.flip_is_covered_reversal G s.tailVertex s.headVertex cov.arrow cov.parents
  exact orderDAG_subgraph_of_markov _ (rank_unique newCovers)
    (fun a b h => earlier_of_causal_order sequence (newCovers a) (newCovers b) h)
    (markov_of_covered_reversal rev markov) arrow


/-- Lemma B.8(c–d). The order projection does not increase the arrow count
and preserves every d-separation of the original graph. -/
theorem covered_tuck_sparsity_and_separations {independent : CIOracle n} (s : OrderSplit (Fin n))
    (order : CausalOrder G s.original) (covers : ∀ u, u ∈ s.original)
    (nodup : s.original.Nodup) (cov : Covered G s.tailVertex s.headVertex)
    (ancestor : Fin n → Bool)
    (ancestorCorrect : ∀ u, ancestor u = true ↔ G.DirectedWalk u s.headVertex)
    (markov : IsMarkov G independent) :
    let projected := orderDAG ((s.tuck (G.edge s.tailVertex s.headVertex) ancestor).idxOf) independent
    arrowCount projected ≤ arrowCount G ∧
      ∀ x y condition, condition x = false → condition y = false →
        graphOracle G x y condition = true → graphOracle projected x y condition = true := by
  let H := Reversal.flip G s.tailVertex s.headVertex cov.arrow cov.parents
  let projected := orderDAG ((s.tuck (G.edge s.tailVertex s.headVertex) ancestor).idxOf) independent
  have subset : ∀ a b, projected.edge a b = true → H.edge a b = true := fun _ _ edge =>
    covered_tuck_subgraph s order covers nodup cov ancestor ancestorCorrect markov edge
  have reversal := Reversal.flip_is_covered_reversal G s.tailVertex s.headVertex cov.arrow cov.parents
  constructor
  · rw [arrow_count_eq_of_reversal reversal]
    exact arrow_count_le_of_subset subset
  · intro x y condition xOutside yOutside separated
    apply graphOracle_of_edge_subset subset xOutside yOutside
    exact (graph_oracle_eq_of_covered_reversal reversal x y condition xOutside yOutside).symm.trans separated

end

end OpenCausalScience.Papers.LamEtAl2022
