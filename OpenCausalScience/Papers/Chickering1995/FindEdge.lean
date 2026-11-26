module
public import OpenCausalScience.Papers.Chickering1995.CoveredReversal
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! Lemma 2 of Chickering (UAI 1995). Choose the earliest head among
arrows whose orientation differs from the target DAG, then its latest
differing parent. The ranks can come from any topological sort. -/

namespace OpenCausalScience.Papers.Chickering1995.FindEdge

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H : DAG n} {a b : Fin n}

/-- Set membership in Chickering's set of edges with differing orientation. -/
def DifferingEdge (G H : DAG n) (u v : Fin n) : Prop :=
  G.edge u v = true ∧ H.edge v u = true

/-- The minimal head and maximal parent conditions of Find-Edge imply
that the selected arrow has equal endpoint parent sets outside the pair. -/
theorem parents_of_find_edge
    (skeleton : ∀ u v, Adjacent G u v ↔ Adjacent H u v)
    (colliders : ∀ u v w, UnshieldedCollider G u v w ↔ UnshieldedCollider H u v w)
    (selected : DifferingEdge G H a b)
    (firstHead : ∀ u v, DifferingEdge G H u v → G.rank b ≤ G.rank v)
    (lastParent : ∀ u, DifferingEdge G H u b → G.rank u ≤ G.rank a) :
    ∀ z, z ≠ a → z ≠ b → (G.edge z a = true ↔ G.edge z b = true) := by
  intro z za zb
  have abRank := G.edge_increases _ _ selected.1
  constructor
  · intro parentA
    by_cases noParentB : G.edge z b = true
    · exact noParentB
    exfalso
    have bzAbsent : G.edge b z ≠ true := by
      intro bz
      exact G.no_directed_cycle z (.extend (.extend (.single parentA) selected.1) bz)
    have noAdj : ¬ Adjacent G z b := fun adj => adj.elim noParentB bzAbsent
    have zaH : H.edge z a = true := by
      rcases (skeleton z a).mp (.inl parentA) with edge | edge
      · exact edge
      · have lower := firstHead z a ⟨parentA, edge⟩
        omega
    have colliderH : UnshieldedCollider H z a b :=
      ⟨zb, fun adj => noAdj ((skeleton z b).mpr adj), zaH, selected.2⟩
    have ba := ((colliders z a b).mpr colliderH).2.2.2
    exact G.no_directed_cycle a (.extend (.single selected.1) ba)
  · intro parentB
    by_cases noParentA : G.edge z a = true
    · exact noParentA
    exfalso
    have az : G.edge a z = true := by
      by_cases noAZ : G.edge a z = true
      · exact noAZ
      exfalso
      have colliderG : UnshieldedCollider G a b z :=
        ⟨za.symm, fun adj => adj.elim noAZ noParentA, selected.1, parentB⟩
      have abH := ((colliders a b z).mp colliderG).2.2.1
      exact H.no_directed_cycle a (.extend (.single abH) selected.2)
    have azH : H.edge a z = true := by
      rcases (skeleton a z).mp (.inl az) with edge | edge
      · exact edge
      · have lower := firstHead a z ⟨az, edge⟩
        have upper := G.edge_increases _ _ parentB
        omega
    rcases (skeleton z b).mp (.inl parentB) with edge | edge
    · exact H.no_directed_cycle b (.extend (.extend (.single selected.2) azH) edge)
    · have upper := lastParent z ⟨parentB, edge⟩
      have lower := G.edge_increases _ _ az
      omega

end
end OpenCausalScience.Papers.Chickering1995.FindEdge
