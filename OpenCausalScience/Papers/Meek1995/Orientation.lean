module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! Soundness of rules R1 and R2 in Meek (UAI 1995) in a consistent DAG
extension preserving the specified skeleton and unshielded colliders. -/

namespace OpenCausalScience.Papers.Meek1995.Orientation

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G : DAG n} {a b c : Fin n}

/-- For R1, reversing the edge between `b` and `c` would introduce
the excluded unshielded collider at `b`. -/
theorem orient_unshielded_noncollider (ab : G.edge a b = true)
    (bc : Adjacent G b c) (distinct : a ≠ c) (nonadjacent : ¬ Adjacent G a c)
    (noncollider : ¬ UnshieldedCollider G a b c) : G.edge b c = true :=
  bc.elim id (fun cb => (noncollider ⟨distinct, nonadjacent, ab, cb⟩).elim)

/-- For R2, a directed path forces the orientation of an adjacency
between its endpoints by acyclicity. -/
theorem orient_along_directed_path (path : G.DirectedWalk a c)
    (adjacent : Adjacent G a c) : G.edge a c = true :=
  adjacent.elim id (fun ca => (G.no_directed_cycle a (.extend path ca)).elim)

end
end OpenCausalScience.Papers.Meek1995.Orientation
