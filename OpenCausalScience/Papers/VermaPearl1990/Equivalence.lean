module
public import OpenCausalScience.Papers.Chickering1995.Transformation

/-! The sufficient direction of Verma and Pearl's Theorem 1, via the
covered-reversal construction of Chickering (1995). -/

namespace OpenCausalScience.Papers.VermaPearl1990.Equivalence

open OpenCausalScience.Papers.KimEtAl2026
open BayesBallCorrectness
open OpenCausalScience.Papers.Chickering1995.Transformation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H : DAG n}

private theorem walk_of_eq_edges (same : G.edge = H.edge)
    {u v : Fin n} (walk : G.DirectedWalk u v) : H.DirectedWalk u v := by
  induction walk with
  | single edge => exact .single (same ▸ edge)
  | extend _ edge ih => exact .extend ih (same ▸ edge)

private theorem dConnection_of_eq_edges (same : G.edge = H.edge)
    (fixed : Fin n → Bool) {x y : Fin n}
    (connected : DConnected (Conditioning.ofPredicate G fixed) x y) :
    DConnected (Conditioning.ofPredicate H fixed) x y := by
  let C := Conditioning.ofPredicate G fixed
  let E := Conditioning.ofPredicate H fixed
  have hit (u : Fin n) : C.descendantHit u = E.descendantHit u := by
    apply Bool.eq_iff_iff.mpr
    rw [C.descendant_spec, E.descendant_spec]
    exact ⟨fun ⟨w, member, walk⟩ => ⟨w, member, walk_of_eq_edges same walk⟩,
      fun ⟨w, member, walk⟩ => ⟨w, member, walk_of_eq_edges same.symm walk⟩⟩
  have step {a b : BayesBall.State (Fin n)} (p : ActiveStep C a b) : ActiveStep E a b := by
    refine ⟨?_, ?_⟩
    · have moved := p.1
      unfold Move at moved ⊢
      simpa only [same] using moved
    · have opened := p.2
      unfold OpenTurn Conditioning.activated at opened ⊢
      have sameMember : C.member = E.member := rfl
      simpa only [sameMember, hit a.1] using opened
  have liftWalk {a b : BayesBall.State (Fin n)} {route : List (Fin n)}
      (walk : ActiveWalk C a route b) : ActiveWalk E a route b := by
    induction walk with
    | nil => exact .nil _
    | cons arrow _ ih => exact .cons (step arrow) ih
  rcases connected with ⟨hx, hy, route, arrival, walk, simple⟩
  exact ⟨hx, hy, route, arrival, liftWalk walk, simple⟩

/-- Equal edge functions yield equal d-separation answers even when the
two stored topological rankings differ. -/
theorem same_dConnections_of_edge_eq (same : G.edge = H.edge) : SameDConnections G H :=
  fun fixed _ _ => ⟨dConnection_of_eq_edges same fixed, dConnection_of_eq_edges same.symm fixed⟩

/-- Markov equivalence in graphical conditional independence is
equivalent to equality of skeletons and unshielded colliders. -/
theorem same_dConnections_iff_same_signature :
    SameDConnections G H ↔ SameSignature G H := by
  refine ⟨sameSkeleton_and_sameUnshieldedColliders_of_sameDConnections, ?_⟩
  intro signature
  have turns := reversal_sequence_of_same_signature signature
  clear signature
  induction turns with
  | done equal => exact same_dConnections_of_edge_eq equal
  | next _ step _ ih =>
    exact fun fixed x y => (sameDConnections_of_reversal step fixed x y).trans (ih fixed x y)

/-- The executable comparison succeeds exactly when all graphical
d-separation queries agree. -/
theorem signaturesMatch_iff_same_dConnections :
    signaturesMatch G H = true ↔ SameDConnections G H :=
  (signaturesMatch_iff G H).trans same_dConnections_iff_same_signature.symm

end
end OpenCausalScience.Papers.VermaPearl1990.Equivalence
