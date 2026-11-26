module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Papers.Meek1995.Closure

/-! The clique case of Meek's maximal orientation result. There are no
unshielded triples. Saturation under R2 gives precisely the comparable
pairs in the ordering imposed by the fixed arrows. -/

namespace OpenCausalScience.Papers.Meek1995.CompleteSkeleton

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

def Complete (base : DAG n) : Prop :=
  ∀ u v, u ≠ v → Adjacent base u v

def R2Closed (base : DAG n) (fixed : Orientations n) : Prop :=
  ∀ u v w, Unoriented base fixed u w → fixed u v → fixed v w → fixed u w

private theorem no_loops {G : DAG n} {u v : Fin n} (edge : Adjacent G u v) : u ≠ v := by
  intro same
  subst v
  exact G.no_directed_cycle u (.single (edge.elim id id))

private theorem rank_lt_orderedRank {rank : Fin n → Nat} {u v : Fin n}
    (h : rank u < rank v) : n * rank u + u.val < n * rank v + v.val := by
  have lt := Nat.add_lt_add_left u.isLt (n * rank u)
  have bound := Nat.mul_le_mul_left n h
  rw [Nat.mul_succ] at bound
  omega

private theorem orderedRank_injective {rank : Fin n → Nat} {u v : Fin n}
    (same : n * rank u + u.val = n * rank v + v.val) : u = v := by
  rcases Nat.lt_trichotomy (rank u) (rank v) with lower | eq | higher
  · exact ((Nat.ne_of_lt (rank_lt_orderedRank lower)) same).elim
  · apply Fin.ext
    simpa [eq] using same
  · exact ((Nat.ne_of_lt (rank_lt_orderedRank higher)) same.symm).elim

private def cliqueDAG (rank : Fin n → Nat) : DAG n where
  edge u v := decide (n * rank u + u.val < n * rank v + v.val)
  rank u := n * rank u + u.val
  edge_increases _ _ := of_decide_eq_true

private theorem cliqueDAG_preserves_rank {rank : Fin n → Nat} {u v : Fin n}
    (h : rank u < rank v) : (cliqueDAG rank).edge u v = true :=
  decide_eq_true (rank_lt_orderedRank h)

private theorem cliqueDAG_complete (rank : Fin n → Nat) : Complete (cliqueDAG rank) := by
  intro u v distinct
  rcases Nat.lt_trichotomy (n * rank u + u.val) (n * rank v + v.val) with h | h | h
  · exact .inl (decide_eq_true h)
  · exact (distinct (orderedRank_injective h)).elim
  · exact .inr (decide_eq_true h)

private theorem collider_false {base : DAG n} (complete : Complete base)
    {u v w : Fin n} (collider : UnshieldedCollider base u v w) : False :=
  collider.2.1 (complete u w collider.1)

private theorem fixed_transitive {base candidate : DAG n} {fixed : Orientations n}
    (complete : Complete base) (ext : Extension base fixed candidate)
    (closed : R2Closed base fixed) {u v w : Fin n} (uv : fixed u v) (vw : fixed v w) :
    fixed u w := by
  have path : candidate.DirectedWalk u w :=
    .extend (.single (ext.oriented _ _ uv)) (ext.oriented _ _ vw)
  have distinct : u ≠ w := by
    intro eq
    subst w
    exact candidate.no_directed_cycle u path
  by_cases uw : fixed u w
  · exact uw
  · have wu : ¬ fixed w u :=
      fun wu => candidate.no_directed_cycle u (.extend path (ext.oriented _ _ wu))
    exact closed u v w ⟨complete u w distinct, uw, wu⟩ uv vw

private theorem direction_extension {base candidate : DAG n} {fixed : Orientations n}
    (complete : Complete base) (ext : Extension base fixed candidate)
    (closed : R2Closed base fixed) {u v : Fin n} (openEdge : Unoriented base fixed u v) :
    ∃ other : DAG n, Extension base fixed other ∧ other.edge u v = true := by
  classical
  let old : DAG n :=
    ⟨fun a b => decide (fixed a b), candidate.rank,
      fun a b e => candidate.edge_increases a b (ext.oriented a b (of_decide_eq_true e))⟩
  have forWalk {a b} (walk : old.DirectedWalk a b) : fixed a b := by
    induction walk with
    | single edge => exact of_decide_eq_true edge
    | extend _ edge prev => exact fixed_transitive complete ext closed prev (of_decide_eq_true edge)
  have unavailable : ¬ old.DirectedWalk v u := fun path => openEdge.2.2 (forWalk path)
  obtain ⟨order, inserted⟩ :=
    (old.exists_insertion_iff (no_loops openEdge.1)).mpr unavailable
  let other := cliqueDAG order.rank
  refine ⟨other, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    exact ⟨fun e => cliqueDAG_complete _ _ _ (no_loops e), fun e => complete _ _ (no_loops e)⟩
  · intro a b c
    exact iff_of_false (collider_false complete) (collider_false (cliqueDAG_complete _))
  · intro a b e
    exact cliqueDAG_preserves_rank
      (order.edge_increases a b ((inserted a b).mpr (.inl (decide_eq_true e))))
  · exact cliqueDAG_preserves_rank
      (order.edge_increases u v ((inserted u v).mpr (.inr ⟨rfl, rfl⟩)))

/-- Under a complete skeleton, any edge left unoriented after R2 closure
has a consistent extension in each direction. The fixed orientations
may encode background knowledge and must admit a consistent extension. -/
theorem both_orientations_after_r2 {base candidate : DAG n} {fixed : Orientations n}
    (complete : Complete base) (ext : Extension base fixed candidate)
    (closed : R2Closed base fixed) {u v : Fin n} (openEdge : Unoriented base fixed u v) :
    (∃ G : DAG n, Extension base fixed G ∧ G.edge u v = true) ∧
      (∃ H : DAG n, Extension base fixed H ∧ H.edge v u = true) :=
  ⟨direction_extension complete ext closed openEdge,
    direction_extension complete ext closed ⟨Or.symm openEdge.1, openEdge.2.2, openEdge.2.1⟩⟩

/-- Starting from a nonempty extension set on a complete skeleton, a
stationary round leaves an edge open exactly where both directions can
be realized by extensions of the starting orientation. -/
theorem complete_skeleton_closure {base candidate : DAG n} {fixed : Orientations n}
    (complete : Complete base) (ext : Extension base fixed candidate) :
    ∃ rounds ≤ (pairs n).length, ∀ u v, Unoriented base (iterate base rounds fixed) u v ↔
      (∃ G : DAG n, Extension base fixed G ∧ G.edge u v = true) ∧
        (∃ H : DAG n, Extension base fixed H ∧ H.edge v u = true) := by
  have contains : ContainsColliders base fixed :=
    fun _ _ _ collider => (collider_false complete collider).elim
  obtain ⟨k, bound, stable⟩ := exists_stationary_round base fixed
  have equivalent {G : DAG n} :
      Extension base (iterate base k fixed) G ↔ Extension base fixed G :=
    extension_iff_after_iterations contains k
  have closed : R2Closed base (iterate base k fixed) :=
    fun u _ w openEdge ab bc => by
      have result : closeRound base (iterate base k fixed) u w :=
        .inr (.r2 openEdge ab bc)
      exact stable ▸ result
  refine ⟨k, bound, fun u v => ⟨?_, ?_⟩⟩
  · intro openEdge
    obtain ⟨⟨G, forward, uv⟩, ⟨H, backward, vu⟩⟩ :=
      both_orientations_after_r2 complete (equivalent.mpr ext) closed openEdge
    exact ⟨⟨G, equivalent.mp forward, uv⟩, ⟨H, equivalent.mp backward, vu⟩⟩
  · rintro ⟨⟨G, forwardOld, uv⟩, ⟨H, backward, vu⟩⟩
    have sk := forwardOld.skeleton
    have forward := equivalent.mpr forwardOld
    have back := equivalent.mpr backward
    exact ⟨(sk u v).mpr (.inl uv),
      fun arrow => H.no_directed_cycle u (.extend (.single (back.oriented _ _ arrow)) vu),
      fun arrow => G.no_directed_cycle u (.extend (.single uv) (forward.oriented _ _ arrow))⟩

end
end OpenCausalScience.Papers.Meek1995.CompleteSkeleton
