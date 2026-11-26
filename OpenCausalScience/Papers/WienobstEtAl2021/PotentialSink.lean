module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Papers.Meek1995.Closure

/-! # Potential-sink elimination

Wienöbst, Bannach, and Liśkiewicz (UAI 2021), Definitions 4.1–4.2,
Fact 4.3, and Corollary 4.4. The mixed input contains its own skeleton
and fixed v-structures, so an input can be represented before an extension
is known. See https://proceedings.mlr.press/v161/wienobst21a.html.
-/

namespace OpenCausalScience.Papers.WienobstEtAl2021.PotentialSink

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

/-- A partially directed graph on labelled vertices. An adjacent pair without
either arrow is an undirected edge. The extension test also accepts cyclic
arrow specifications as inputs. -/
structure PDAG (n : Nat) where
  adjacent : Fin n → Fin n → Prop
  arrow : Fin n → Fin n → Prop
  adjacent_symm : ∀ {u v}, adjacent u v → adjacent v u
  no_loops : ∀ u, ¬ adjacent u u
  arrow_adjacent : ∀ {u v}, arrow u v → adjacent u v

namespace PDAG

def undirected (P : PDAG n) (u v : Fin n) : Prop :=
  P.adjacent u v ∧ ¬ P.arrow u v ∧ ¬ P.arrow v u

theorem undirected_symm {P : PDAG n} {u v : Fin n} (h : P.undirected u v) :
    P.undirected v u := ⟨P.adjacent_symm h.1, h.2.2, h.2.1⟩

def collider (P : PDAG n) (u v w : Fin n) : Prop :=
  u ≠ w ∧ ¬ P.adjacent u w ∧ P.arrow u v ∧ P.arrow w v

/-- The consistent extension condition preserves adjacencies, fixes existing
arrows and introduces no unshielded collider. -/
structure Extends (P : PDAG n) (G : DAG n) : Prop where
  skeleton : ∀ u v, P.adjacent u v ↔ Adjacent G u v
  arrows : ∀ u v, P.arrow u v → G.edge u v = true
  colliders : ∀ u v w, UnshieldedCollider G u v w → P.collider u v w

theorem Extends.colliders_iff {P : PDAG n} {G : DAG n} (h : P.Extends G)
    (u v w : Fin n) : P.collider u v w ↔ UnshieldedCollider G u v w :=
  ⟨fun c => ⟨c.1, fun a => c.2.1 ((h.skeleton u w).mpr a),
    h.arrows u v c.2.2.1, h.arrows w v c.2.2.2⟩, h.colliders u v w⟩

/-- Relation to Meek's representation, when an original DAG provides
the skeleton and collider signature of the input. -/
theorem extends_iff_meek {P : PDAG n} {base G : DAG n}
    (skeleton : ∀ u v, P.adjacent u v ↔ Adjacent base u v)
    (colliders : ∀ u v w, P.collider u v w ↔ UnshieldedCollider base u v w) :
    P.Extends G ↔ Extension base P.arrow G := by
  constructor
  · intro h
    exact ⟨fun u v => (skeleton u v).symm.trans (h.skeleton u v),
      fun u v w => (colliders u v w).symm.trans (h.colliders_iff u v w), h.arrows⟩
  · intro h
    exact ⟨fun u v => (skeleton u v).trans (h.skeleton u v), h.oriented,
      fun u v w c => (colliders u v w).mpr ((h.colliders u v w).mpr c)⟩

/-- Potential-sink conditions in the subgraph induced by the active vertices.
The undirected neighbors must be pairwise adjacent and adjacent to each parent. -/
def IsPotentialSink (P : PDAG n) (active : Fin n → Prop) (v : Fin n) : Prop :=
  (∀ u, active u → ¬ P.arrow v u) ∧
  ∀ u w, active u → active w → u ≠ w →
    P.undirected u v → (P.undirected w v ∨ P.arrow w v) → P.adjacent u w

private theorem IsPotentialSink.arrows_of_nonadjacent_parents
    {P : PDAG n} {active : Fin n → Prop} {u v w : Fin n}
    (sink : P.IsPotentialSink active v) (uActive : active u) (wActive : active w)
    (distinct : u ≠ w) (nonadjacent : ¬ P.adjacent u w)
    (left : P.adjacent u v) (right : P.adjacent w v) :
    P.arrow u v ∧ P.arrow w v := by
  have noOutU := sink.1 u uActive
  have noOutW := sink.1 w wActive
  have arrowU : P.arrow u v := by
    apply Classical.byContradiction
    intro openU
    have other : P.undirected w v ∨ P.arrow w v := by
      by_cases a : P.arrow w v
      · exact .inr a
      · exact .inl ⟨right, a, noOutW⟩
    exact nonadjacent (sink.2 u w uActive wActive distinct ⟨left, openU, noOutU⟩ other)
  refine ⟨arrowU, ?_⟩
  apply Classical.byContradiction
  intro openW
  exact nonadjacent (P.adjacent_symm (sink.2 w u wActive uActive
    distinct.symm ⟨right, openW, noOutW⟩ (.inr arrowU)))

/-- Larger ranks are eliminated first. At the elimination of a vertex, precisely
the vertices of lower or equal rank are still active. -/
def IsEliminationOrder (P : PDAG n) (rank : Fin n → Nat) : Prop :=
  (∀ {u v}, rank u = rank v → u = v) ∧
  ∀ v, P.IsPotentialSink (fun u => rank u ≤ rank v) v

private theorem rank_pair_lt {r s : Nat} {u v : Fin n} (h : r < s) :
    n * r + u.val < n * s + v.val := by
  have next := Nat.mul_le_mul_left n h
  rw [Nat.mul_succ] at next
  have bound := u.isLt
  omega

theorem Extends.has_elimination_order {P : PDAG n} {G : DAG n} (h : P.Extends G) :
    ∃ rank, P.IsEliminationOrder rank := by
  let rank (u : Fin n) := n * G.rank u + u.val
  have increases {u v} (edge : G.edge u v = true) : rank u < rank v :=
    rank_pair_lt (G.edge_increases _ _ edge)
  have toward {u v} (a : P.adjacent u v) (before : rank u ≤ rank v) :
      G.edge u v = true :=
    ((h.skeleton u v).mp a).resolve_right fun back => Nat.not_lt_of_ge before (increases back)
  refine ⟨rank, ?_, ?_⟩
  · intro u v equal
    have rankEqual : G.rank u = G.rank v := by
      rcases Nat.lt_trichotomy (G.rank u) (G.rank v) with less | same | greater
      · exact (Nat.ne_of_lt (rank_pair_lt (u := u) (v := v) less) equal).elim
      · exact same
      · exact (Nat.ne_of_lt (rank_pair_lt (u := v) (v := u) greater) equal.symm).elim
    apply Fin.ext
    simpa [rank, rankEqual] using equal
  · intro v
    refine ⟨fun u before a => Nat.not_lt_of_ge before (increases (h.arrows v u a)), ?_⟩
    intro u w beforeU beforeW distinct undirected other
    apply Classical.byContradiction
    intro absent
    have uw : UnshieldedCollider G u v w :=
      ⟨distinct, fun a => absent ((h.skeleton u w).mpr a), toward undirected.1 beforeU,
        toward (other.elim (·.1) P.arrow_adjacent) beforeW⟩
    exact undirected.2.1 (h.colliders u v w uw).2.2.1

theorem IsEliminationOrder.extend {P : PDAG n} {rank : Fin n → Nat}
    (h : P.IsEliminationOrder rank) : ∃ G, P.Extends G := by
  classical
  let G : DAG n :=
    ⟨fun u v => decide (P.adjacent u v ∧ rank u < rank v), rank,
      fun _ _ e => (of_decide_eq_true e).2⟩
  have edge {u v} : G.edge u v = true ↔ P.adjacent u v ∧ rank u < rank v :=
    decide_eq_true_iff
  have skeleton (u v) : P.adjacent u v ↔ Adjacent G u v := by
    constructor
    · intro adjacent
      have ne : rank u ≠ rank v := fun e => P.no_loops u (h.1 e ▸ adjacent)
      rcases Nat.lt_or_gt_of_ne ne with before | after
      · exact .inl (edge.mpr ⟨adjacent, before⟩)
      · exact .inr (edge.mpr ⟨P.adjacent_symm adjacent, after⟩)
    · exact fun a => a.elim (fun e => (edge.mp e).1) (fun e => P.adjacent_symm (edge.mp e).1)
  have arrows (u v) (a : P.arrow u v) : G.edge u v = true := by
    refine edge.mpr ⟨P.arrow_adjacent a, Nat.lt_of_not_ge ?_⟩
    intro before
    exact (h.2 u).1 v before a
  refine ⟨G, ⟨skeleton, arrows, ?_⟩⟩
  intro u v w c
  have left := edge.mp c.2.2.1
  have right := edge.mp c.2.2.2
  have absent : ¬ P.adjacent u w := fun a => c.2.1 ((skeleton u w).mp a)
  exact ⟨c.1, absent, (h.2 v).arrows_of_nonadjacent_parents
    (Nat.le_of_lt left.2) (Nat.le_of_lt right.2) c.1 absent left.1 right.1⟩

/-- Corollary 4.4. The input has a consistent DAG extension exactly when
successive potential-sink elimination is possible. -/
theorem extendable_iff_elimination_order (P : PDAG n) :
    (∃ G, P.Extends G) ↔ ∃ rank, P.IsEliminationOrder rank :=
  ⟨fun ⟨_, h⟩ => h.has_elimination_order, fun ⟨_, h⟩ => h.extend⟩

/-- Every nonempty extendable input has a potential sink. The maximal
elimination rank belongs to such a vertex. -/
theorem Extends.exists_potential_sink {P : PDAG n} {G : DAG n} (h : P.Extends G)
    (nonempty : Nonempty (Fin n)) : ∃ v, P.IsPotentialSink (fun _ => True) v := by
  obtain ⟨rank, order⟩ := h.has_elimination_order
  obtain ⟨u⟩ := nonempty
  let ranks := (List.finRange n).map rank
  have mem (w : Fin n) : rank w ∈ ranks :=
    List.mem_map.mpr ⟨w, List.mem_finRange _, rfl⟩
  cases greatest : ranks.max? with
  | none =>
    have empty : ranks = [] := List.max?_eq_none_iff.mp greatest
    simpa [empty] using mem u
  | some maximum =>
    obtain ⟨present, upper⟩ := List.max?_eq_some_iff.mp greatest
    obtain ⟨v, _, hv⟩ := List.mem_map.mp present
    have active (w : Fin n) : rank w ≤ rank v := hv ▸ upper _ (mem w)
    exact ⟨v, ⟨fun w _ => (order.2 v).1 w (active w),
      fun x y _ _ => (order.2 v).2 x y (active x) (active y)⟩⟩

/-- Delete the incident edges of `v`, retaining its label as an isolated vertex. -/
def delete (P : PDAG n) (v : Fin n) : PDAG n where
  adjacent u w := u ≠ v ∧ w ≠ v ∧ P.adjacent u w
  arrow u w := u ≠ v ∧ w ≠ v ∧ P.arrow u w
  adjacent_symm a := ⟨a.2.1, a.1, P.adjacent_symm a.2.2⟩
  no_loops u a := P.no_loops u a.2.2
  arrow_adjacent a := ⟨a.1, a.2.1, P.arrow_adjacent a.2.2⟩

private theorem delete_undirected {P : PDAG n} {v u w : Fin n} :
    (P.delete v).undirected u w ↔ u ≠ v ∧ w ≠ v ∧ P.undirected u w := by
  by_cases hu : u = v <;> by_cases hw : w = v <;> simp [undirected, delete, hu, hw]

private theorem IsEliminationOrder.delete {P : PDAG n} {rank : Fin n → Nat}
    (h : P.IsEliminationOrder rank) (v : Fin n) : (P.delete v).IsEliminationOrder rank := by
  refine ⟨h.1, fun w => ⟨fun u before a => (h.2 w).1 u before a.2.2, ?_⟩⟩
  intro u x beforeU beforeX distinct edge other
  obtain ⟨hu, _, openU⟩ := delete_undirected.mp edge
  have keepX : x ≠ v ∧ (P.undirected x w ∨ P.arrow x w) :=
    other.elim (fun a => ⟨(delete_undirected.mp a).1, .inl (delete_undirected.mp a).2.2⟩)
      (fun a => ⟨a.1, .inr a.2.2⟩)
  exact ⟨hu, keepX.1, (h.2 w).2 u x beforeU beforeX distinct openU keepX.2⟩

/-- Lift an extension of the remaining graph by keeping all of its arrows
between surviving vertices and directing each edge incident to the chosen
potential sink toward that sink. -/
theorem Extends.append_potential_sink {P : PDAG n} {v : Fin n} {G : DAG n}
    (ext : (P.delete v).Extends G) (sink : P.IsPotentialSink (fun _ => True) v) :
    ∃ H, P.Extends H ∧
      (∀ u, H.edge v u = false) ∧
      (∀ u, H.edge u v = true ↔ P.adjacent u v) ∧
      (∀ u w, u ≠ v → w ≠ v → H.edge u w = G.edge u w) := by
  classical
  let edge (u w : Fin n) :=
    if u = v then false else if w = v then decide (P.adjacent u v) else G.edge u w
  let rank (u : Fin n) := if u = v then G.rankBound else G.rank u
  have increases (u w) (a : edge u w = true) : rank u < rank w := by
    by_cases hu : u = v
    · simp [edge, hu] at a
    · by_cases hw : w = v
      · simpa [rank, hu, hw] using G.rank_lt_bound u
      · have before := G.edge_increases u w (by simpa [edge, hu, hw] using a)
        simpa [rank, hu, hw] using before
  let H : DAG n := ⟨edge, rank, increases⟩
  have outgoing (u) : H.edge v u = false := by simp [H, edge]
  have incoming (u) : H.edge u v = true ↔ P.adjacent u v := by
    by_cases hu : u = v
    · subst u
      simp [H, edge, P.no_loops]
    · simp [H, edge, hu]
  have stayed (u w) (hu : u ≠ v) (hw : w ≠ v) : H.edge u w = G.edge u w := by
    simp [H, edge, hu, hw]
  have skeleton (u w) : P.adjacent u w ↔ Adjacent H u w := by
    by_cases hu : u = v
    · subst u
      exact ⟨fun a => .inr ((incoming w).mpr (P.adjacent_symm a)),
        fun a => a.elim (fun impossible => by simp [outgoing] at impossible)
          (fun back => P.adjacent_symm ((incoming w).mp back))⟩
    · by_cases hw : w = v
      · subst w
        exact ⟨fun a => .inl ((incoming u).mpr a),
          fun a => a.elim (incoming u).mp (fun impossible => by simp [outgoing] at impossible)⟩
      · simpa [delete, hu, hw, Adjacent, stayed u w hu hw, stayed w u hw hu]
          using ext.skeleton u w
  refine ⟨H, ⟨skeleton, ?_, ?_⟩, outgoing, incoming, stayed⟩
  · intro u w a
    have hu : u ≠ v := fun equal => sink.1 w trivial (equal ▸ a)
    by_cases hw : w = v
    · subst w
      exact (incoming u).mpr (P.arrow_adjacent a)
    · rw [stayed u w hu hw]
      exact ext.arrows u w ⟨hu, hw, a⟩
  · intro u w z c
    have absent : ¬ P.adjacent u z := fun a => c.2.1 ((skeleton u z).mp a)
    by_cases hw : w = v
    · subst w
      exact ⟨c.1, absent, sink.arrows_of_nonadjacent_parents trivial trivial c.1 absent
        ((incoming u).mp c.2.2.1) ((incoming z).mp c.2.2.2)⟩
    · have without {u} (a : H.edge u w = true) : u ≠ v := by
        intro equal
        subst u
        simp [outgoing] at a
      have hu := without c.2.2.1
      have hz := without c.2.2.2
      have previous : UnshieldedCollider G u w z :=
        ⟨c.1, fun a => absent (((ext.skeleton u z).mpr a).2.2),
          stayed u w hu hw ▸ c.2.2.1, stayed z w hz hw ▸ c.2.2.2⟩
      have old := ext.colliders u w z previous
      exact ⟨c.1, absent, old.2.2.1.2.2, old.2.2.2.2.2⟩

/-- Any currently eligible potential sink can be deleted. Extendability
of the remaining induced graph is equivalent to extendability of the input. -/
theorem extendable_iff_delete_potential_sink {P : PDAG n} {v : Fin n}
    (sink : P.IsPotentialSink (fun _ => True) v) :
    (∃ G, P.Extends G) ↔ ∃ G, (P.delete v).Extends G := by
  constructor
  · rintro ⟨_, h⟩
    obtain ⟨_, order⟩ := h.has_elimination_order
    exact (order.delete v).extend
  · rintro ⟨_, h⟩
    obtain ⟨H, extension, _⟩ := h.append_potential_sink sink
    exact ⟨H, extension⟩

end PDAG
end
end OpenCausalScience.Papers.WienobstEtAl2021.PotentialSink
