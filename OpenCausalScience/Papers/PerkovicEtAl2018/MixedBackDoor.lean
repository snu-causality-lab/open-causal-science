module
public import OpenCausalScience.Graph.MixedPath

/-! # Directed-edge deletion in the proper back-door graph

Perković et al. (2018), Definition 6 deletes specified visible directed edges
and keeps the other marked edges. The theorem here shows that every active
path after directed-edge deletion was already active before deletion. The
argument preserves arrowhead marks, including on a parallel bidirected edge.
The remaining proper-path and forbidden-set arguments of Theorem 7 require
additional graph geometry. Visibility is not part of this deletion lemma.

Source: https://jmlr.org/papers/v18/16-319.html.
-/

namespace OpenCausalScience.Papers.PerkovicEtAl2018.MixedBackDoor

@[expose] public section

variable {n : Nat}

/-- Decide whether this marked edge survives a directed-arrow cut. -/
def keepsMarking (cut : Fin n → Fin n → Bool)
    (u : Fin n) (a : Bool) (v : Fin n) (b : Bool) : Bool :=
  match a, b with
  | false, true => !cut u v
  | true, false => !cut v u
  | _, _ => true

/-- Delete the marked arrow `u → v` when `cut u v` is true. -/
def deleteDirected (graph : MixedGraph n) (cut : Fin n → Fin n → Bool) : MixedGraph n where
  edge u a v b := graph.edge u a v b && keepsMarking cut u a v b
  symmetric u a v b := by
    rw [graph.symmetric u a v b]
    cases a <;> cases b <;> rfl
  loop_free u a b := by simp [graph.loop_free]
  no_arrow_of_undirected := by
    intro u v w mark undirected
    have original : graph.edge u false v false = true := (Bool.and_eq_true_iff.mp undirected).1
    rw [graph.no_arrow_of_undirected original]
    rfl

theorem retained_directed_iff (graph : MixedGraph n) (cut : Fin n → Fin n → Bool) (u v : Fin n) :
    (deleteDirected graph cut).edge u false v true = true ↔
      graph.edge u false v true = true ∧ cut u v = false := by
  simp [deleteDirected, keepsMarking]

theorem bidirected_unchanged (graph : MixedGraph n) (cut : Fin n → Fin n → Bool) (u v : Fin n) :
    (deleteDirected graph cut).edge u true v true = graph.edge u true v true := by
  simp [deleteDirected, keepsMarking]

/-- A suffix of directed arrows that visits no treatment vertex. In an
acyclic directed part the vertex sequence is simple. -/
inductive DirectedSuffix (graph : MixedGraph n) (treatment : Fin n → Bool) :
    Fin n → Fin n → Prop
  | done {v} : treatment v = false → DirectedSuffix graph treatment v v
  | step {u v w} : treatment u = false → graph.edge u false v true = true →
      DirectedSuffix graph treatment v w → DirectedSuffix graph treatment u w

/-- The visible first arrow of a proper directed treatment-to-outcome path.
`visible` supplies the graph's directed-edge visibility predicate. -/
def FirstVisibleArrow (graph : MixedGraph n) (treatment outcome : Fin n → Bool)
    (visible : Fin n → Fin n → Bool) (u v : Fin n) : Prop :=
  graph.edge u false v true = true ∧ treatment u = true ∧ visible u v = true ∧
    ∃ y, outcome y = true ∧ DirectedSuffix graph treatment v y

/-- Definition 6 for a fully oriented mixed graph, given its directed-edge
visibility predicate. The graph can retain a bidirected edge at the same pair. -/
noncomputable def properBackDoor (graph : MixedGraph n) (treatment outcome : Fin n → Bool)
    (visible : Fin n → Fin n → Bool) : MixedGraph n := by
  classical
  exact deleteDirected graph (fun u v => decide (FirstVisibleArrow graph treatment outcome visible u v))

theorem proper_backdoor_deletes_iff (graph : MixedGraph n) (treatment outcome : Fin n → Bool)
    (visible : Fin n → Fin n → Bool) (u v : Fin n) (edge : graph.edge u false v true = true) :
    (properBackDoor graph treatment outcome visible).edge u false v true = false ↔
      FirstVisibleArrow graph treatment outcome visible u v := by
  classical
  simp [properBackDoor, deleteDirected, keepsMarking, edge]

private theorem original_edge {graph : MixedGraph n} {cut : Fin n → Fin n → Bool}
    {u v : Fin n} {a b : Bool} (edge : (deleteDirected graph cut).edge u a v b = true) :
    graph.edge u a v b = true := (Bool.and_eq_true_iff.mp edge).1

private theorem original_ancestor {graph : MixedGraph n} {cut : Fin n → Fin n → Bool}
    {conditioning : Fin n → Bool} {u : Fin n}
    (ancestor : (deleteDirected graph cut).AncestorOf conditioning u) :
    graph.AncestorOf conditioning u := by
  induction ancestor with
  | conditioned contained => exact .conditioned contained
  | parent arrow _ ih => exact .parent (original_edge arrow) ih

private theorem original_step {graph : MixedGraph n} {cut : Fin n → Fin n → Bool}
    {conditioning : Fin n → Bool} {u v : MixedGraph.Arrival n}
    (step : (deleteDirected graph cut).Step conditioning u v) : graph.Step conditioning u v := by
  obtain ⟨mark, edge, turn⟩ := step
  refine ⟨mark, original_edge edge, ?_⟩
  cases collider : (u.2 && mark) with
  | false => simpa [MixedGraph.openTurn, collider] using turn
  | true =>
    have activated : (deleteDirected graph cut).AncestorOf conditioning u.1 := by
      simpa [MixedGraph.openTurn, collider] using turn
    simpa [MixedGraph.openTurn, collider] using original_ancestor activated

private theorem original_walk {graph : MixedGraph n} {cut : Fin n → Fin n → Bool}
    {conditioning : Fin n → Bool} {u v : MixedGraph.Arrival n} {visited : List (Fin n)}
    (walk : (deleteDirected graph cut).ActiveWalk conditioning u visited v) :
    graph.ActiveWalk conditioning u visited v := by
  induction walk with
  | nil state => exact .nil state
  | cons step _ ih => exact .cons (original_step step) ih

/-- Collider activation after deletion can only use directed paths that
already existed. Interior noncollider tests and vertex simplicity are unchanged. -/
theorem path_connected_of_deleted (graph : MixedGraph n) (cut : Fin n → Fin n → Bool)
    (left right conditioning : Fin n → Bool)
    (path : (deleteDirected graph cut).PathConnected left right conditioning) :
    graph.PathConnected left right conditioning := by
  obtain ⟨source, mark, first, visited, last, inLeft, edge, walk, inRight, simple⟩ := path
  exact ⟨source, mark, first, visited, last, inLeft, original_edge edge, original_walk walk, inRight, simple⟩

end

end OpenCausalScience.Papers.PerkovicEtAl2018.MixedBackDoor
