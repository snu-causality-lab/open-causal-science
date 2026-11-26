module
public import OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction

/-! # Graphical fixing and the order of choices

Richardson, Evans, Robins and Shpitser (2023), Definition 19 and Lemma 22.
Fixing removes arrowheads at a vertex and marks that vertex as fixed.
Other fixable vertices remain fixable. If a target is reachable, one
can choose any currently fixable vertex outside the target first.
Source: https://doi.org/10.1214/22-AOS2253
-/

namespace OpenCausalScience.Papers.RichardsonEtAl2023.Fixing

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability
open Shpitser2023.FixedPointObstruction

@[expose] public section

variable {n : Nat}

def removeRandom (current : Vertices n) (r : Fin n) : Vertices n :=
  current.filter (· != r)

/-- Delete each edge with an arrowhead at a vertex in the fixed set. -/
def removeArrowheads (graph : MixedGraph n) (fixed : Fin n → Bool) : MixedGraph n where
  edge u a v b := graph.edge u a v b && !(a && fixed u) && !(b && fixed v)
  symmetric u a v b := by
    rw [graph.symmetric u a v b]
    ac_rfl
  loop_free u a b := by simp [graph.loop_free]
  no_arrow_of_undirected {u v w mark} h := by
    have oldEdge : graph.edge u false v false = true := by simpa using h
    simp [graph.no_arrow_of_undirected (w := w) (mark := mark) oldEdge]

def fixGraph (graph : MixedGraph n) (r : Fin n) : MixedGraph n :=
  removeArrowheads graph (· == r)

private theorem Reached.mono {edge₁ edge₂ : Fin n → Fin n → Bool} {small large : Vertices n}
    {seeds : Fin n → Bool} {v : Fin n} (inside : small ⊆ large)
    (edges : ∀ a b, edge₁ a b = true → edge₂ a b = true)
    (path : Reached edge₁ small seeds v) : Reached edge₂ large seeds v := by
  induction path with
  | seed member source => exact .seed (inside member) source
  | step _ member edge ih => exact .step ih (inside member) (edges _ _ edge)

private theorem fixable_of_subgraph {graph subgraph : MixedGraph n} {current remaining : Vertices n}
    {s : Fin n} (inside : remaining ⊆ current)
    (edges : ∀ a h b k, subgraph.edge a h b k = true → graph.edge a h b k = true)
    (fixable : Fixable graph current s) (present : s ∈ remaining) :
    Fixable subgraph remaining s := by
  refine ⟨present, ?_⟩
  intro t distinct directed bidirected
  have oldDirected : descendant graph current s t :=
    Reached.mono inside (fun a b => edges a false b true) directed
  have oldBidirected : t ∈ district graph current s :=
    (mem_district_iff graph current s t).mpr
      (Reached.mono inside (fun a b => edges a true b true)
        ((mem_district_iff subgraph remaining s t).mp bidirected))
  exact fixable.2 t distinct oldDirected oldBidirected

theorem fixable_after_fixing {graph : MixedGraph n} {current : Vertices n} {r s : Fin n}
    (other : s ≠ r) (fixable : Fixable graph current s) :
    Fixable (fixGraph graph r) (removeRandom current r) s := by
  refine fixable_of_subgraph (graph := graph) (current := current)
    (fun _ h => (List.mem_filter.mp h).1) ?_ fixable ?_
  · intro a h b k edge
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp edge).1).1
  · exact List.mem_filter.mpr ⟨fixable.1, bne_iff_ne.mpr other⟩

private theorem edges_determine_graph {first second : MixedGraph n}
    (same : first.edge = second.edge) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Successive graphical fixings delete exactly the arrowheads at the
fixed vertices. Outgoing arrows into still-random vertices survive. -/
theorem fixings_remove_arrowheads_at_fixed_set (graph : MixedGraph n) (order : Vertices n) :
    order.foldl fixGraph graph = removeArrowheads graph order.contains := by
  induction order generalizing graph with
  | nil =>
    apply edges_determine_graph
    funext u a v b
    simp [removeArrowheads]
  | cons r rest ih =>
    rw [List.foldl_cons, ih]
    apply edges_determine_graph
    funext u a v b
    simp only [fixGraph, removeArrowheads, List.contains_cons]
    cases a <;> cases b <;>
      simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.and_true, Bool.not_or] <;>
      ac_rfl

theorem same_graph_after_fixing_same_set (graph : MixedGraph n)
    (first second : Vertices n) (same : ∀ v, v ∈ first ↔ v ∈ second) :
    first.foldl fixGraph graph = second.foldl fixGraph graph := by
  have membership : first.contains = second.contains := by
    funext v
    cases a : first.contains v <;> cases b : second.contains v <;>
      simp_all
  rw [fixings_remove_arrowheads_at_fixed_set, fixings_remove_arrowheads_at_fixed_set, membership]

theorem fixings_retain_random_complement (current order : Vertices n) :
    order.foldl removeRandom current = current.filter (!order.contains ·) := by
  induction order generalizing current with
  | nil => exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | cons r rest ih =>
    rw [List.foldl_cons, ih]
    simp only [removeRandom, List.filter_filter, List.contains_cons, Bool.not_or, bne, Bool.and_comm]

private theorem remove_random_comm (current : Vertices n) (r s : Fin n) :
    removeRandom (removeRandom current r) s = removeRandom (removeRandom current s) r := by
  simp [removeRandom, List.filter_filter, Bool.and_comm]

private theorem fixable_after_removing_random {graph : MixedGraph n} {current : Vertices n}
    {r s : Fin n} (other : s ≠ r) (fixable : Fixable graph current s) :
    Fixable graph (removeRandom current r) s :=
  fixable_of_subgraph (fun _ h => (List.mem_filter.mp h).1) (fun _ _ _ _ h => h)
    fixable (List.mem_filter.mpr ⟨fixable.1, bne_iff_ne.mpr other⟩)

private theorem order_after_choice {graph : MixedGraph n} {target current final : Vertices n}
    {r : Fin n} (order : FixingOrder graph target current final)
    (fixable : Fixable graph current r) (outside : r ∉ target) (retained : final ⊆ target) :
    FixingOrder graph target (removeRandom current r) final := by
  induction order with
  | empty current =>
    exact (outside (retained fixable.1)).elim
  | @step current final s valid avoids tail ih =>
    by_cases same : r = s
    · subst r
      exact tail
    · apply FixingOrder.step (fixable_after_removing_random (Ne.symm same) valid) avoids
      rw [show (removeRandom current r).filter (· != s) =
        removeRandom (removeRandom current s) r from remove_random_comm current r s]
      exact ih (fixable_after_removing_random same fixable) retained

/-- A valid first choice can be moved to the front of an existing order.
The ambient edges used to test fixability lie within the current random set. -/
theorem reachable_after_fixable_choice {graph : MixedGraph n} {target current : Vertices n}
    {r : Fin n} (order : FixingOrder graph target current target)
    (fixable : Fixable graph current r) (outside : r ∉ target) :
    FixingOrder graph target (removeRandom current r) target :=
  order_after_choice order fixable outside (fun _ h => h)

end
end OpenCausalScience.Papers.RichardsonEtAl2023.Fixing
