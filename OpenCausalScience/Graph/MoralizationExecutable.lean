module
public import OpenCausalScience.Graph.Moralization

/-! # A Boolean specification of CGA's DAG separation routine

CGA finds the ancestors of the query sets, adds skeleton and co-parent
edges among ancestral vertices, and searches from the left set while
blocking the conditioned vertices. The order of graph traversal is
immaterial to the result. This executable uses a FIFO worklist.
-/

namespace OpenCausalScience.Moralization.Query

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026
open BayesBall BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G : DAG n}

/-- Test membership in the ancestor set used to build the moral graph. -/
def relevantBool (Q : Query G) (u : Fin n) : Bool :=
  (List.finRange n).any fun w =>
    (Q.left w || (Q.right w || Q.condition.member w)) &&
      (u == w || hasDirectedWalk G u w)

theorem relevantBool_iff (Q : Query G) (u : Fin n) :
    Q.relevantBool u = true ↔ Q.relevant u := by
  rw [Q.relevant_iff]
  simp [relevantBool, List.any_eq_true, Ancestor, hasDirectedWalk_iff]

/-- Neighbors in the ancestral moral graph after blocking conditioning vertices. -/
def moralNeighbors (Q : Query G) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    let coParents := (List.finRange n).any fun c =>
      Q.relevantBool c && (G.edge u c && G.edge v c)
    Q.relevantBool u && (Q.relevantBool v &&
      (!Q.condition.member u && (!Q.condition.member v &&
        (u != v && (G.edge u v || (G.edge v u || coParents))))))

theorem mem_moralNeighbors_iff (Q : Query G) (u v : Fin n) :
    v ∈ Q.moralNeighbors u ↔ Q.MoralEdge u v := by
  simp only [moralNeighbors, List.mem_filter, List.mem_finRange, true_and,
    Bool.and_eq_true, Bool.or_eq_true_iff, Bool.not_eq_true', bne_iff_ne,
    List.any_eq_true, Q.relevantBool_iff]
  constructor
  · rintro ⟨hu, hv, hcu, hcv, hd, he⟩
    exact ⟨hu, hv, hcu, hcv, hd, he⟩
  · rintro ⟨hu, hv, hcu, hcv, hd, he⟩
    exact ⟨hu, hv, hcu, hcv, hd, he⟩

private theorem MoralWalk.snoc {Q : Query G} {u v w : Fin n}
    (route : Q.MoralWalk u v) (edge : Q.MoralEdge v w) : Q.MoralWalk u w := by
  induction route with
  | nil _ => exact .cons edge (.nil w)
  | cons step _ ih => exact .cons step (ih edge)

/-- Every vertex reachable from the left set in the unblocked moral graph. -/
def moralVisited (Q : Query G) : List (Fin n) :=
  explore Q.moralNeighbors (List.finRange n) ((List.finRange n).filter Q.left)

theorem mem_moralVisited_iff (Q : Query G) (v : Fin n) :
    v ∈ Q.moralVisited ↔ ∃ u, Q.left u = true ∧ Q.MoralWalk u v := by
  unfold moralVisited
  constructor
  · intro found
    refine explore_sound (P := fun w => ∃ u, Q.left u = true ∧ Q.MoralWalk u w) ?_ ?_ found
    · rintro a b ⟨u, hu, route⟩ move
      exact ⟨u, hu, route.snoc ((Q.mem_moralNeighbors_iff a b).mp move)⟩
    · intro u mem
      exact ⟨u, (List.mem_filter.mp mem).2, .nil u⟩
  · rintro ⟨u, hu, route⟩
    have seed : u ∈ explore Q.moralNeighbors (List.finRange n) ((List.finRange n).filter Q.left) :=
      explore_covers (List.mem_finRange u) (List.mem_filter.mpr ⟨List.mem_finRange u, hu⟩)
    clear hu
    induction route with
    | nil _ => exact seed
    | cons edge _ ih =>
      exact ih (explore_closed seed ((Q.mem_moralNeighbors_iff _ _).mpr edge) (List.mem_finRange _))

/-- Return true if the search from the left set cannot visit the right set. -/
def dagMoralSeparated (Q : Query G) : Bool :=
  !(Q.moralVisited.any Q.right)

theorem dagMoralSeparated_eq_true_iff (Q : Query G)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false) :
    Q.dagMoralSeparated = true ↔ ¬ Q.DConnection := by
  have connection : Q.moralVisited.any Q.right = true ↔ Q.MoralConnection := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨y, visited, hy⟩
      obtain ⟨x, hx, route⟩ := (Q.mem_moralVisited_iff y).mp visited
      exact ⟨x, y, hx, hy, route⟩
    · rintro ⟨x, y, hx, hy, route⟩
      exact ⟨y, (Q.mem_moralVisited_iff y).mpr ⟨x, hx, route⟩, hy⟩
  rw [dagMoralSeparated, Bool.not_eq_true', Bool.eq_false_iff]
  exact (not_congr connection).trans
    (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside).symm

end

end OpenCausalScience.Moralization.Query
