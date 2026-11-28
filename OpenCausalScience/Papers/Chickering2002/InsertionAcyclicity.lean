module
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap

/-! # Acyclicity of the insertions in Apply-Edge-Operation

Chickering (2002), Figure 2 and Lemma 30. These results check the
acyclicity part of Steps 4, 7, and 8. Step 8 uses a parent of Z distinct
from Y when adding that parent to Y.
-/

namespace OpenCausalScience.Papers.Chickering2002

open Discovery
open VermaPearl1990.DAGEquivalence
open KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G : DAG n}

private theorem first_arrow {x y : Fin n} (walk : G.DirectedWalk x y) :
    ∃ z, G.edge x z = true ∧ G.ancestor z y := by
  induction walk with
  | single arrow => exact ⟨_, arrow, .inl rfl⟩
  | extend _ arrow ih =>
    obtain ⟨z, first, rest⟩ := ih
    refine ⟨z, first, .inr ?_⟩
    rcases rest with rfl | walk
    · exact .single arrow
    · exact .extend walk arrow

private theorem walk_then_ancestor {x y z : Fin n}
    (leading : G.DirectedWalk x y) (suffix : G.ancestor y z) : G.ancestor x z := by
  rcases suffix with rfl | route
  · exact .inr leading
  · apply Or.inr
    induction route with
    | single arrow => exact .extend leading arrow
    | extend _ arrow ih => exact .extend ih arrow

/-- Step 4 adds an arrow to a sink. -/
theorem insert_into_sink_acyclic {x y : Fin n} (different : x ≠ y)
    (sink : ∀ z, G.edge y z = false) : ∃ H : DAG n, G.IsInsertion H x y :=
  (G.exists_insertion_iff different).mpr fun path => by
    obtain ⟨z, first, _⟩ := first_arrow path
    exact Bool.false_ne_true ((sink z).symm.trans first)

/-- Step 7 adds a shortcut parallel to an existing directed path. -/
theorem insert_shortcut_acyclic {x z : Fin n} (path : G.DirectedWalk x z) :
    ∃ H : DAG n, G.IsInsertion H x z := by
  have ne : x ≠ z := fun h => G.no_directed_cycle x (h ▸ path)
  apply (G.exists_insertion_iff ne).mpr
  intro back
  exact Nat.lt_asymm (G.rank_lt_of_directedWalk path) (G.rank_lt_of_directedWalk back)

/-- Step 8 uses a parent `x` of a maximal child `z` of `y` on a directed
route to `d`. A return path `y` to `x` would exhibit a child of `y`
that precedes `z` and still reaches `d`. -/
theorem insert_parent_of_maximal_child_acyclic {x y z d : Fin n}
    (different : x ≠ y) (parent : G.edge x z = true) (reaches : G.ancestor z d)
    (maximal : ∀ w, G.edge y w = true → G.ancestor w d → ¬ G.DirectedWalk w z) :
    ∃ H : DAG n, G.IsInsertion H x y := by
  apply (G.exists_insertion_iff different).mpr
  intro back
  obtain ⟨w, child, rest⟩ := first_arrow back
  have toZ : G.DirectedWalk w z := by
    rcases rest with rfl | route
    · exact .single parent
    · exact .extend route parent
  exact maximal w child (walk_then_ancestor toZ reaches) toZ

/-- Adding an arrow from a vertex to itself is impossible in a DAG. -/
theorem no_self_insertion (G : DAG n) (x : Fin n) : ¬ ∃ H : DAG n, G.IsInsertion H x x := by
  rintro ⟨H, edit⟩
  exact H.no_directed_cycle x (.single ((edit x x).mpr (.inr ⟨rfl, rfl⟩)))

namespace Step8Example

/-- The labels 0, 1, 2 represent X, Y, Z. -/
def start : DAG 3 where
  edge x y := (x == 0 || x == 1) && y == 2
  rank := Fin.val
  edge_increases := by decide +kernel

def target : DAG 3 where
  edge x y := (x == 0 && (y == 1 || y == 2)) || (x == 2 && y == 1)
  rank x := if x == 1 then 2 else if x == 2 then 1 else 0
  edge_increases := by decide +kernel

theorem target_is_imap : IndependenceMap start target := by
  intro x y cond different outX outY sep
  have complete : ∀ a b : Fin 3, a ≠ b → (target.edge a b || target.edge b a) = true := by
    decide +kernel
  exact ((graphOracle_eq_true_iff target x y cond outX outY).mp sep
    (adjacent_dConnected _ (Bool.or_eq_true_iff.mp (complete x y different)) outX outY)).elim

/-- The target has only sink Y, which has only child Z in the starting
DAG. The parents in the starting DAG force the Step 8 case. -/
theorem step_eight_is_applicable :
    (∀ sink : Fin 3, (∀ w, target.edge sink w = false) ↔ sink = 1) ∧
    (∀ child : Fin 3, start.edge 1 child = true ↔ child = 2) ∧
    (∀ parent : Fin 3, start.edge parent 1 = false) ∧
    start.edge 0 2 = true := by
  decide +kernel

/-- The literal Step 8 parent test admits the tail Y of the arrow to Z. -/
theorem tail_satisfies_printed_parent_test : start.edge 1 2 = true ∧ start.edge 1 1 = false ∧
    ¬ ∃ H : DAG 3, start.IsInsertion H 1 1 := ⟨rfl, rfl, no_self_insertion start 1⟩

end Step8Example

end

end OpenCausalScience.Papers.Chickering2002
