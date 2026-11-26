module
public import OpenCausalScience.Papers.Chickering2002.Delete
public import OpenCausalScience.Papers.Meek1995.ChainComponents

/-! GES Insert and Delete with the component structure used in
Chickering (2002), Lemma 36. The clique order is realized by rooted
join-tree construction and substitution into the full DAG. -/

namespace OpenCausalScience.Papers.Chickering2002.CliqueExtensions

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.ChainComponents
open OpenCausalScience.Papers.Meek1995.JoinTreeOrientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.Chickering2002.Insert (Vertices NeighborsAdjacentToSource)

@[expose] public section

variable {n m : Nat} {base G : DAG n} {fixed : Orientations n} {x y : Fin n}

/-- The clique rooted for an Insert consists of Y and the reversible
parents of Y selected by the source adjacency or by the argument T. -/
def insertClique (base : DAG n) (fixed : Orientations n) (x y : Fin n)
    (tails : Vertices n) (v : Fin n) : Prop :=
  v = y ∨ NeighborsAdjacentToSource base fixed x y v ∨ tails v

private theorem opposite_absent {H : DAG n} {u v : Fin n} (edge : H.edge u v = true) :
    H.edge v u ≠ true :=
  fun reverse => H.no_directed_cycle u (.extend (.single edge) reverse)

private theorem adjacent_distinct {G : DAG n} {u v : Fin n} (edge : Adjacent G u v) : u ≠ v := by
  intro same
  subst v
  exact G.no_directed_cycle u (.single (edge.elim id id))

/-- The sufficient direction of the Insert test under rooted component
data. The selected extension is constructed inside the proof. -/
theorem insert_from_root_clique (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed) (tails : Vertices n)
    (choice : Insert.Choice base fixed x y tails)
    (tree : RootedJoinTree (components.adjacency (components.label y)) m)
    (inRoot : ∀ v, insertClique base fixed x y tails v → tree.inBag tree.root v)
    (blocked : ¬ Insert.AvoidingWalk base fixed
      (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) y x) :
    ∃ K H : DAG n, Extension base fixed K ∧ K.IsInsertion H x y ∧
      Insert.Realizes base fixed x y tails H := by
  classical
  let priority (v : Fin n) := if v = y then 1 else 0
  obtain ⟨K, keep, order, away⟩ := components.extend_with_root_clique ext contains _ tree
    (insertClique base fixed x y tails) inRoot priority
  have step {v : Fin n} (edge : Unoriented base fixed v y) :
      components.adjacency (components.label y) v y :=
    ⟨edge.1, components.label_eq_of_unoriented edge, rfl⟩
  have parent {v : Fin n} (selected : NeighborsAdjacentToSource base fixed x y v ∨ tails v) :
      K.edge v y = true := by
    have openEdge : Unoriented base fixed v y :=
      selected.elim And.left (fun tail => (choice.valid v tail).1)
    exact order v y (.inr selected) (.inl rfl) (by
      simp [priority, adjacent_distinct openEdge.1]) (step openEdge)
  have selection : Insert.MatchesTails base K fixed x y tails := by
    intro v openEdge nonadjacent
    constructor
    · intro toward
      by_cases picked : tails v
      · exact picked
      · have notIn : ¬ insertClique base fixed x y tails v := by
          rintro (rfl | common | own)
          · exact adjacent_distinct openEdge.1 rfl
          · exact nonadjacent common.2
          · exact picked own
        have out := away y v (.inl rfl) notIn
          ⟨Or.symm openEdge.1, rfl, components.label_eq_of_unoriented openEdge⟩
        exact (opposite_absent out toward).elim
    · intro picked
      exact parent (.inr picked)
  obtain ⟨H, edit, realizes⟩ :=
    Insert.exists_realization_of_selected_extension keep contains choice selection
      (fun _ => parent) blocked
  exact ⟨K, H, keep, edit, realizes⟩

/-- The Delete clique consists of Y, X if their edge is reversible,
and common reversible neighbors that are outside the argument H. -/
def deleteClique (base : DAG n) (fixed : Orientations n) (x y : Fin n)
    (heads : Vertices n) (v : Fin n) : Prop :=
  v = y ∨ (v = x ∧ Unoriented base fixed x y) ∨
    (NeighborsAdjacentToSource base fixed x y v ∧ ¬ heads v)

/-- The sufficient direction of the Delete test under rooted component
data. The compelled-child implication follows from the component order. -/
theorem delete_from_root_clique (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed) (heads : Vertices n)
    (xy : fixed x y ∨ Unoriented base fixed x y)
    (valid : ∀ v, heads v → NeighborsAdjacentToSource base fixed x y v)
    (tree : RootedJoinTree (components.adjacency (components.label y)) m)
    (inRoot : ∀ v, deleteClique base fixed x y heads v → tree.inBag tree.root v) :
    ∃ K : DAG n, Extension base fixed K ∧ K.edge x y = true ∧
      Delete.Realizes base fixed x y heads (K.deleteArrow x y) := by
  classical
  let priority (v : Fin n) := if v = y then 2 else if v = x then 1 else 0
  obtain ⟨K, keep, order, away⟩ := components.extend_with_root_clique ext contains _ tree
    (deleteClique base fixed x y heads) inRoot priority
  have step {v : Fin n} (edge : Unoriented base fixed v y) :
      components.adjacency (components.label y) v y :=
    ⟨edge.1, components.label_eq_of_unoriented edge, rfl⟩
  have toward : K.edge x y = true := by
    rcases xy with known | openEdge
    · exact keep.oriented _ _ known
    · exact order x y (.inr (.inl ⟨rfl, openEdge⟩)) (.inl rfl) (by
        simp [priority, adjacent_distinct openEdge.1]) (step openEdge)
  have selected : Delete.MatchesHeads base K fixed x y heads := by
    intro v common
    have vy := adjacent_distinct common.1.1
    have vx := (adjacent_distinct common.2).symm
    constructor
    · intro child
      by_cases own : heads v
      · exact own
      · have parent := order v y (.inr (.inr ⟨common, own⟩)) (.inl rfl)
          (by simp [priority, vy, vx]) (step common.1)
        exact (opposite_absent parent child).elim
    · intro own
      have notIn : ¬ deleteClique base fixed x y heads v := by
        rintro (eq | ⟨eq, _⟩ | ⟨_, out⟩)
        · exact vy eq
        · exact vx eq
        · exact out own
      exact away y v (.inl rfl) notIn
        ⟨Or.symm common.1.1, rfl, components.label_eq_of_unoriented common.1⟩
  have compelledChild (v) (known : fixed y v) (edge : K.edge x v = true) : fixed x v := by
    have strict := components.fixed_increases _ _ known
    have bound := components.label_le_of_edge keep toward
    exact components.fixed_of_edge_between keep edge (by omega)
  exact ⟨K, keep, toward,
    Delete.realized_of_matching_heads keep contains toward valid compelledChild selected⟩

end
end OpenCausalScience.Papers.Chickering2002.CliqueExtensions
