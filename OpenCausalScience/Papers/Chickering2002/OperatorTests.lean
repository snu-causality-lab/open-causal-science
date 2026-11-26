module
public import OpenCausalScience.Papers.Chickering2002.InsertBlocking

/-! The two operator validity tests with abstract chain-component
structure. Root availability is a property of the component
representation, independent of either choice of GES operator. -/

namespace OpenCausalScience.Papers.Chickering2002.OperatorTests

open OpenCausalScience.Papers.Chickering2002.CliqueExtensions
open OpenCausalScience.Papers.Chickering2002.Insert (Vertices NeighborsAdjacentToSource)
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.ChainComponents
open OpenCausalScience.Papers.Meek1995.JoinTreeOrientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {base G : DAG n} {fixed : Orientations n} {x y : Fin n}

def IsClique (base : DAG n) (vertices : Vertices n) : Prop :=
  ∀ u v, vertices u → vertices v → u ≠ v → Adjacent base u v

/-- Each clique inside a component can be contained in the root bag of
a join tree for that component. This is a rooted form of the chordal
component representation used in the operator argument. -/
def RootsAvailable (components : Components base fixed) : Prop :=
  ∀ c (vertices : Vertices n), (∀ u, vertices u → components.label u = c) →
    IsClique base vertices →
      ∃ m, ∃ tree : RootedJoinTree (components.adjacency c) m,
        ∀ u, vertices u → tree.inBag tree.root u


/-- The rooted representation property follows from join trees whose
bags cover their component and whose root can be chosen at any bag. -/
theorem roots_available_of_join_trees (components : Components base fixed)
    (trees : ∀ c, ∃ m, ∃ tree : RootedJoinTree (components.adjacency c) m,
      (∀ v, components.label v = c → ∃ i, tree.inBag i v) ∧
      (∀ i, ∃ rooted : RootedJoinTree (components.adjacency c) m,
        rooted.inBag = tree.inBag ∧ rooted.root = i)) :
    RootsAvailable components := by
  intro c vertices allInside clique
  obtain ⟨_, tree, covered, reroot⟩ := trees c
  obtain ⟨bag, contains⟩ := tree.exists_bag_containing_clique vertices
    (fun u v hu hv ne => ⟨clique u v hu hv ne, allInside u hu, allInside v hv⟩)
    (fun v hv => covered v (allInside v hv))
  obtain ⟨rooted, same, root⟩ := reroot bag
  exact ⟨_, rooted, fun v hv => by rw [same, root]; exact contains v hv⟩

/-- Theorem 15 under the chain-component assumptions and the rooted
join-tree representation. Both tests use the original PDAG. -/
theorem insert_iff_clique_and_blocks (components : Components base fixed)
    (roots : RootsAvailable components) (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed) (tails : Vertices n)
    (choice : Insert.Choice base fixed x y tails) :
    (∃ K H : DAG n, Extension base fixed K ∧ K.IsInsertion H x y ∧
      Insert.Realizes base fixed x y tails H) ↔
      IsClique base (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) ∧
      ¬ Insert.AvoidingWalk base fixed (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) y x := by
  constructor
  · rintro ⟨_, _, before, edit, after⟩
    exact ⟨fun _ _ => Insert.clique_of_realization before contains choice edit after,
      InsertBlocking.blocks_of_realization components before contains tails choice edit after⟩
  · rintro ⟨clique, blocks⟩
    have neighbor {v : Fin n} (h : NeighborsAdjacentToSource base fixed x y v ∨ tails v) :
        Unoriented base fixed v y :=
      h.elim And.left (fun picked => (choice.valid v picked).1)
    obtain ⟨_, tree, root⟩ := roots (components.label y) (insertClique base fixed x y tails)
      (fun _ h => h.elim (fun e => e.symm ▸ rfl)
        (fun selected => components.label_eq_of_unoriented (neighbor selected))) (by
      intro u v hu hv different
      rcases hu with eq | selectedU
      · subst u
        exact hv.elim (fun e => (different e.symm).elim) (fun h => Or.symm (neighbor h).1)
      · rcases hv with eq | selectedV
        · subst v
          exact (neighbor selectedU).1
        · exact clique _ _ selectedU selectedV different)
    exact insert_from_root_clique components ext contains tails choice tree root blocks

/-- Theorem 17 under the chain-component assumptions and the rooted
join-tree representation. The unselected common neighbors must and
can form a clique. -/
theorem delete_iff_clique (components : Components base fixed) (roots : RootsAvailable components)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed) (heads : Vertices n)
    (xy : fixed x y ∨ Unoriented base fixed x y)
    (valid : ∀ v, heads v → NeighborsAdjacentToSource base fixed x y v) :
    (∃ K : DAG n, Extension base fixed K ∧ K.edge x y = true ∧
      Delete.Realizes base fixed x y heads (K.deleteArrow x y)) ↔
      IsClique base (fun v => NeighborsAdjacentToSource base fixed x y v ∧ ¬ heads v) := by
  constructor
  · rintro ⟨_, before, present, after⟩
    exact fun _ _ => Delete.clique_of_realization before contains present after
  · intro clique
    obtain ⟨_, tree, root⟩ := roots (components.label y) (deleteClique base fixed x y heads)
      (by
        intro v h
        rcases h with eq | ⟨eq, openEdge⟩ | ⟨common, _⟩
        · subst v
          rfl
        · subst v
          exact components.label_eq_of_unoriented openEdge
        · exact components.label_eq_of_unoriented common.1) (by
      intro u v hu hv different
      rcases hu with eu | ⟨eu, openU⟩ | ⟨commonU, notU⟩
      · subst u
        rcases hv with ev | ⟨ev, openV⟩ | ⟨commonV, _⟩
        · exact (different ev.symm).elim
        · subst v
          exact Or.symm openV.1
        · exact Or.symm commonV.1.1
      · subst u
        rcases hv with ev | ⟨ev, _⟩ | ⟨commonV, _⟩
        · subst v
          exact openU.1
        · exact (different ev.symm).elim
        · exact commonV.2
      · rcases hv with ev | ⟨ev, _⟩ | ⟨commonV, notV⟩
        · subst v
          exact commonU.1.1
        · subst v
          exact Or.symm commonU.2
        · exact clique _ _ ⟨commonU, notU⟩ ⟨commonV, notV⟩ different)
    exact delete_from_root_clique components ext contains heads xy valid tree root

end
end OpenCausalScience.Papers.Chickering2002.OperatorTests
