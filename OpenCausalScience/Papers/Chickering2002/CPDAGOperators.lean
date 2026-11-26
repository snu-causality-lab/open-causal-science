module
public import OpenCausalScience.Papers.AnderssonEtAl1997.Characterization
public import OpenCausalScience.Papers.Chickering2002.OperatorTests

/-! Chickering (2002), Theorems 15 and 17, for the essential graph of
a finite DAG. Andersson, Madigan and Perlman's component theorem supplies
the order and the consistent extensions with prescribed cliques.
-/

namespace OpenCausalScience.Papers.Chickering2002.CPDAGOperators

open OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph (Compelled)
open OpenCausalScience.Papers.AnderssonEtAl1997.Characterization
open OpenCausalScience.Papers.Chickering2002.OperatorTests
open OpenCausalScience.Papers.Chickering2002.Insert (Vertices NeighborsAdjacentToSource)
open OpenCausalScience.Papers.Meek1995.Closure

@[expose] public section

variable {n : Nat} {base : DAG n} {x y : Fin n}

theorem cliques_orientable (base : DAG n) : CliquesOrientable (essentialComponents base) :=
  extend_with_initial_clique base

/-- The clique and path-blocking tests characterize valid Insert operators
on the essential graph of a finite DAG. -/
theorem insert_iff_clique_and_blocks (tails : Vertices n)
    (choice : Insert.Choice base (Compelled base) x y tails) :
    (∃ K H : DAG n, Extension base (Compelled base) K ∧ K.IsInsertion H x y ∧
      Insert.Realizes base (Compelled base) x y tails H) ↔
      IsClique base (fun v => NeighborsAdjacentToSource base (Compelled base) x y v ∨ tails v) ∧
      ¬ Insert.AvoidingWalk base (Compelled base)
        (fun v => NeighborsAdjacentToSource base (Compelled base) x y v ∨ tails v) y x :=
  insert_iff_clique_and_blocks_of_initial_cliques (essentialComponents base)
    (cliques_orientable base) (contains_essential_colliders base) tails choice

/-- The clique test characterizes valid Delete operators on the essential
graph of a finite DAG. -/
theorem delete_iff_clique (heads : Vertices n)
    (xy : Compelled base x y ∨ Unoriented base (Compelled base) x y)
    (valid : ∀ v, heads v → NeighborsAdjacentToSource base (Compelled base) x y v) :
    (∃ K : DAG n, Extension base (Compelled base) K ∧ K.edge x y = true ∧
      Delete.Realizes base (Compelled base) x y heads (K.deleteArrow x y)) ↔
      IsClique base (fun v => NeighborsAdjacentToSource base (Compelled base) x y v ∧ ¬ heads v) :=
  delete_iff_clique_of_initial_cliques (essentialComponents base)
    (cliques_orientable base) (contains_essential_colliders base) heads xy valid

end
end OpenCausalScience.Papers.Chickering2002.CPDAGOperators
