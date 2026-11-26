module
public import OpenCausalScience.Papers.AnderssonEtAl1997.Condensation
public import OpenCausalScience.Papers.AnderssonEtAl1997.PerfectOrientation

/-! Andersson, Madigan and Perlman (1997), Proposition 4.1.
After temporarily forgetting arrows inside the strongly connected
components, reorient any one component to realize either direction.
Thus no forgotten arrow was compelled. The chain components are chordal.
-/

namespace OpenCausalScience.Papers.AnderssonEtAl1997.Characterization

open OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
open OpenCausalScience.Papers.AnderssonEtAl1997.Condensation
open OpenCausalScience.Papers.AnderssonEtAl1997.PerfectOrientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.ChainComponents

@[expose] public section

variable {n m : Nat}

noncomputable def componentDAG (G : DAG n) (c : Nat) : DAG n where
  edge u v :=
    if label G u = c ∧ label G v = c then G.edge u v else false
  rank := G.rank
  edge_increases u v edge := by
    by_cases within : label G u = c ∧ label G v = c
    · exact G.edge_increases u v (by simpa [within] using edge)
    · simp [within] at edge

theorem adjacent_in_component_dag {G : DAG n} {c : Nat} {u v : Fin n} :
    Adjacent (componentDAG G c) u v ↔ (components G).adjacency c u v := by
  change Adjacent (componentDAG G c) u v ↔ Adjacent G u v ∧ label G u = c ∧ label G v = c
  by_cases inside : label G u = c ∧ label G v = c
  · simp [Adjacent, componentDAG, inside.1, inside.2]
  · have opposite : ¬ (label G v = c ∧ label G u = c) := fun pair => inside pair.symm
    simp [Adjacent, componentDAG, inside, opposite]

/-- The restriction of the original DAG to a condensation component
has no unshielded collider, since collider arrows survived condensation. -/
theorem no_collider_in_component (G : DAG n) (c : Nat) (a b d : Fin n) :
    ¬ UnshieldedCollider (componentDAG G c) a b d := by
  intro collider
  have insideAB := adjacent_in_component_dag.mp (.inl collider.2.2.1)
  have insideDB := adjacent_in_component_dag.mp (.inl collider.2.2.2)
  have notAdjacent : ¬ Adjacent G a d := fun edge =>
    collider.2.1 (adjacent_in_component_dag.mpr ⟨edge, insideAB.2.1, insideDB.2.1⟩)
  have edgeInBase {u v : Fin n} (lu : label G u = c) (lv : label G v = c)
      (edge : (componentDAG G c).edge u v = true) : G.edge u v = true := by
    simpa [componentDAG, lu, lv] using edge
  have ab := edgeInBase insideAB.2.1 insideAB.2.2 collider.2.2.1
  have db := edgeInBase insideDB.2.1 insideDB.2.2 collider.2.2.2
  have fixed := (contains_colliders G a b d ⟨collider.1, notAdjacent, ab, db⟩).1
  exact Nat.ne_of_lt (label_lt_of_across fixed) (insideAB.2.1.trans insideAB.2.2.symm)

theorem base_extends_condensation (G : DAG n) : Extension G (AcrossArrow G) G :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ edge => compelled_in_base edge.1⟩

theorem same_d_connections_of_condensation_extension {G H : DAG n}
    (extension : Extension G (AcrossArrow G) H) : SameDConnections G H :=
  VermaPearl1990.Equivalence.same_dConnections_iff_same_signature.mpr
    ⟨extension.skeleton, extension.colliders⟩

/-- Every adjacency within a condensation component can have either
orientation in the original Markov equivalence class. -/
theorem possible_inside {G : DAG n} {u v : Fin n} (within : SameComponent G u v)
    (adjacent : Adjacent G u v) : PossibleArrow G u v := by
  let c := label G v
  have hu : label G u = c := label_eq_iff.mpr within
  have inside : Adjacent (componentDAG G c) u v :=
    adjacent_in_component_dag.mpr ⟨adjacent, hu, rfl⟩
  obtain ⟨H, skeleton, noColliders, orient⟩ :=
    exists_orientation_of_adjacent (no_collider_in_component G c) inside
  obtain ⟨K, ext, installed⟩ :=
    (components G).replace_component (base_extends_condensation G) (contains_colliders G)
      c H (fun x y => (skeleton x y).symm.trans adjacent_in_component_dag) noColliders
  exact ⟨K, same_d_connections_of_condensation_extension ext,
    (installed u v hu rfl).trans orient⟩

/-- No compelled arrow lies on a semidirected cycle. This is the chain
graph conclusion of Proposition 4.1(i). -/
theorem compelled_has_no_semidirected_return {G : DAG n} {u v : Fin n}
    (fixed : Compelled G u v) (back : PossibleReach G v u) : False := by
  have forward := possible_iff.mpr (.inl fixed)
  obtain ⟨H, same, reverse⟩ := possible_inside ⟨back, .extend (.refl u) forward⟩
    (Or.inr (compelled_in_base fixed))
  exact H.no_directed_cycle u (.extend (.single (fixed H same)) reverse)

theorem across_iff_compelled {G : DAG n} {u v : Fin n} :
    AcrossArrow G u v ↔ Compelled G u v :=
  ⟨And.left, fun fixed => ⟨fixed, compelled_has_no_semidirected_return fixed⟩⟩

/-- The essential graph itself has topologically ordered components and
inherits every external parent throughout its component. -/
noncomputable def essentialComponents (G : DAG n) : Components G (Compelled G) where
  label := label G
  fixed_increases _ _ edge := (components G).fixed_increases _ _ (across_iff_compelled.mpr edge)
  directions_between _ _ edge different :=
    ((components G).directions_between _ _ edge different).imp And.left And.left
  inherits_parents _ _ _ edge equal :=
    ((components G).inherits_parents _ _ _ (across_iff_compelled.mpr edge) equal).1

/-- Proposition 4.1(ii). No chain-component skeleton has an induced
chordless cycle of length at least four. -/
theorem chain_components_chordal (G : DAG n) (c : Nat)
    (cycle : Meek1995.ChordlessCycle.Cycle (componentDAG G c) m) : False := by
  obtain ⟨k, collider⟩ := Meek1995.ChordlessCycle.contains_collider cycle
  exact no_collider_in_component _ _ _ _ _ collider

theorem contains_essential_colliders (G : DAG n) : ContainsColliders G (Compelled G) :=
  fun _ _ _ collider => collider_arrows_compelled collider

/-- Each clique inside an essential-graph component can be ordered as
prescribed and placed before its remaining neighbors in a representative DAG. -/
theorem extend_with_initial_clique (G : DAG n) (c : Nat)
    (clique : Fin n → Prop)
    (inside : ∀ v, clique v → label G v = c)
    (pairwise : ∀ u v, clique u → clique v → u ≠ v → Adjacent G u v)
    (priority : Fin n → Nat) :
    ∃ K : DAG n, Extension G (Compelled G) K ∧
      (∀ u v, clique u → clique v → priority u < priority v →
        (essentialComponents G).adjacency c u v → K.edge u v = true) ∧
      (∀ u v, clique u → ¬ clique v →
        (essentialComponents G).adjacency c u v → K.edge u v = true) := by
  have componentClique (u v : Fin n) (hu : clique u) (hv : clique v) (ne : u ≠ v) :
      Adjacent (componentDAG G c) u v :=
    adjacent_in_component_dag.mpr ⟨pairwise u v hu hv ne, inside u hu, inside v hv⟩
  obtain ⟨H, skeleton, noColliders, beforeOutside, ordered⟩ :=
    exists_orientation_with_ordered_initial_clique (no_collider_in_component G c)
      clique componentClique priority
  obtain ⟨K, ext, installed⟩ := (components G).replace_component
    (base_extends_condensation G) (contains_colliders G) c H
    (fun u v => (skeleton u v).symm.trans adjacent_in_component_dag) noColliders
  refine ⟨K, extension_iff_same_d_connections.mpr
    (same_d_connections_of_condensation_extension ext), ?_, ?_⟩
  · intro u v hu hv order adj
    exact (installed u v adj.2.1 adj.2.2).trans
      (ordered u v hu hv order (adjacent_in_component_dag.mpr adj))
  · intro u v hu hv adj
    have hAdjacent := (skeleton u v).mp (adjacent_in_component_dag.mpr adj)
    have forward := hAdjacent.resolve_right (fun reverse =>
      Nat.lt_asymm (beforeOutside u v hu hv) (H.edge_increases _ _ reverse))
    exact (installed u v adj.2.1 adj.2.2).trans forward

end
end OpenCausalScience.Papers.AnderssonEtAl1997.Characterization
