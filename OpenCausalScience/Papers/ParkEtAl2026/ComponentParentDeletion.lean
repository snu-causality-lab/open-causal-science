module
public import OpenCausalScience.Papers.AnderssonEtAl1997.Characterization

/-! # Component-wise parent deletion

Theorem 2 of Park et al. (UAI 2026). Delete the incoming arrows from outside
a chain component of the semantic essential graph. Deleting the same arrows
in a representative DAG supplies a consistent extension of the result.

Source: https://proceedings.mlr.press/v337/park26b.html
-/

namespace OpenCausalScience.Papers.ParkEtAl2026.ComponentParentDeletion

open OpenCausalScience
open AnderssonEtAl1997.Characterization (essentialComponents)
open AnderssonEtAl1997.Condensation (label)
open AnderssonEtAl1997.EssentialGraph (Compelled compelled_in_base collider_arrows_compelled)
open Meek1995.Closure (ContainsColliders Extension)
open VermaPearl1990.DAGEquivalence (Adjacent UnshieldedCollider)

@[expose] public section

variable {n : Nat}

/-- A directed edge is removed exactly when it enters the component from outside. -/
def Enters (G : DAG n) (component : Nat) (a b : Fin n) : Prop :=
  label G a ≠ component ∧ label G b = component

/-- Delete external parent arrows in one DAG representative. -/
noncomputable def deleteComponentParents (G : DAG n) (component : Nat) : DAG n := by
  classical
  refine ⟨fun a b => if Enters G component a b then false else G.edge a b, G.rank, ?_⟩
  intro a b edge
  by_cases removed : Enters G component a b
  · simp [removed] at edge
  · exact G.edge_increases a b (by simpa [removed] using edge)

theorem delete_edge_iff {G : DAG n} {component : Nat} {a b : Fin n} :
    (deleteComponentParents G component).edge a b = true ↔
      G.edge a b = true ∧ ¬ Enters G component a b := by
  by_cases removed : Enters G component a b <;> simp [deleteComponentParents, removed]

/-- The compelled arrows retained by the partially directed deletion result. -/
def RetainedCompelled (G : DAG n) (component : Nat) (a b : Fin n) : Prop :=
  Compelled G a b ∧ ¬ Enters G component a b

private theorem compelled_of_cross {G : DAG n} {a b : Fin n}
    (edge : G.edge a b = true) (across : label G a ≠ label G b) : Compelled G a b := by
  rcases (essentialComponents G).directions_between a b (Or.inl edge) across with
    forward | backward
  · exact forward
  · exact (G.no_directed_cycle a (.extend (.single edge) (compelled_in_base backward))).elim

private theorem compelled_after_parent_edge_removal {G : DAG n} {component : Nat}
    {a b c : Fin n} (ab : G.edge a b = true) (cb : G.edge c b = true)
    (ac : G.edge a c = true) (removed : Enters G component a c)
    (kept : ¬ Enters G component a b) : Compelled G a b ∧ Compelled G c b := by
  have outside : label G b ≠ component := fun same => kept ⟨removed.1, same⟩
  have fixedCB : Compelled G c b := compelled_of_cross cb (fun eq => outside (eq.symm.trans removed.2))
  have diffAB : label G a ≠ label G b := by
    intro same
    have reverse := (essentialComponents G).inherits_parents c b a fixedCB same.symm
    exact G.no_directed_cycle a (.extend (.single ac) (compelled_in_base reverse))
  exact ⟨compelled_of_cross ab diffAB, fixedCB⟩

theorem deletion_contains_colliders (G : DAG n) (component : Nat) :
    ContainsColliders (deleteComponentParents G component) (RetainedCompelled G component) := by
  classical
  intro a b c collider
  obtain ⟨ab, keepAB⟩ := delete_edge_iff.mp collider.2.2.1
  obtain ⟨cb, keepCB⟩ := delete_edge_iff.mp collider.2.2.2
  have fixed : Compelled G a b ∧ Compelled G c b := by
    by_cases adjacent : Adjacent G a c
    · rcases adjacent with ac | ca
      · have removed : Enters G component a c := by
          apply Classical.byContradiction
          intro needed
          exact collider.2.1 (Or.inl (delete_edge_iff.mpr ⟨ac, needed⟩))
        exact compelled_after_parent_edge_removal ab cb ac removed keepAB
      · have removed : Enters G component c a := by
          apply Classical.byContradiction
          intro needed
          exact collider.2.1 (Or.inr (delete_edge_iff.mpr ⟨ca, needed⟩))
        obtain ⟨fixedCB, fixedAB⟩ := compelled_after_parent_edge_removal cb ab ca removed keepCB
        exact ⟨fixedAB, fixedCB⟩
    · exact collider_arrows_compelled ⟨collider.1, adjacent, ab, cb⟩
  exact ⟨⟨fixed.1, keepAB⟩, ⟨fixed.2, keepCB⟩⟩

/-- Theorem 2. The component-wise deletion leaves a PDAG with a consistent
extension. The collider invariant identifies the PDAG's colliders with those
of the deleted representative, whose skeleton is the remaining skeleton. -/
theorem component_parent_deletion_valid (G : DAG n) (component : Nat) :
    ContainsColliders (deleteComponentParents G component) (RetainedCompelled G component) ∧
      ∃ H : DAG n, Extension (deleteComponentParents G component) (RetainedCompelled G component) H :=
  ⟨deletion_contains_colliders G component, deleteComponentParents G component,
    fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ kept =>
      delete_edge_iff.mpr ⟨compelled_in_base kept.1, kept.2⟩⟩

end
end OpenCausalScience.Papers.ParkEtAl2026.ComponentParentDeletion
