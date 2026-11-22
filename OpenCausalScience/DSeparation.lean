module
public import Causalean.Graph.DSep.Separation

/-! # Conditioning on a collider or its descendant

In the DAG `X → M ← Y` with `M → D`, the collider at `M` blocks the walk
from `X` to `Y` when nothing is conditioned on. Conditioning on either `M`
or `D` activates the collider.
-/

namespace OpenCausalScience.DSeparation

@[expose] public section

open Causalean.Graph

inductive Vertex
  | x | y | m | d
  deriving DecidableEq

instance : Fintype Vertex where
  elems := {.x, .y, .m, .d}
  complete v := by cases v <;> decide

def dagFromLevels (arrow : Vertex → Vertex → Bool) (level : Vertex → Nat)
    (increases : ∀ u v, arrow u v = true → level u < level v) : DAG Vertex where
  edge u v := arrow u v = true
  decEdge _ _ := inferInstance
  acyclic := DAG.acyclic_of_topoOrder (r := (· < · : Nat → Nat → Prop)) (τ := level) increases

def colliderArrow : Vertex → Vertex → Bool
  | .x, .m | .y, .m | .m, .d => true
  | _, _ => false

def colliderLevel : Vertex → Nat
  | .x | .y => 0
  | .m => 1
  | .d => 2

/-- The graph `X → M ← Y`, `M → D`. -/
def colliderGraph : DAG Vertex := dagFromLevels colliderArrow colliderLevel (by
  intro u v h
  cases u <;> cases v <;> simp_all [colliderArrow, colliderLevel])

/-- For conditioning sets excluding `X` and `Y`, d-separation means there is no active
walk from `X` to `Y`. This connects Causalean's Bayes Ball definition to the walk rule. -/
theorem dSeparated_iff_noActiveWalk (Z : Finset Vertex)
    (hx : Vertex.x ∉ Z) (hy : Vertex.y ∉ Z) :
    colliderGraph.dSep {.x} {.y} Z ↔
      ¬ ∃ p : List Vertex, 2 ≤ p.length ∧ colliderGraph.IsActiveWalk Z p ∧
        p.head? = some .x ∧ p.getLast? = some .y := by
  have reachable_iff_walk :
      Vertex.y ∈ colliderGraph.bbReachableVertices Z {.x} ↔
        ∃ p : List Vertex, 2 ≤ p.length ∧ colliderGraph.IsActiveWalk Z p ∧
          p.head? = some .x ∧ p.getLast? = some .y := by
    simpa using colliderGraph.bbReachableVertices_iff_activeWalk {.x} Z .y
  simp [DAG.dSep, hx, hy, reachable_iff_walk]

theorem dSeparated_given_empty : colliderGraph.dSep {.x} {.y} ∅ := by decide

theorem dConnected_given_collider : ¬ colliderGraph.dSep {.x} {.y} {.m} := by decide

theorem dConnected_given_descendant : ¬ colliderGraph.dSep {.x} {.y} {.d} := by decide

end

end OpenCausalScience.DSeparation
