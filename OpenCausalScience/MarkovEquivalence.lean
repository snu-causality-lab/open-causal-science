module
public import Causalean.Graph.MarkovEquiv
public import OpenCausalScience.DSeparation

/-! # Markov equivalence on a common skeleton

The chain `X → M → Y` and the fork `X ← M → Y`, each with `M → D`,
have the same skeleton and the same collection of unshielded colliders.
The collider graph `X → M ← Y` with `M → D` shares their skeleton,
but d-separates `X` and `Y` given the empty set.
-/

namespace OpenCausalScience.MarkovEquivalence

@[expose] public section

open Causalean.Graph
open Causalean.Graph.MarkovEquiv (MarkovEquiv SameSkeleton)
open DSeparation (Vertex colliderGraph dagFromLevels dSeparated_given_empty)

def chainArrow : Vertex → Vertex → Bool
  | .x, .m | .m, .y | .m, .d => true
  | _, _ => false

def chainLevel : Vertex → Nat
  | .x => 0
  | .m => 1
  | .y | .d => 2

def chainGraph : DAG Vertex := dagFromLevels chainArrow chainLevel (by
  intro u v h
  cases u <;> cases v <;> simp_all [chainArrow, chainLevel])

def forkArrow : Vertex → Vertex → Bool
  | .m, .x | .m, .y | .m, .d => true
  | _, _ => false

def forkLevel : Vertex → Nat
  | .m => 0
  | _ => 1

def forkGraph : DAG Vertex := dagFromLevels forkArrow forkLevel (by
  intro u v h
  cases u <;> cases v <;> simp_all [forkArrow, forkLevel])

/-- The chain and fork satisfy both conditions of the Verma–Pearl theorem. -/
theorem chain_markovEquiv_fork : MarkovEquiv chainGraph forkGraph :=
  (markovEquiv_iff_sameSkeleton_sameImmoralities chainGraph forkGraph).2 ⟨by decide, by decide⟩

theorem chain_sameSkeleton_collider : SameSkeleton chainGraph colliderGraph := by decide

/-- The empty conditioning set distinguishes the chain from the collider graph. -/
theorem chain_not_markovEquiv_collider : ¬ MarkovEquiv chainGraph colliderGraph := by
  intro equivalent
  have chain_connected : ¬ chainGraph.dSep {.x} {.y} ∅ := by decide
  exact chain_connected ((equivalent {.x} {.y} ∅).2 dSeparated_given_empty)

end

end OpenCausalScience.MarkovEquivalence
