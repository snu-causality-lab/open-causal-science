module
public import OpenCausalScience.Papers.RichardsonRobins2013.NodeSplitting

/-! # The split edge, and the split of two successive treatments

In Figure 2, the random treatment X loses its only outgoing arrow.
The fixed x has the arrow to the potential outcome Y(x). A three-node
chain illustrates the distinction between an interior vertex and a
random endpoint in Proposition 9.

Source: https://csss.uw.edu/Papers/2013/wp128.pdf
-/

namespace OpenCausalScience.Papers.RichardsonRobins2013.Figure2

open NodeSplitting

@[expose] public section

def pairGraph : DAG 2 where
  edge u v := u == 0 && v == 1
  rank := Fin.val
  edge_increases := by decide +kernel

def pairTargets : Targets 2 := (· == 0)

theorem figure2_split_edge :
    InLabel pairGraph pairTargets 0 1 ∧
    ¬ DirectedWalk pairGraph (Vertex.random (targets := pairTargets) 0) (.random 1) := by
  constructor
  · exact ⟨rfl, .single rfl⟩
  · intro walk
    exact no_random_walk_from_target pairGraph (targets := pairTargets) rfl
      (random_walk_iff.mp walk)

def chainGraph : DAG 3 where
  edge u v := (u == 0 && v == 1) || (u == 1 && v == 2)
  rank := Fin.val
  edge_increases := by decide +kernel

def chainTargets : Targets 3 := fun v => v == 0 || v == 1

theorem successive_treatments :
    InLabel chainGraph chainTargets 0 1 ∧ InLabel chainGraph chainTargets 1 2 ∧
    ¬ InLabel chainGraph chainTargets 0 2 := by
  refine ⟨⟨rfl, .single rfl⟩, ⟨rfl, .single rfl⟩, ?_⟩
  intro label
  obtain ⟨_, first, arrow, path⟩ := in_label_iff.mp label
  have unique : ∀ v, chainGraph.edge 0 v = true → v = 1 := by decide +kernel
  have equal := unique first arrow
  subst first
  rcases path with stops | continues
  · contradiction
  · exact no_random_walk_from_target chainGraph (targets := chainTargets) rfl continues

end

end OpenCausalScience.Papers.RichardsonRobins2013.Figure2
