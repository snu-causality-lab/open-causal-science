module
public import OpenCausalScience.Graph.DAG

/-! # The graph of a single-world intervention template

Richardson and Robins (2013), §3.3.1 and Propositions 4–9. The random
half of an intervened node keeps its incoming arrows. Each outgoing
arrow instead leaves the fixed half. A fixed label appears at a random
node exactly when a directed walk from its fixed vertex reaches that
node. This module formalizes the graph before assigning fixed values.

Source: https://csss.uw.edu/Papers/2013/wp128.pdf
-/

namespace OpenCausalScience.Papers.RichardsonRobins2013.NodeSplitting

@[expose] public section

variable {n : Nat}

abbrev Targets (n : Nat) := Fin n → Bool

inductive Vertex (targets : Targets n) where
  | random (v : Fin n)
  | fixed (v : Fin n) (selected : targets v = true)

def Vertex.original {targets : Targets n} : Vertex targets → Fin n
  | .random v | .fixed v _ => v

def sourceVertex (targets : Targets n) (v : Fin n) : Vertex targets :=
  if selected : targets v = true then .fixed v selected else .random v

def edge (graph : DAG n) {targets : Targets n} : Vertex targets → Vertex targets → Bool
  | .random u, .random v => !targets u && graph.edge u v
  | .fixed u _, .random v => graph.edge u v
  | _, .fixed _ _ => false

/-- The random vertices retain exactly the arrows whose original source is
outside the intervention targets. -/
def randomPart (graph : DAG n) (targets : Targets n) : DAG n where
  edge u v := !targets u && graph.edge u v
  rank := graph.rank
  edge_increases _ _ h := graph.edge_increases _ _ (Bool.and_eq_true_iff.mp h).2

theorem random_edge_iff (graph : DAG n) (targets : Targets n) (u v : Fin n) :
    edge graph (Vertex.random (targets := targets) u) (.random v) = true ↔
      targets u = false ∧ graph.edge u v = true := by
  simp [edge, Bool.and_eq_true]

theorem no_incoming_fixed (graph : DAG n) {targets : Targets n} (u : Vertex targets)
    {v : Fin n} (selected : targets v = true) : edge graph u (.fixed v selected) = false := by
  cases u <;> rfl

theorem original_edge (graph : DAG n) {targets : Targets n} {u v : Vertex targets}
    (arrow : edge graph u v = true) : graph.edge u.original v.original = true := by
  cases u <;> cases v <;> simp_all [edge, Vertex.original, Bool.and_eq_true]

theorem translated_edge_iff (graph : DAG n) (targets : Targets n) (u v : Fin n) :
    edge graph (sourceVertex targets u) (.random v) = true ↔ graph.edge u v = true := by
  by_cases selected : targets u = true <;> simp [sourceVertex, edge, selected]

inductive DirectedWalk (graph : DAG n) {targets : Targets n} :
    Vertex targets → Vertex targets → Prop
  | single {u v} : edge graph u v = true → DirectedWalk graph u v
  | extend {u v w} : DirectedWalk graph u v → edge graph v w = true → DirectedWalk graph u w

theorem original_walk {graph : DAG n} {targets : Targets n} {u v : Vertex targets}
    (walk : DirectedWalk graph u v) : graph.DirectedWalk u.original v.original := by
  induction walk with
  | single h => exact .single (original_edge graph h)
  | extend _ h ih => exact .extend ih (original_edge graph h)

theorem no_directed_cycle (graph : DAG n) {targets : Targets n} (u : Vertex targets) :
    ¬ DirectedWalk graph u u := fun walk =>
  graph.no_directed_cycle u.original (original_walk walk)

private theorem edge_ends_at_random {graph : DAG n} {targets : Targets n} {u v : Vertex targets}
    (arrow : edge graph u v = true) : ∃ node, v = .random node := by
  cases v with
  | random node => exact ⟨node, rfl⟩
  | fixed node selected =>
    rw [no_incoming_fixed] at arrow
    contradiction

private theorem walk_ends_at_random {graph : DAG n} {targets : Targets n} {u v : Vertex targets}
    (walk : DirectedWalk graph u v) : ∃ node, v = .random node := by
  cases walk with
  | single h => exact edge_ends_at_random h
  | extend _ h => exact edge_ends_at_random h

private theorem walk_from_random {graph : DAG n} {targets : Targets n} {u v : Vertex targets}
    (walk : DirectedWalk graph u v) (random : ∃ node, u = .random node) :
    (randomPart graph targets).DirectedWalk u.original v.original := by
  induction walk with
  | @single v h =>
    obtain ⟨source, rfl⟩ := random
    obtain ⟨child, rfl⟩ := edge_ends_at_random h
    exact .single h
  | @extend v w path h ih =>
    obtain ⟨middle, rfl⟩ := walk_ends_at_random path
    obtain ⟨child, rfl⟩ := edge_ends_at_random h
    exact .extend ih h

private theorem lift_random_walk {graph : DAG n} {targets : Targets n} {u v : Fin n}
    (walk : (randomPart graph targets).DirectedWalk u v) :
    DirectedWalk graph (Vertex.random (targets := targets) u) (.random v) := by
  induction walk with
  | single h => exact .single h
  | extend _ h ih => exact .extend ih h

theorem random_walk_iff {graph : DAG n} {targets : Targets n} {u v : Fin n} :
    DirectedWalk graph (Vertex.random (targets := targets) u) (.random v) ↔
      (randomPart graph targets).DirectedWalk u v :=
  ⟨fun walk => walk_from_random walk ⟨u, rfl⟩, lift_random_walk⟩

theorem no_random_walk_from_target (graph : DAG n) {targets : Targets n} {u v : Fin n}
    (selected : targets u = true) : ¬ (randomPart graph targets).DirectedWalk u v := by
  intro walk
  induction walk with
  | single arrow => simp [randomPart, selected] at arrow
  | extend _ _ ih => exact ih

private theorem append_walk {graph : DAG n} {targets : Targets n} {u v w : Vertex targets}
    (first : DirectedWalk graph u v) (second : DirectedWalk graph v w) :
    DirectedWalk graph u w := by
  induction second with
  | single h => exact .extend first h
  | extend _ h ih => exact .extend ih h

/-- The treatment indices labeling a random node in §3.3.1. -/
def InLabel (graph : DAG n) (targets : Targets n) (treatment node : Fin n) : Prop :=
  ∃ selected : targets treatment = true,
    DirectedWalk graph (.fixed treatment selected) (.random node)

theorem label_monotone_along_walk {graph : DAG n} {targets : Targets n} {treatment u v : Fin n}
    (walk : DirectedWalk graph (Vertex.random (targets := targets) u) (.random v))
    (label : InLabel graph targets treatment u) : InLabel graph targets treatment v := by
  obtain ⟨selected, before⟩ := label
  exact ⟨selected, append_walk before walk⟩

private theorem first_fixed_arrow {graph : DAG n} {targets : Targets n} {treatment : Fin n}
    {selected : targets treatment = true} {u v : Vertex targets} (walk : DirectedWalk graph u v)
    (starts : u = .fixed treatment selected) :
    ∃ first, graph.edge treatment first = true ∧
      (first = v.original ∨ (randomPart graph targets).DirectedWalk first v.original) := by
  induction walk with
  | @single v h =>
    subst u
    exact ⟨v.original, original_edge graph h, .inl rfl⟩
  | @extend v w path h ih =>
    obtain ⟨middle, rfl⟩ := walk_ends_at_random path
    obtain ⟨child, rfl⟩ := edge_ends_at_random h
    obtain ⟨first, original, equal | suffix⟩ := ih
    · have arrow : (randomPart graph targets).edge middle child = true := h
      exact ⟨first, original, .inr (.single (equal.symm ▸ arrow))⟩
    · exact ⟨first, original, .inr (.extend suffix h)⟩

/-- A fixed label requires a directed path with no intervened interior
vertex. A random endpoint can itself represent another treatment. -/
theorem in_label_iff {graph : DAG n} {targets : Targets n} {treatment node : Fin n} :
    InLabel graph targets treatment node ↔
      targets treatment = true ∧ ∃ first, graph.edge treatment first = true ∧
        (first = node ∨ (randomPart graph targets).DirectedWalk first node) := by
  constructor
  · rintro ⟨selected, walk⟩
    exact ⟨selected, first_fixed_arrow walk rfl⟩
  · rintro ⟨selected, first, original, equal | suffix⟩
    · subst first
      exact ⟨selected, .single original⟩
    · have start : edge graph (.fixed treatment selected) (.random first) = true := original
      exact ⟨selected, append_walk (.single start) (lift_random_walk suffix)⟩

end

end OpenCausalScience.Papers.RichardsonRobins2013.NodeSplitting
