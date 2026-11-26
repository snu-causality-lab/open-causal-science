module
public import OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.EdgeConsistency

/-! The three common-edge cases discussed after the definition in §5.3.
Source: https://arxiv.org/pdf/1411.2127#page=26
-/

namespace OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.Figure2A

open EdgeConsistency

@[expose] public section

abbrev w : Fin 4 := 0
abbrev a : Fin 4 := 1
abbrev m : Fin 4 := 2
abbrev y : Fin 4 := 3

def arrows : List (Fin 4 × Fin 4) := [(w, a), (w, m), (a, m), (a, y), (m, y)]

def graph : DAG 4 where
  edge u v := arrows.contains (u, v)
  rank := Fin.val
  edge_increases := by decide +kernel

def throughMediator : List (Fin 4) := [w, a, m, y]
def direct : List (Fin 4) := [w, a, y]
def listed (wv : Bool) : Assignments 4 := [(throughMediator, wv), (direct, wv)]

def onlyMediator : Assignments 4 := [(throughMediator, false)]
def disagreeing : Assignments 4 := [(throughMediator, false), (direct, true)]

private theorem end_at_y {paths : Assignments 4} {later : List (Fin 4)}
    (h : RelevantSuffix graph paths y y later) : later = [] := by
  cases h with
  | outcome => rfl
  | prepend edge _ _ =>
    have noOutgoing : ∀ v, graph.edge y v = false := by decide +kernel
    rw [noOutgoing] at edge
    contradiction

private theorem from_m {paths : Assignments 4} {later : List (Fin 4)}
    (h : RelevantSuffix graph paths y m later) : later = [y] := by
  cases h with
  | @prepend _ v tail edge _ route =>
    have only : ∀ u, graph.edge m u = true → u = y := by decide +kernel
    have happens := only v edge
    subst v
    exact congrArg (y :: ·) (end_at_y route)

private theorem from_a {paths : Assignments 4} {later : List (Fin 4)}
    (h : RelevantSuffix graph paths y a later) : later = [m, y] ∨ later = [y] := by
  cases h with
  | @prepend _ v tail edge _ route =>
    have only : ∀ u, graph.edge a u = true → u = m ∨ u = y := by decide +kernel
    obtain hm | hy := only v edge
    · subst v
      exact Or.inl (congrArg (m :: ·) (from_m route))
    · subst v
      exact Or.inr (congrArg (y :: ·) (end_at_y route))

/-- The paper's pair of paths with one common value is consistent. -/
theorem common_value_consistent (wv : Bool) : Consistent graph (listed wv) y := by
  constructor
  · intro entry member
    rcases List.mem_cons.mp member with same | rest
    · subst entry
      change 2 ≤ 4
      decide
    · have same := List.mem_singleton.mp rest
      subst entry
      change 2 ≤ 3
      decide
  · intro left hl right hr _
    have value (entry : List (Fin 4) × Bool) (inList : entry ∈ listed wv) : entry.2 = wv := by
      rcases List.mem_cons.mp inList with same | rest
      · subst entry
        rfl
      · have same := List.mem_singleton.mp rest
        subst entry
        rfl
    exact (value left hl).trans (value right hr).symm
  · intro src first later route _ assigned
    have which : ∀ u v, inducedEdges (listed wv) u v ≠ none → u = w ∧ v = a := by
      cases wv <;> decide +kernel
    obtain ⟨rfl, rfl⟩ := which src first assigned
    obtain rfl | rfl := from_a route <;> cases wv <;> decide +kernel

/-- A listed prefix on one branch also marks the common edge. The
uncovered branch violates consistency. -/
theorem only_mediator_inconsistent : ¬ Consistent graph onlyMediator y := by
  intro consistent
  have live : RelevantSuffix graph onlyMediator y a [y] := .prepend rfl rfl .outcome
  exact consistent.covers w a [y] live rfl (by decide +kernel) rfl

/-- Two paths using different values on the same first edge violate
edge consistency even when both branches are covered. -/
theorem unequal_values_inconsistent : ¬ Consistent graph disagreeing y := by
  intro consistent
  have impossible : false = true := consistent.agrees (throughMediator, false) (by decide +kernel)
    (direct, true) (by decide +kernel) rfl
  contradiction

end
end OpenCausalScience.Papers.ShpitserTchetgenTchetgen2016.Figure2A
