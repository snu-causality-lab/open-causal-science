module
public import OpenCausalScience.Graph.MixedSeparation

/-! # A six-node comparison in the proof of Theorem 3

This graph is the first published CGA regression for Appendix B.10 of
Runge, arXiv:2102.10324v4, p. 19. Under the sets supplied by that regression,
the outcome connects to the comparison variables given the treatment alone;
adding the parent V separates them. The theorem's optimality conclusion
requires a comparison of terms, so the open path does not refute that conclusion.

Source: https://arxiv.org/html/2102.10324v4#App.B.SS10.
Fixture: https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/fixtures/papers/runge_2023_sufficiency_defects.json.
-/

namespace OpenCausalScience.Papers.Runge2021.ConditionIExample

@[expose] public section

def x : Fin 6 := 0
def y : Fin 6 := 1
def u : Fin 6 := 2
def u₂ : Fin 6 := 3
def v : Fin 6 := 4
def w : Fin 6 := 5

def directed (a b : Fin 6) : Bool :=
  (a == x && (b == y || b == u)) || (a == v && (b == u₂ || b == y))

def bidirected (a b : Fin 6) : Bool :=
  (a == w && (b == u || b == y)) || (b == w && (a == u || a == y))

def marked (a : Fin 6) (left : Bool) (b : Fin 6) (right : Bool) : Bool :=
  match left, right with
  | false, true => directed a b
  | true, false => directed b a
  | true, true => bidirected a b
  | false, false => false

def graph : MixedGraph 6 where
  edge := marked
  symmetric := by decide
  loop_free := by decide
  no_arrow_of_undirected := by decide

def outcomes : Fin 6 → Bool := (· == y)
def comparison : Fin 6 → Bool := fun a => a == u || a == u₂
def treatment : Fin 6 → Bool := (· == x)
def treatmentAndParent : Fin 6 → Bool := fun a => a == x || a == v

/-- `Y ← V → U₂` is active given the treatment, so the comparison term
cannot be set to zero using m-separation. -/
theorem outcome_connected_given_treatment : graph.PathConnected outcomes comparison treatment := by
  refine ⟨y, true, (v, false), [u₂], (u₂, true), rfl, rfl, ?_, rfl, by decide⟩
  have step : graph.Step treatment (v, false) (u₂, true) := ⟨false, rfl, rfl⟩
  exact .cons step (.nil _)

private theorem seed_cases : ∀ (source : Fin 6) (out : Bool) (a : Fin 6) (head : Bool),
    outcomes source = true → graph.edge source out a head = true →
    (a = x ∧ head = false) ∨ (a = v ∧ head = false) ∨ (a = w ∧ head = true) := by decide

private theorem no_directed_edge_out_of_w : ∀ a, graph.edge w false a true = false := by decide

private theorem w_is_not_activated : ¬ graph.AncestorOf treatmentAndParent w := by
  intro ancestor
  cases ancestor with
  | conditioned atW => exact (by decide : treatmentAndParent w ≠ true) atW
  | parent edge _ => simp [no_directed_edge_out_of_w] at edge

private theorem no_tail_out_of_w : ∀ a mark, graph.edge w false a mark = false := by decide

private theorem seeds_do_not_continue (a b : MixedGraph.Arrival 6)
    (seed : graph.Seed outcomes a) : ¬ graph.Step treatmentAndParent a b := by
  obtain ⟨source, out, starts, entry⟩ := seed
  obtain ⟨vertex, head⟩ := a
  rintro ⟨leave, next, turn⟩
  rcases seed_cases source out vertex head starts entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (by decide : treatmentAndParent x ≠ false) (by simpa [MixedGraph.openTurn] using turn)
  · exact (by decide : treatmentAndParent v ≠ false) (by simpa [MixedGraph.openTurn] using turn)
  · cases leave with
    | false => simp [no_tail_out_of_w] at next
    | true => exact w_is_not_activated (by simpa [MixedGraph.openTurn] using turn)

/-- The subset `{V}` does suffice to block the outcome-side comparison. -/
theorem parent_separates_outcome_from_comparison :
    ¬ graph.PathConnected outcomes comparison treatmentAndParent := by
  rintro ⟨source, mark, first, _, _, starts, entry, walk, ends, _⟩
  have seed : graph.Seed outcomes first := ⟨source, mark, starts, entry⟩
  cases walk with
  | nil =>
    rcases seed_cases source mark first.1 first.2 starts entry with ⟨node, _⟩ | ⟨node, _⟩ | ⟨node, _⟩
    · rw [node] at ends
      exact (by decide : comparison x ≠ true) ends
    · rw [node] at ends
      exact (by decide : comparison v ≠ true) ends
    · rw [node] at ends
      exact (by decide : comparison w ≠ true) ends
  | cons step _ => exact seeds_do_not_continue _ _ seed step

end

end OpenCausalScience.Papers.Runge2021.ConditionIExample
