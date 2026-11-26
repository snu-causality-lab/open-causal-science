module
public import OpenCausalScience.Graph.DAG

/-! # The O-set in a finite DAG

Henckel, Perković and Maathuis (2022), arXiv:1907.02435v2, Definition 3.12,
and Witte et al. (2020), Definition 1. A causal node is a non-treatment node on a proper directed
path from the treatment set to the outcome set. The forbidden set includes
the treatments and all descendants of causal nodes. The O-set is the set of
parents of causal nodes outside the forbidden set.

Sources: https://doi.org/10.1111/rssb.12451 and
https://jmlr.org/papers/v21/20-175.html.
-/

namespace OpenCausalScience.Papers.HenckelEtAl2022.DAGOSet

@[expose] public section

variable {n : Nat}

/-- A nonempty directed path whose interior vertices satisfy `allowed`.
The DAG's increasing ranks preclude repetitions. -/
inductive DirectedPath (graph : DAG n) (allowed : Fin n → Prop) : Fin n → Fin n → Prop
  | single {u v} : graph.edge u v = true → DirectedPath graph allowed u v
  | prepend {u v w} : graph.edge u v = true → allowed v →
      DirectedPath graph allowed v w → DirectedPath graph allowed u w

namespace DirectedPath

theorem relax {graph : DAG n} {p q : Fin n → Prop} {u v : Fin n}
    (path : DirectedPath graph p u v) (allows : ∀ w, p w → q w) :
    DirectedPath graph q u v := by
  induction path with
  | single edge => exact .single edge
  | prepend edge allowed _ ih => exact .prepend edge (allows _ allowed) ih

theorem append_edge {graph : DAG n} {allowed : Fin n → Prop} {u v w : Fin n}
    (path : DirectedPath graph allowed u v) (middle : allowed v)
    (edge : graph.edge v w = true) : DirectedPath graph allowed u w := by
  induction path with
  | single first => exact .prepend first middle (.single edge)
  | prepend first inside _ ih => exact .prepend first inside (ih middle edge)

theorem append_to_walk {graph : DAG n} {allowed : Fin n → Prop} {u v w : Fin n}
    (path : DirectedPath graph allowed v w) (initial : graph.DirectedWalk u v) :
    graph.DirectedWalk u w := by
  induction path with
  | single edge => exact .extend initial edge
  | prepend edge _ _ ih => exact ih (.extend initial edge)

theorem to_walk {graph : DAG n} {allowed : Fin n → Prop} {u v : Fin n}
    (path : DirectedPath graph allowed u v) : graph.DirectedWalk u v := by
  cases path with
  | single edge => exact .single edge
  | prepend edge _ tail => exact tail.append_to_walk (.single edge)

end DirectedPath

def TreatmentAncestor (graph : DAG n) (treatment : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ a, treatment a = true ∧ graph.DirectedWalk a v

/-- Reach an outcome using a path with no treatment among the interior
vertices, or already be at an outcome. -/
def OutcomeSuffix (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ y, outcome y = true ∧ (v = y ∨ DirectedPath graph (fun w => treatment w = false) v y)

/-- Split the proper directed path at the causal node. Its prefix and suffix
therefore have no treatment among their interior vertices. -/
def CausalNode (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  treatment v = false ∧
    (∃ a, treatment a = true ∧ DirectedPath graph (fun w => treatment w = false) a v) ∧
    OutcomeSuffix graph treatment outcome v

private theorem exists_proper_prefix {graph : DAG n} {treatment : Fin n → Bool}
    {a v : Fin n} (walk : graph.DirectedWalk a v) (starts : treatment a = true) :
    ∃ b, treatment b = true ∧ DirectedPath graph (fun w => treatment w = false) b v := by
  induction walk with
  | single edge => exact ⟨a, starts, .single edge⟩
  | @extend middle _ _ edge ih =>
    cases middleTreatment : treatment middle with
    | true => exact ⟨middle, middleTreatment, .single edge⟩
    | false =>
      obtain ⟨source, sourceTreatment, path⟩ := ih
      exact ⟨source, sourceTreatment, path.append_edge middleTreatment edge⟩

/-- Directed reachability from a treatment may first encounter other
treatments. Starting again at the last one gives a proper prefix. -/
theorem causal_node_iff {graph : DAG n} {treatment outcome : Fin n → Bool} {v : Fin n} :
    CausalNode graph treatment outcome v ↔ treatment v = false ∧
      TreatmentAncestor graph treatment v ∧ OutcomeSuffix graph treatment outcome v := by
  constructor
  · rintro ⟨outside, ⟨source, sourceTreatment, path⟩, suffix⟩
    exact ⟨outside, ⟨source, sourceTreatment, path.to_walk⟩, suffix⟩
  · rintro ⟨outside, ⟨source, sourceTreatment, walk⟩, suffix⟩
    exact ⟨outside, exists_proper_prefix walk sourceTreatment, suffix⟩

def Forbidden (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  treatment v = true ∨ ∃ c, CausalNode graph treatment outcome c ∧
    (c = v ∨ graph.DirectedWalk c v)

theorem causal_node_forbidden {graph : DAG n} {treatment outcome : Fin n → Bool} {v : Fin n}
    (causal : CausalNode graph treatment outcome v) : Forbidden graph treatment outcome v :=
  .inr ⟨v, causal, .inl rfl⟩

theorem treatment_ancestor_of_forbidden {graph : DAG n} {treatment outcome : Fin n → Bool}
    {v : Fin n} (forbidden : Forbidden graph treatment outcome v)
    (outside : treatment v = false) : TreatmentAncestor graph treatment v := by
  rcases forbidden with treated | ⟨c, causal, rfl | walk⟩
  · simp [outside] at treated
  · exact (causal_node_iff.mp causal).2.1
  · obtain ⟨source, isTreatment, initial⟩ := (causal_node_iff.mp causal).2.1
    clear outside
    refine ⟨source, isTreatment, ?_⟩
    induction walk with
    | single edge => exact .extend initial edge
    | extend _ edge ih => exact .extend ih edge

def OSet (graph : DAG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  (∃ c, CausalNode graph treatment outcome c ∧ graph.edge v c = true) ∧
    ¬ Forbidden graph treatment outcome v

end

end OpenCausalScience.Papers.HenckelEtAl2022.DAGOSet
