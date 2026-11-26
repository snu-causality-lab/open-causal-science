module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! # Ancestral relations under randomized interventions

The graphical statements behind Lemma 1 and Algorithm 1 of Kocaoglu,
Shanmugam and Bareinboim (2017). The observed graph is a vertex-induced
subgraph when the unmeasured vertices are exogenous roots.
-/

namespace OpenCausalScience.Papers.KocaogluEtAl2017Latent.AncestralRelations

open OpenCausalScience.Papers.KimEtAl2026
open BayesBall BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G : DAG n}

/-- Randomization cuts every incoming arrow at a target. -/
def cut (G : DAG n) (target : Fin n → Bool) : DAG n where
  edge u v := G.edge u v && !target v
  rank := G.rank
  edge_increases u v h := G.edge_increases u v (Bool.and_eq_true_iff.mp h).1

def unconditioned (G : DAG n) : Conditioning G where
  member := fun _ => false
  descendantHit := fun _ => false
  descendant_spec := by simp

private theorem prepend {u v w : Fin n} (edge : G.edge u v = true)
    (path : G.DirectedWalk v w) : G.DirectedWalk u w := by
  induction path with
  | single h => exact .extend (.single edge) h
  | extend _ h ih => exact .extend ih h

private theorem descend_only {s t : State (Fin n)} {route : List (Fin n)}
    (walk : ActiveWalk (unconditioned G) s route t) (arrivedDown : s.2 = .down) :
    s.1 = t.1 ∨ G.DirectedWalk s.1 t.1 := by
  induction walk with
  | nil => exact .inl rfl
  | @cons start next last _ step _ ih =>
    have nextDown : next.2 = .down := by
      cases outgoing : next.2 with
      | down => rfl
      | up =>
        have blocked := step.2
        simp [OpenTurn, arrivedDown, outgoing, Conditioning.activated, unconditioned] at blocked
    have edge : G.edge start.1 next.1 = true := by simpa [Move, nextDown] using step.1
    apply Or.inr
    rcases ih nextDown with same | path
    · exact .single (same ▸ edge)
    · exact prepend edge path

private theorem path_is_active {u v : Fin n} (path : G.DirectedWalk u v) (arrival : Direction) :
    ∃ route, ActiveWalk (unconditioned G) (u, arrival) route (v, .down) := by
  induction path with
  | @single v h =>
    have next : ActiveStep (unconditioned G) (u, arrival) (v, .down) :=
      ⟨h, by simp [OpenTurn, unconditioned]⟩
    exact ⟨[v], .cons next (.nil _)⟩
  | @extend w v _ h ih =>
    obtain ⟨route, active⟩ := ih
    have next : ActiveStep (unconditioned G) (w, .down) (v, .down) :=
      ⟨h, by simp [OpenTurn, unconditioned]⟩
    have append {s t z : State (Fin n)} {route : List (Fin n)}
        (path : ActiveWalk (unconditioned G) s route t)
        (step : ActiveStep (unconditioned G) t z) :
        ActiveWalk (unconditioned G) s (route ++ [z.1]) z := by
      induction path with
      | nil => exact .cons step (.nil _)
      | cons first _ ih => exact .cons first (ih step)
    exact ⟨route ++ [v], append active next⟩

/-- A root has an unconditioned active path to a distinct vertex exactly
when it is an ancestor. The root cannot start with an incoming arrow. -/
theorem root_dconnected_iff_directed_walk {u v : Fin n} (different : u ≠ v)
    (root : ∀ p, G.edge p u = false) :
    DConnected (unconditioned G) u v ↔ G.DirectedWalk u v := by
  constructor
  · rintro ⟨_, _, route, arrival, walk, _⟩
    cases walk with
    | nil => exact (different rfl).elim
    | @cons _ next _ _ step suffix =>
      have down : next.2 = .down := by
        cases direction : next.2 with
        | down => rfl
        | up =>
          have incoming := step.1
          simp [Move, direction, root] at incoming
      have edge : G.edge u next.1 = true := by simpa [Move, down] using step.1
      rcases descend_only suffix down with same | directed
      · have same' : next.1 = v := same
        rw [same'] at edge
        exact .single edge
      · exact prepend edge directed
  · intro direction
    obtain ⟨_, active⟩ := path_is_active direction .up
    obtain ⟨route, final, simple, same, nodup, _⟩ := active.to_simple
    obtain ⟨endpoint, arrival⟩ := final
    change endpoint = v at same
    subst endpoint
    exact ⟨rfl, rfl, route, arrival, simple, nodup⟩

def observedGraph (G : DAG n) (observed : Fin n → Bool) : DAG n where
  edge u v := G.edge u v && (observed u && observed v)
  rank := G.rank
  edge_increases u v h := G.edge_increases u v (Bool.and_eq_true_iff.mp h).1

private theorem restrict_directed {observed : Fin n → Bool}
    (allLatentsRoot : ∀ u v, G.edge u v = true → observed v = true)
    {x y : Fin n} (path : G.DirectedWalk x y) (source : observed x = true) :
    observed y = true ∧ (observedGraph G observed).DirectedWalk x y := by
  induction path with
  | single edge =>
    have target := allLatentsRoot _ _ edge
    exact ⟨target, .single (by simp [observedGraph, edge, source, target])⟩
  | extend _ edge ih =>
    obtain ⟨middle, path⟩ := ih
    have target := allLatentsRoot _ _ edge
    exact ⟨target, .extend path (by simp [observedGraph, edge, middle, target])⟩

private theorem lift_observed {observed : Fin n → Bool} {x y : Fin n}
    (path : (observedGraph G observed).DirectedWalk x y) : G.DirectedWalk x y := by
  induction path with
  | single edge => exact .single (Bool.and_eq_true_iff.mp edge).1
  | extend _ edge ih => exact .extend ih (Bool.and_eq_true_iff.mp edge).1

/-- Lemma 1 at the graph level. The observable ancestry test uses the
induced post-intervention graph when latent vertices have no parents. -/
theorem randomized_dconnected_iff_observable_ancestry {observed target : Fin n → Bool}
    (latentRoot : ∀ u v, G.edge u v = true → observed v = true)
    {x y : Fin n} (sourceObserved : observed x = true) (treated : target x = true)
    (untreated : target y = false) :
    DConnected (unconditioned (cut G target)) x y ↔
      (observedGraph (cut G target) observed).DirectedWalk x y := by
  have different : x ≠ y := by
    rintro rfl
    simp [treated] at untreated
  rw [root_dconnected_iff_directed_walk different (by intro p; simp [cut, treated])]
  constructor
  · intro path
    exact (restrict_directed (fun u v edge => latentRoot u v (Bool.and_eq_true_iff.mp edge).1)
      path sourceObserved).2
  · exact lift_observed

/-- Algorithm 1 records an arrow for each positive ancestry test. -/
def testedEdge (G : DAG n) (observed : Fin n → Bool) (design : List (Fin n → Bool))
    (x y : Fin n) : Prop :=
  ∃ targets ∈ design, observed x = true ∧ observed y = true ∧
    targets x = true ∧ targets y = false ∧
    (observedGraph (cut G targets) observed).DirectedWalk x y

inductive Walk (rel : Fin n → Fin n → Prop) : Fin n → Fin n → Prop
  | single {u v} : rel u v → Walk rel u v
  | extend {u v w} : Walk rel u v → rel v w → Walk rel u w

private theorem tested_is_ancestor {observed : Fin n → Bool} {design : List (Fin n → Bool)}
    {u v : Fin n} (found : testedEdge G observed design u v) :
    (observedGraph G observed).DirectedWalk u v := by
  obtain ⟨targets, member, obsU, obsV, treated, untreated, walk⟩ := found
  clear member obsU obsV treated untreated
  induction walk with
  | single edge =>
    have old := Bool.and_eq_true_iff.mp edge
    exact .single (Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp old.1).1, old.2⟩)
  | extend _ edge ih =>
    have old := Bool.and_eq_true_iff.mp edge
    exact .extend ih (Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp old.1).1, old.2⟩)

private theorem concatenate {u v w : Fin n} (first : G.DirectedWalk u v)
    (second : G.DirectedWalk v w) : G.DirectedWalk u w := by
  induction second with
  | single edge => exact .extend first edge
  | extend _ edge ih => exact .extend ih edge

/-- Graphical correctness of the final transitive closure. A directed
observed edge is tested in some separating experiment and every positive
test already lies in the original observable transitive closure. -/
theorem strongly_separating_design_recovers_ancestry
    {observed : Fin n → Bool} {design : List (Fin n → Bool)}
    (separates : ∀ u v, observed u = true → observed v = true → u ≠ v →
      ∃ targets ∈ design, targets u = true ∧ targets v = false)
    {x y : Fin n} :
    Walk (testedEdge G observed design) x y ↔ (observedGraph G observed).DirectedWalk x y := by
  have finds_edge {u v : Fin n} (edge : (observedGraph G observed).edge u v = true) :
      testedEdge G observed design u v := by
    have data := Bool.and_eq_true_iff.mp edge
    have obs := Bool.and_eq_true_iff.mp data.2
    have unequal : u ≠ v := by
      rintro rfl
      exact Nat.lt_irrefl _ (G.edge_increases _ _ data.1)
    obtain ⟨targets, mem, treated, control⟩ := separates u v obs.1 obs.2 unequal
    exact ⟨targets, mem, obs.1, obs.2, treated, control,
      .single (by simp [observedGraph, cut, data.1, control, obs.1, obs.2])⟩
  constructor
  · intro path
    induction path with
    | single found => exact tested_is_ancestor found
    | extend _ found ih => exact concatenate ih (tested_is_ancestor found)
  · intro path
    induction path with
    | single edge => exact .single (finds_edge edge)
    | extend _ edge ih => exact .extend ih (finds_edge edge)

end
end OpenCausalScience.Papers.KocaogluEtAl2017Latent.AncestralRelations
