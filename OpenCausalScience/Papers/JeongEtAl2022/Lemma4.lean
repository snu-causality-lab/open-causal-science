module
public import OpenCausalScience.Graph.DSeparation

/-! # Directed path blocking for the front-door criterion

Jeong, Tian and Bareinboim (2022), Lemma 4 uses d-separation in the
causal-path graph to characterize blocking every directed treatment-to-outcome
path. These conditions differ on the graph below. The directed reachability
check used by Wienöbst et al. (2024), Algorithm 2 has the exact local property.
-/

namespace OpenCausalScience.FrontDoorPathBlocking

@[expose] public section

variable {n : Nat}

/-- Keep the same vertex labels and remove every arrow incident to a blocked
vertex. Queries here use endpoints outside the blocked set. -/
def withoutVertices (graph : DAG n) (blocked : Fin n → Bool) : DAG n where
  edge u v := graph.edge u v && (!blocked u && !blocked v)
  rank := graph.rank
  edge_increases u v h := graph.edge_increases u v (by simpa using (Bool.and_eq_true_iff.mp h).1)

/-- A nonempty directed walk whose vertices all avoid the blocked set. -/
inductive DirectedWalkAvoiding (graph : DAG n) (blocked : Fin n → Bool) : Fin n → Fin n → Prop
  | single {u v : Fin n} : graph.edge u v = true → blocked u = false → blocked v = false →
      DirectedWalkAvoiding graph blocked u v
  | extend {u v w : Fin n} : DirectedWalkAvoiding graph blocked u v → graph.edge v w = true →
      blocked w = false → DirectedWalkAvoiding graph blocked u w

theorem deleted_graph_iff_avoiding_walk (graph : DAG n) (blocked : Fin n → Bool) (x y : Fin n) :
    (withoutVertices graph blocked).DirectedWalk x y ↔ DirectedWalkAvoiding graph blocked x y := by
  have unpack (u v : Fin n) (h : (withoutVertices graph blocked).edge u v = true) :
      graph.edge u v = true ∧ blocked u = false ∧ blocked v = false := by
    simpa [withoutVertices, Bool.and_eq_true_iff] using h
  have pack (u v : Fin n) (h : graph.edge u v = true) (hu : blocked u = false)
      (hv : blocked v = false) : (withoutVertices graph blocked).edge u v = true := by
    simp [withoutVertices, h, hu, hv]
  constructor
  · intro walk
    induction walk with
    | single h =>
      obtain ⟨edge, hu, hv⟩ := unpack _ _ h
      exact .single edge hu hv
    | extend _ h shorter =>
      obtain ⟨edge, _, hw⟩ := unpack _ _ h
      exact .extend shorter edge hw
  · intro walk
    have withEndpoint {u v : Fin n} (walk : DirectedWalkAvoiding graph blocked u v) :
        (withoutVertices graph blocked).DirectedWalk u v ∧ blocked v = false := by
      induction walk with
      | single h hu hv => exact ⟨.single (pack _ _ h hu hv), hv⟩
      | extend _ h hw shorter => exact ⟨.extend shorter.1 (pack _ _ h shorter.2 hw), hw⟩
    exact (withEndpoint walk).1

private theorem no_walk_from_sink (graph : DAG n) {source target : Fin n}
    (h : ∀ v, graph.edge source v = false) : ¬ graph.DirectedWalk source target := by
  intro walk
  induction walk with
  | single edge => simp [h] at edge
  | extend _ _ shorter => exact shorter

def x : Fin 5 := 0
def b : Fin 5 := 1
def c : Fin 5 := 2
def a : Fin 5 := 3
def y : Fin 5 := 4

def counterexample : DAG 5 where
  edge u v := (u == x && (v == a || v == b)) || (u == b && v == c) ||
    (u == c && (v == a || v == y)) || (u == a && v == y)
  rank u := u.val
  edge_increases := by decide

def blocks (v : Fin 5) : Bool := v == a || v == b

theorem no_avoiding_directed_walk : ¬ DirectedWalkAvoiding counterexample blocks x y := by
  rw [← deleted_graph_iff_avoiding_walk]
  apply no_walk_from_sink
  decide

/-- Conditioning on A opens the collider on X → A ← C → Y. -/
theorem still_d_connected : counterexample.dSeparated x y [a, b] = some false := by decide

end

end OpenCausalScience.FrontDoorPathBlocking
