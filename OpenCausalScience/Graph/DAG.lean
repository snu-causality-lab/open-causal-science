module
public import Std

namespace OpenCausalScience

@[expose] public section

/-- A DAG on the vertices `0, …, n - 1`. `edge u v` is true exactly when
there is an arrow from `u` to `v`. The ranks witness acyclicity by strictly
increasing along every arrow. Vertices may share a rank. -/
structure DAG (n : Nat) where
  edge : Fin n → Fin n → Bool
  rank : Fin n → Nat
  edge_increases : ∀ u v, edge u v = true → rank u < rank v

namespace DAG

variable {n : Nat}

/-- Nonempty directed reachability, built by appending arrows. -/
inductive DirectedWalk (G : DAG n) : Fin n → Fin n → Prop
  | single {u v : Fin n} : G.edge u v = true → DirectedWalk G u v
  | extend {u v w : Fin n} : DirectedWalk G u v → G.edge v w = true → DirectedWalk G u w

/-- Ranks strictly increase along every nonempty directed walk. -/
theorem rank_lt_of_directedWalk (G : DAG n) {u v : Fin n} (walk : G.DirectedWalk u v) :
    G.rank u < G.rank v := by
  induction walk with
  | single h => exact G.edge_increases _ _ h
  | extend _ h ih => exact Nat.lt_trans ih (G.edge_increases _ _ h)

theorem no_directed_cycle (G : DAG n) (v : Fin n) : ¬ G.DirectedWalk v v :=
  fun walk => Nat.lt_irrefl (G.rank v) (G.rank_lt_of_directedWalk walk)

end DAG

end

end OpenCausalScience
