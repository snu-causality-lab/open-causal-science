module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Graph.MixedGraph

/-! # Finite chain graphs

Lines preserve the rank and arrows strictly increase it. This realizes
the acyclic ordering of the undirected components used by Lauritzen and
Wermuth (1989), Frydenberg (1990), and Drton (2009).
-/

namespace OpenCausalScience

@[expose] public section

structure ChainGraph (n : Nat) where
  line : Fin n → Fin n → Bool
  arrow : Fin n → Fin n → Bool
  rank : Fin n → Nat
  line_symm : ∀ u v, line u v = line v u
  line_irrefl : ∀ u, line u u = false
  line_level : ∀ u v, line u v = true → rank u = rank v
  arrow_increases : ∀ u v, arrow u v = true → rank u < rank v

namespace ChainGraph

open MixedGraph (Reach)

variable {n : Nat}

abbrev Vertices (n : Nat) := Fin n → Bool

def singleton (u : Fin n) : Vertices n := (· == u)

private theorem reach_trans {α : Type} {R : α → α → Prop} {u v w : α}
    (first : Reach R u v) (second : Reach R v w) : Reach R u w := by
  induction second with
  | refl => exact first
  | extend prior edge ih => exact .extend ih edge

/-- Boolean reflexive closure by adding one allowable intermediate vertex
at a time. This definition computes the closure on finite examples. -/
def route (edge : Fin n → Fin n → Bool) : List (Fin n) → Fin n → Fin n → Bool
  | [], u, v => (u == v) || edge u v
  | i :: rest, u, v => route edge rest u v ||
      (route edge rest u i && route edge rest i v)

private theorem route_sound (edge : Fin n → Fin n → Bool) (inside : List (Fin n))
    {u v : Fin n} (path : route edge inside u v = true) :
    Reach (fun a b => edge a b = true) u v := by
  induction inside generalizing u v with
  | nil =>
    rcases Bool.or_eq_true_iff.mp path with equal | edge
    · obtain rfl := beq_iff_eq.mp equal
      exact .refl u
    · exact .extend (.refl u) edge
  | cons middle rest ih =>
    rcases Bool.or_eq_true_iff.mp path with direct | via
    · exact ih direct
    · obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp via
      exact reach_trans (ih first) (ih second)

private theorem route_of_direct (edge : Fin n → Fin n → Bool) (inside : List (Fin n))
    {u v : Fin n} (step : (u == v) || edge u v = true) :
    route edge inside u v = true := by
  induction inside with
  | nil => exact step
  | cons middle rest ih => exact Bool.or_eq_true_iff.mpr (.inl ih)

private theorem route_trans_at (edge : Fin n → Fin n → Bool) (inside : List (Fin n))
    {u v w : Fin n} (admitted : v ∈ inside) (first : route edge inside u v = true)
    (second : route edge inside v w = true) : route edge inside u w = true := by
  induction inside generalizing u v w with
  | nil => contradiction
  | cons i rest ih =>
    have first := Bool.or_eq_true_iff.mp first
    have second := Bool.or_eq_true_iff.mp second
    apply Bool.or_eq_true_iff.mpr
    rcases List.mem_cons.mp admitted with rfl | keep
    · apply Or.inr
      exact Bool.and_eq_true_iff.mpr
        ⟨first.elim id (fun via => (Bool.and_eq_true_iff.mp via).1),
          second.elim id (fun via => (Bool.and_eq_true_iff.mp via).2)⟩
    · rcases first with direct1 | via1 <;> rcases second with direct2 | via2
      · exact .inl (ih keep direct1 direct2)
      · obtain ⟨toI, fromI⟩ := Bool.and_eq_true_iff.mp via2
        exact .inr (Bool.and_eq_true_iff.mpr ⟨ih keep direct1 toI, fromI⟩)
      · obtain ⟨toI, fromI⟩ := Bool.and_eq_true_iff.mp via1
        exact .inr (Bool.and_eq_true_iff.mpr ⟨toI, ih keep fromI direct2⟩)
      · exact .inr (Bool.and_eq_true_iff.mpr
          ⟨(Bool.and_eq_true_iff.mp via1).1, (Bool.and_eq_true_iff.mp via2).2⟩)

theorem route_iff (edge : Fin n → Fin n → Bool) (u v : Fin n) :
    route edge (List.finRange n) u v = true ↔ Reach (fun a b => edge a b = true) u v := by
  refine ⟨route_sound edge _, ?_⟩
  intro path
  induction path with
  | refl => apply route_of_direct; simp
  | @extend middle finish prior hop ih =>
    exact route_trans_at edge _ (List.mem_finRange middle) ih
      (route_of_direct edge _ (by simp [hop]))

def reached (edge : Fin n → Fin n → Bool) (seed : Vertices n) : List (Fin n) :=
  (List.finRange n).filter fun v =>
    (List.finRange n).any fun u => seed u && route edge (List.finRange n) u v

theorem mem_reached_iff (edge : Fin n → Fin n → Bool) (seed : Vertices n) (v : Fin n) :
    v ∈ reached edge seed ↔ ∃ u, seed u = true ∧ Reach (fun a b => edge a b = true) u v := by
  simp [reached, route_iff, List.any_eq_true]

/-- The line component containing its named vertex. -/
def component (G : ChainGraph n) (u : Fin n) : Vertices n :=
  fun v => route G.line (List.finRange n) u v

theorem component_eq_true_iff (G : ChainGraph n) (u v : Fin n) :
    G.component u v = true ↔ Reach (fun a b => G.line a b = true) u v :=
  route_iff G.line u v

theorem component_refl (G : ChainGraph n) (u : Fin n) : G.component u u = true :=
  (G.component_eq_true_iff u u).mpr (.refl u)

theorem component_symm (G : ChainGraph n) {u v : Fin n} (connected : G.component u v = true) :
    G.component v u = true := by
  apply (G.component_eq_true_iff v u).mpr
  have path := (G.component_eq_true_iff u v).mp connected
  clear connected
  induction path with
  | refl => exact .refl u
  | @extend b c prior edge ih =>
    have back : G.line c b = true := (G.line_symm c b).trans edge
    exact reach_trans (.extend (.refl c) back) ih

theorem component_trans (G : ChainGraph n) {u v w : Fin n}
    (first : G.component u v = true) (second : G.component v w = true) :
    G.component u w = true :=
  (G.component_eq_true_iff u w).mpr
    (reach_trans ((G.component_eq_true_iff u v).mp first) ((G.component_eq_true_iff v w).mp second))

theorem component_rank (G : ChainGraph n) {u v : Fin n} (connected : G.component u v = true) :
    G.rank u = G.rank v := by
  have path := (G.component_eq_true_iff u v).mp connected
  clear connected
  induction path with
  | refl => rfl
  | extend prior edge ih => exact ih.trans (G.line_level _ _ edge)

theorem component_eq_of_connected (G : ChainGraph n) {u v : Fin n}
    (connected : G.component u v = true) : G.component u = G.component v := by
  funext w
  apply Bool.eq_iff_iff.mpr
  exact ⟨G.component_trans (G.component_symm connected), G.component_trans connected⟩

/-- Arrows induce a rank-increasing relation on chain components. -/
def componentArrow (G : ChainGraph n) (u v : Fin n) : Prop :=
  ∃ a b, G.component u a = true ∧ G.arrow a b = true ∧ G.component v b = true

theorem component_arrow_increases (G : ChainGraph n) {u v : Fin n}
    (step : G.componentArrow u v) : G.rank u < G.rank v := by
  obtain ⟨a, b, hu, edge, hv⟩ := step
  rw [G.component_rank hu, G.component_rank hv]
  exact G.arrow_increases _ _ edge

def advance (G : ChainGraph n) (u v : Fin n) : Bool := G.line u v || G.arrow u v

theorem rank_le_of_advance (G : ChainGraph n) {u v : Fin n}
    (path : Reach (fun a b => G.advance a b = true) u v) : G.rank u ≤ G.rank v := by
  induction path with
  | refl => exact Nat.le_refl _
  | extend prior edge ih =>
    rcases Bool.or_eq_true_iff.mp edge with line | arrow
    · exact (G.line_level _ _ line) ▸ ih
    · exact Nat.le_trans ih (Nat.le_of_lt (G.arrow_increases _ _ arrow))

theorem no_semidirected_return (G : ChainGraph n) {u v : Fin n} (edge : G.arrow u v = true) :
    ¬ Reach (fun a b => G.advance a b = true) v u := by
  intro path
  exact Nat.not_lt_of_ge (G.rank_le_of_advance path) (G.arrow_increases _ _ edge)

def ofDAG (G : DAG n) : ChainGraph n where
  line := fun _ _ => false
  arrow := G.edge
  rank := G.rank
  line_symm := fun _ _ => rfl
  line_irrefl := fun _ => rfl
  line_level := by simp
  arrow_increases := G.edge_increases

theorem ofDAG_component_singleton (G : DAG n) (u : Fin n) :
    (ofDAG G).component u = singleton u := by
  funext v
  apply Bool.eq_iff_iff.mpr
  rw [component_eq_true_iff]
  constructor
  · intro path
    cases path with
    | refl => simp [singleton]
    | extend prior edge => simp [ofDAG] at edge
  · intro equal
    have : v = u := by simpa [singleton] using equal
    subst v
    exact .refl u

def parents (G : ChainGraph n) (vertices : Vertices n) (v : Fin n) : Bool :=
  (List.finRange n).any fun u => vertices u && G.arrow v u

def neighbors (G : ChainGraph n) (vertices : Vertices n) (v : Fin n) : Bool :=
  !vertices v && (List.finRange n).any fun u => vertices u && G.line v u

/-- Drton (2009), §2.2. A representative reaches all of its component
and all vertices in descendant components via semidirected paths. -/
def nonDescendants (G : ChainGraph n) (u : Fin n) : Vertices n :=
  fun v => !decide (v ∈ reached G.advance (singleton u))

end ChainGraph
end
end OpenCausalScience
