module
public import Std

/-! # Mixed edges and active walks

The two endpoint marks identify an edge. A tail is false and an arrowhead is
true. Parallel directed and bidirected edges of an ADMG therefore stay
distinct. Undirected edges obey the ancestral-graph endpoint restriction in
Richardson and Spirtes (2002), §3.1(ii). This edge representation and
that restriction suffice for the separation proof.

Source: https://doi.org/10.1214/aos/1031689015
-/

namespace OpenCausalScience

@[expose] public section

/-- A finite mixed graph with no arrowhead incident to an undirected endpoint. -/
structure MixedGraph (n : Nat) where
  edge : Fin n → Bool → Fin n → Bool → Bool
  symmetric : ∀ u a v b, edge u a v b = edge v b u a
  loop_free : ∀ u a b, edge u a u b = false
  no_arrow_of_undirected : ∀ {u v w : Fin n} {mark : Bool},
    edge u false v false = true → edge u true w mark = false

namespace MixedGraph

universe u

variable {n : Nat}

abbrev Arrival (n : Nat) := Fin n × Bool

/-- Reflexive directed ancestry of the conditioning set. -/
inductive AncestorOf (G : MixedGraph n) (conditioning : Fin n → Bool) : Fin n → Prop
  | conditioned {v} : conditioning v = true → AncestorOf G conditioning v
  | parent {u v} : G.edge u false v true = true →
      AncestorOf G conditioning v → AncestorOf G conditioning u

/-- The interior vertex is a collider exactly when both endpoint marks are heads. -/
def openTurn (G : MixedGraph n) (conditioning : Fin n → Bool)
    (s : Arrival n) (outgoing : Bool) : Prop :=
  if s.2 && outgoing then G.AncestorOf conditioning s.1 else conditioning s.1 = false

def Step (G : MixedGraph n) (conditioning : Fin n → Bool) (s t : Arrival n) : Prop :=
  ∃ outgoing, G.edge s.1 outgoing t.1 t.2 = true ∧ G.openTurn conditioning s outgoing

inductive Reach {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (u) : Reach R u u
  | extend {u v w} : Reach R u v → R v w → Reach R u w

/-- Seed an arrival with one edge from a left endpoint. -/
def Seed (G : MixedGraph n) (left : Fin n → Bool) (s : Arrival n) : Prop :=
  ∃ x outgoing, left x = true ∧ G.edge x outgoing s.1 s.2 = true

def WalkConnected (G : MixedGraph n) (left right conditioning : Fin n → Bool) : Prop :=
  ∃ first last, G.Seed left first ∧ Reach (G.Step conditioning) first last ∧ right last.1 = true

end MixedGraph
end
end OpenCausalScience
