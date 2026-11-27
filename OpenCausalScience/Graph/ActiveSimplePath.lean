module
public import Std

@[expose] public section

namespace OpenCausalScience.ActiveSimplePath

variable {Vertex : Type}

/-- An ancestor of a conditioned vertex, including the vertex itself. -/
inductive Activated (arrow : Vertex → Vertex → Prop)
    (conditioned : Vertex → Prop) : Vertex → Prop
  | conditioned {v} : conditioned v → Activated arrow conditioned v
  | parent {v w} : arrow v w → Activated arrow conditioned w → Activated arrow conditioned v

def Adjacent (arrow : Vertex → Vertex → Prop) (a b : Vertex) : Prop :=
  arrow a b ∨ arrow b a

/-- A collider needs a conditioned descendant, possibly itself. Other
interior vertices must lie outside the conditioning set. -/
def OpenTurn (arrow : Vertex → Vertex → Prop) (conditioned : Vertex → Prop)
    (a b c : Vertex) : Prop :=
  ((arrow a b ∧ arrow c b) ∧ Activated arrow conditioned b) ∨
    (¬ (arrow a b ∧ arrow c b) ∧ ¬ conditioned b)

/-- The list after the first two vertices of an active walk, with all
interior turns checked. Simplicity is imposed by `DConnected`. -/
inductive ActiveSuffix (arrow : Vertex → Vertex → Prop)
    (conditioned : Vertex → Prop) : Vertex → Vertex → List Vertex → Vertex → Prop
  | last {a b} : Adjacent arrow a b → ActiveSuffix arrow conditioned a b [] b
  | cons {a b c rest finish} :
      Adjacent arrow a b →
      OpenTurn arrow conditioned a b c →
      ActiveSuffix arrow conditioned b c rest finish →
      ActiveSuffix arrow conditioned a b (c :: rest) finish

theorem ActiveSuffix.first_adjacent {arrow : Vertex → Vertex → Prop}
    {conditioned : Vertex → Prop} {a b finish : Vertex} {rest : List Vertex}
    (walk : ActiveSuffix arrow conditioned a b rest finish) : Adjacent arrow a b := by
  cases walk <;> assumption

/-- An active simple path of positive length. For a d-connection query
the caller checks that the endpoints are outside the conditioning set. -/
def DConnected (arrow : Vertex → Vertex → Prop) (conditioned : Vertex → Prop)
    (start finish : Vertex) : Prop :=
  ∃ next rest, ActiveSuffix arrow conditioned start next rest finish ∧
    (start :: next :: rest).Nodup

end OpenCausalScience.ActiveSimplePath

end
