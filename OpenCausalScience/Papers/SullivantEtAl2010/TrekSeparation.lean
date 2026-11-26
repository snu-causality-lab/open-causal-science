module
public import OpenCausalScience.Graph.DAG

/-! Sullivant, Talaska and Draisma (2010), Definition 2.7 and the
two-copy DAG in Proposition 3.5. -/

@[expose] public section

namespace OpenCausalScience.Papers.SullivantEtAl2010.TrekSeparation

variable {n : Nat}

/-- A directed path avoiding a set, including at its endpoints. -/
inductive Avoiding (G : DAG n) (removed : Fin n → Prop) : Fin n → Fin n → Prop
  | zero (v) : ¬ removed v → Avoiding G removed v v
  | step {u v w} :
      ¬ removed u → G.edge u v = true → Avoiding G removed v w → Avoiding G removed u w

theorem Avoiding.start_not_removed {G : DAG n} {removed : Fin n → Prop}
    {u v : Fin n} (path : Avoiding G removed u v) : ¬ removed u := by
  cases path with
  | zero _ h => exact h
  | step h _ _ => exact h

inductive Copy (n : Nat)
  | left : Fin n → Copy n
  | right : Fin n → Copy n

/-- The left copy has reversed arrows and the right copy has original arrows.
The only transitions between copies go from left to right at the same vertex. -/
inductive Route (G : DAG n) (leftRemoved rightRemoved : Fin n → Prop)
    (target : Fin n) : Copy n → Prop
  | finish : ¬ rightRemoved target → Route G leftRemoved rightRemoved target (.right target)
  | rightStep {u v} : ¬ rightRemoved u → G.edge u v = true →
      Route G leftRemoved rightRemoved target (.right v) →
      Route G leftRemoved rightRemoved target (.right u)
  | cross {v} : ¬ leftRemoved v → Route G leftRemoved rightRemoved target (.right v) →
      Route G leftRemoved rightRemoved target (.left v)
  | leftStep {u v} : ¬ leftRemoved u → G.edge v u = true →
      Route G leftRemoved rightRemoved target (.left v) →
      Route G leftRemoved rightRemoved target (.left u)

private theorem route_readout {G : DAG n} {L R : Fin n → Prop} {b : Fin n}
    {start : Copy n} (route : Route G L R b start) :
    match start with
    | .right a => Avoiding G R a b
    | .left a => ∃ top, Avoiding G L top a ∧ Avoiding G R top b := by
  induction route with
  | finish h => exact .zero _ h
  | rightStep h edge _ ih => exact .step h edge ih
  | cross h _ ih => exact ⟨_, .zero _ h, ih⟩
  | leftStep h edge _ ih =>
      obtain ⟨top, left, right⟩ := ih
      exact ⟨top, append left edge h, right⟩
where
  append {u v w : Fin n} (path : Avoiding G L u v) (edge : G.edge v w = true)
      (allowed : ¬ L w) : Avoiding G L u w := by
    induction path with
    | zero _ h => exact .step h edge (.zero _ allowed)
    | step h first _ ih => exact .step h first (ih edge)

private theorem right_route {G : DAG n} {L R : Fin n → Prop} {u v : Fin n}
    (path : Avoiding G R u v) : Route G L R v (.right u) := by
  induction path with
  | zero _ h => exact .finish h
  | step h edge _ ih => exact .rightStep h edge ih

private theorem left_route {G : DAG n} {L R : Fin n → Prop} {u v b : Fin n}
    (path : Avoiding G L u v) (after : Route G L R b (.left u)) :
    Route G L R b (.left v) := by
  induction path with
  | zero _ _ => exact after
  | step _ edge rest ih => exact ih (.leftStep rest.start_not_removed edge after)

theorem route_iff_unblocked_trek {G : DAG n} {L R : Fin n → Prop} {a b : Fin n} :
    Route G L R b (.left a) ↔ ∃ top, Avoiding G L top a ∧ Avoiding G R top b := by
  constructor
  · exact route_readout
  · rintro ⟨_, left, right⟩
    exact left_route left (.cross left.start_not_removed (right_route right))

/-- Definition 2.7 expressed by exclusion of a pair of unblocked sides. -/
def Separates (G : DAG n) (A B L R : Fin n → Prop) : Prop :=
  ∀ a b, A a → B b → ¬ ∃ top, Avoiding G L top a ∧ Avoiding G R top b

theorem separates_iff_no_route {G : DAG n} {A B L R : Fin n → Prop} :
    Separates G A B L R ↔ ∀ a b, A a → B b → ¬ Route G L R b (.left a) := by
  simp only [Separates, route_iff_unblocked_trek]

theorem overlap_requires_removal {G : DAG n} {A B L R : Fin n → Prop} {v : Fin n}
    (sep : Separates G A B L R) (inA : A v) (inB : B v) : L v ∨ R v := by
  by_cases left : L v
  · exact Or.inl left
  by_cases right : R v
  · exact Or.inr right
  exact False.elim (sep v v inA inB ⟨v, .zero v left, .zero v right⟩)

end OpenCausalScience.Papers.SullivantEtAl2010.TrekSeparation
