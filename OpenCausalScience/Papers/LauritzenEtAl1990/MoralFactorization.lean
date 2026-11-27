module
public import OpenCausalScience.Graph.Moralization
public import OpenCausalScience.Papers.LauritzenEtAl1990.KernelElimination
public import OpenCausalScience.Probability.ProductLaw

/-! # Separating the families of an ancestral product

Every unconditioned child-parent family lies on one side of a moral
separation. The corresponding density therefore splits, with the
conditioned coordinates held fixed. Source: Lauritzen et al. (1990),
https://doi.org/10.1002/net.3230200503.
-/

namespace OpenCausalScience.Papers.LauritzenEtAl1990.MoralFactorization

open OpenCausalScience.Moralization
open Probability (FiniteLaw)
open KernelElimination

@[expose] public section

variable {n : Nat} {G : DAG n}

theorem parent_is_relevant {Q : Query G} {u v : Fin n}
    (edge : G.edge u v = true) (relevant : Q.relevant v) : Q.relevant u := by
  obtain ⟨w, inQuery, rfl | path⟩ := (Q.relevant_iff v).mp relevant
  · exact (Q.relevant_iff u).mpr ⟨v, inQuery, .inr (.single edge)⟩
  · apply (Q.relevant_iff u).mpr
    refine ⟨w, inQuery, .inr ?_⟩
    clear inQuery
    induction path with
    | single next => exact .extend (.single edge) next
    | extend _ next ih => exact .extend ih next

theorem family_vertex_relevant {Q : Query G} {child u : Fin n}
    (childRelevant : Q.relevant child) (family : Family G child u) : Q.relevant u := by
  rcases family with rfl | parent
  · exact childRelevant
  · exact parent_is_relevant parent childRelevant

theorem moral_edge_between_family_members {Q : Query G} {child u v : Fin n}
    (relevant : Q.relevant child) (left : Family G child u)
    (other : Family G child v) (distinct : u ≠ v)
    (outsideU : Q.condition.member u = false) (outsideV : Q.condition.member v = false) :
    Q.MoralEdge u v := by
  refine ⟨family_vertex_relevant relevant left, family_vertex_relevant relevant other,
    outsideU, outsideV, distinct, ?_⟩
  rcases left with rfl | parentU
  · rcases other with rfl | parentV
    · exact (distinct rfl).elim
    · exact .inr (.inl parentV)
  · rcases other with rfl | parentV
    · exact .inl parentU
    · exact .inr (.inr ⟨child, relevant, parentU, parentV⟩)

theorem moral_walk_extend {Q : Query G} {u v w : Fin n}
    (first : Q.MoralWalk u v) (last : Q.MoralEdge v w) : Q.MoralWalk u w := by
  induction first with
  | nil => exact .cons last (.nil _)
  | cons step _ ih => exact .cons step (ih last)

def ReachedFromLeft (Q : Query G) (v : Fin n) : Prop :=
  ∃ u, Q.left u = true ∧ Q.MoralWalk u v

noncomputable def leftSide (Q : Query G) (v : Fin n) : Bool :=
  open Classical in decide (ReachedFromLeft Q v)

theorem left_side_iff (Q : Query G) (v : Fin n) :
    leftSide Q v = true ↔ ReachedFromLeft Q v := by
  simp [leftSide]

theorem moral_edge_same_side {Q : Query G} {u v : Fin n} (edge : Q.MoralEdge u v) :
    leftSide Q u = leftSide Q v := by
  have reverse : Q.MoralEdge v u :=
    ⟨edge.targetRelevant, edge.sourceRelevant, edge.targetOutside, edge.sourceOutside,
      Ne.symm edge.distinct, by
        rcases edge.connection with f | r | ⟨c, h, a, b⟩
        · exact .inr (.inl f)
        · exact .inl r
        · exact .inr (.inr ⟨c, h, b, a⟩)⟩
  apply Bool.eq_iff_iff.mpr
  rw [left_side_iff, left_side_iff]
  constructor
  · rintro ⟨x, start, walk⟩
    exact ⟨x, start, moral_walk_extend walk edge⟩
  · rintro ⟨x, start, walk⟩
    exact ⟨x, start, moral_walk_extend walk reverse⟩

noncomputable def owner (Q : Query G) (child : Fin n) : Bool :=
  open Classical in decide (∃ u, Family G child u ∧ Q.condition.member u = false ∧
    leftSide Q u = true)

theorem family_has_one_side (Q : Query G) (child u : Fin n)
    (relevant : Q.relevant child) (family : Family G child u)
    (outside : Q.condition.member u = false) : leftSide Q u = owner Q child := by
  apply Bool.eq_iff_iff.mpr
  simp only [owner, decide_eq_true_eq]
  constructor
  · intro onLeft
    exact ⟨u, family, outside, onLeft⟩
  · rintro ⟨v, other, outsideV, onLeft⟩
    by_cases equal : u = v
    · simpa [equal] using onLeft
    · have connected := moral_edge_between_family_members relevant family other
        equal outside outsideV
      exact (moral_edge_same_side connected).trans onLeft

theorem separated_families_factorize {A : Type} {states : List A}
    (Q : Query G) (K : Kernels G states)
    (relevant : List (Fin n)) (allRelevant : ∀ v ∈ relevant, Q.relevant v)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.DConnection) :
    (∀ v, Q.left v = true → leftSide Q v = true) ∧
    (∀ v, Q.right v = true → leftSide Q v = false) ∧
    ∀ left right : State n A,
      (∀ v, Q.condition.member v = true → left v = right v) →
      density K relevant (splice (leftSide Q) left right) =
        density K (relevant.filter (owner Q)) left *
          density K (relevant.filter (fun v => !owner Q v)) right := by
  have noWalk := (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside).mp separated
  refine ⟨?_, ?_, ?_⟩
  · intro v here
    exact (left_side_iff Q v).mpr ⟨v, here, .nil _⟩
  · intro v there
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨u, here, walk⟩ := (left_side_iff Q v).mp hit
    exact noWalk ⟨u, v, here, there, walk⟩
  · intro left right agree
    exact split_conditioned_families K relevant Q.condition.member (leftSide Q) (owner Q)
      left right agree (fun child mem u onScope outside =>
        family_has_one_side Q child u (allRelevant child mem) onScope outside)

theorem directed_ancestor_le
    (topological : ∀ u v, G.edge u v = true → u < v)
    {u v : Fin n} (ancestor : Ancestor G u v) : u ≤ v := by
  rcases ancestor with rfl | path
  · exact Fin.le_refl _
  · induction path with
    | single edge => exact Nat.le_of_lt (topological _ _ edge)
    | extend _ next ih => exact Nat.le_trans ih (Nat.le_of_lt (topological _ _ next))

def readCoordinates {A : Type} (selected : Fin n → Bool) (x : State n A) :
    Fin n → Option A :=
  fun v => if selected v then some (x v) else none

/-- The joint slice specified by the two Cartesian lists has the
ancestral density and independent query observables. The equality
between this coordinate enumeration and the caller's original law is
kept as a separate reindexing step. -/
theorem moral_product_law {A : Type} {states : List A}
    (Q : Query G) (K : Kernels G states)
    (relevant : List (Fin n)) (allRelevant : ∀ v ∈ relevant, Q.relevant v)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.DConnection)
    (left right : FiniteLaw (State n A)) (fixed : State n A)
    (leftCell : ∀ x ∈ left.atoms, ∀ u, Q.condition.member u = true → x u = fixed u)
    (rightCell : ∀ y ∈ right.atoms, ∀ u, Q.condition.member u = true → y u = fixed u)
    (leftWeight : ∀ x ∈ left.atoms, left.weight x = density K (relevant.filter (owner Q)) x)
    (rightWeight : ∀ y ∈ right.atoms, right.weight y =
      density K (relevant.filter (fun v => !owner Q v)) y) :
    (∀ pair ∈ (left.productLaw right).atoms,
      (left.productLaw right).weight pair =
        density K relevant (splice (leftSide Q) pair.1 pair.2)) ∧
    (left.productLaw right).IndependentAt
      (fun pair => readCoordinates Q.left (splice (leftSide Q) pair.1 pair.2))
      (fun pair => readCoordinates Q.right (splice (leftSide Q) pair.1 pair.2))
      (fun _ => true) := by
  obtain ⟨onLeft, onRight, split⟩ :=
    separated_families_factorize Q K relevant allRelevant leftOutside rightOutside separated
  constructor
  · rintro ⟨x, y⟩ occurs
    obtain ⟨first, firstMem, rest⟩ := List.mem_flatMap.mp occurs
    obtain ⟨second, secondMem, equal⟩ := List.mem_map.mp rest
    cases equal
    change left.weight x * right.weight y =
      density K relevant (splice (leftSide Q) x y)
    rw [leftWeight x firstMem, rightWeight y secondMem]
    exact (split x y (fun u given => (leftCell x firstMem u given).trans
      (rightCell y secondMem u given).symm)).symm
  · have readLeft :
        (fun pair : State n A × State n A =>
          readCoordinates Q.left (splice (leftSide Q) pair.1 pair.2)) =
          readCoordinates Q.left ∘ Prod.fst := by
      funext pair v
      by_cases query : Q.left v = true
      · simp [readCoordinates, query, splice, onLeft v query]
      · simp [readCoordinates, query]
    have readRight :
        (fun pair : State n A × State n A =>
          readCoordinates Q.right (splice (leftSide Q) pair.1 pair.2)) =
          readCoordinates Q.right ∘ Prod.snd := by
      funext pair v
      by_cases query : Q.right v = true
      · simp [readCoordinates, query, splice, onRight v query]
      · simp [readCoordinates, query]
    rw [readLeft, readRight]
    exact left.product_independent right _ _

/-- A vertex is d-separated from its preceding nonparents given all
of its parents. The universal global Markov property can therefore
be applied to these ordered local queries. -/
theorem ordered_local_separation (Q : Query G) (v : Fin n)
    (topological : ∀ u v, G.edge u v = true → u < v)
    (starts : ∀ u, Q.left u = true → u = v)
    (earlier : ∀ u, Q.right u = true → u < v)
    (conditioned : ∀ u, Q.condition.member u = true ↔ G.edge u v = true)
    (rightOutside : ∀ u, Q.right u = true → Q.condition.member u = false) :
    ¬ Q.DConnection := by
  have noSelf : G.edge v v ≠ true := fun edge => Nat.lt_irrefl _ (topological _ _ edge)
  have leftOutside (u : Fin n) (here : Q.left u = true) : Q.condition.member u = false := by
    have equal := starts u here
    subst u
    exact Bool.eq_false_iff.mpr (fun mem => noSelf ((conditioned _).mp mem))
  apply (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside).mpr
  rintro ⟨first, last, here, there, walk⟩
  have equal := starts first here
  subst first
  have scope (w : Fin n) (inside : Q.relevant w) : w ≤ v := by
    obtain ⟨u, endpoint, ancestor⟩ := (Q.relevant_iff w).mp inside
    have le := directed_ancestor_le topological ancestor
    rcases endpoint with here | there | given
    · exact (starts u here) ▸ le
    · exact Nat.le_trans le (Nat.le_of_lt (earlier u there))
    · exact Nat.le_trans le (Nat.le_of_lt (topological u v ((conditioned u).mp given)))
  cases walk with
  | nil => exact Nat.lt_irrefl _ (earlier v there)
  | @cons _ u _ step _ =>
    rcases step.connection with out | into | ⟨child, childRelevant, parent, _⟩
    · exact Nat.not_lt_of_ge (scope u step.targetRelevant) (topological v u out)
    · exact Bool.false_ne_true (step.targetOutside.symm.trans ((conditioned u).mpr into))
    · exact Nat.not_lt_of_ge (scope child childRelevant) (topological v child parent)

end
end OpenCausalScience.Papers.LauritzenEtAl1990.MoralFactorization
