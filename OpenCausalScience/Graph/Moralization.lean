module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! # Ancestral moralization and d-separation

This module formalizes the reduction used by CGA's DAG separation routine.
It compares simple active paths with reachability after restricting the DAG
to the ancestors of the query sets, joining co-parents with undirected
edges, and removing the conditioned vertices.

[Perković et al. (2018), Theorem 35](https://www.jmlr.org/papers/volume18/16-319/16-319.pdf#page=26)
states the reduction and cites Lauritzen et al. (1990), Proposition 3.
-/

namespace OpenCausalScience.Moralization

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026
open BayesBall BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G : DAG n}

def Ancestor (G : DAG n) (u v : Fin n) : Prop :=
  u = v ∨ G.DirectedWalk u v

private theorem directed_prepend {u v w : Fin n}
    (edge : G.edge u v = true) (suffix : G.DirectedWalk v w) :
    G.DirectedWalk u w := by
  induction suffix with
  | single next => exact .extend (.single edge) next
  | extend _ next ih => exact .extend ih next

private theorem ancestor_prepend {u v w : Fin n}
    (edge : G.edge u v = true) (suffix : Ancestor G v w) : Ancestor G u w := by
  rcases suffix with rfl | path
  · exact .inr (.single edge)
  · exact .inr (directed_prepend edge path)

private theorem ancestor_iff_activated (C : Conditioning G) (u : Fin n) :
    C.activated u = true ↔ ∃ w, C.member w = true ∧ Ancestor G u w := by
  rw [Conditioning.activated, Bool.or_eq_true_iff, C.descendant_spec]
  constructor
  · rintro (here | ⟨w, hw, path⟩)
    · exact ⟨u, here, .inl rfl⟩
    · exact ⟨w, hw, .inr path⟩
  · rintro ⟨w, hw, rfl | path⟩
    · exact .inl hw
    · exact .inr ⟨w, hw, path⟩

private theorem inactive_child (C : Conditioning G) {u v : Fin n}
    (inactive : C.activated u = false) (edge : G.edge u v = true) :
    C.activated v = false := by
  apply Bool.eq_false_iff.mpr
  intro activated
  obtain ⟨w, hw, path⟩ := (ancestor_iff_activated C v).mp activated
  have active := (ancestor_iff_activated C u).mpr ⟨w, hw, ancestor_prepend edge path⟩
  exact Bool.false_ne_true (inactive.symm.trans active)

private theorem inactive_outside {C : Conditioning G} {u : Fin n}
    (inactive : C.activated u = false) : C.member u = false :=
  (Bool.or_eq_false_iff.mp inactive).1

structure Query (G : DAG n) where
  left : Fin n → Bool
  right : Fin n → Bool
  condition : Conditioning G

namespace Query

/-- The reflexive ancestral closure of all three query sets. -/
def relevant (Q : Query G) (v : Fin n) : Prop :=
  Q.condition.activated v = true ∨
    (∃ x, Q.left x = true ∧ Ancestor G v x) ∨
    (∃ y, Q.right y = true ∧ Ancestor G v y)

theorem relevant_iff (Q : Query G) (v : Fin n) :
    Q.relevant v ↔
      ∃ w, (Q.left w = true ∨ Q.right w = true ∨ Q.condition.member w = true) ∧
        Ancestor G v w := by
  unfold relevant
  rw [ancestor_iff_activated]
  constructor
  · rintro (⟨w, hw, path⟩ | ⟨w, hw, path⟩ | ⟨w, hw, path⟩)
    · exact ⟨w, .inr (.inr hw), path⟩
    · exact ⟨w, .inl hw, path⟩
    · exact ⟨w, .inr (.inl hw), path⟩
  · rintro ⟨w, (hw | hw | hw), path⟩
    · exact .inr (.inl ⟨w, hw, path⟩)
    · exact .inr (.inr ⟨w, hw, path⟩)
    · exact .inl ⟨w, hw, path⟩

private theorem relevant_parent {Q : Query G} {u v : Fin n}
    (edge : G.edge u v = true) (child : Q.relevant v) : Q.relevant u := by
  obtain ⟨w, hw, path⟩ := (Q.relevant_iff v).mp child
  exact (Q.relevant_iff u).mpr ⟨w, hw, ancestor_prepend edge path⟩

/-- An undirected edge of the ancestral moral graph after removing the
conditioning set. Both edge cases are the cases in CGA's construction. -/
structure MoralEdge (Q : Query G) (u v : Fin n) : Prop where
  sourceRelevant : Q.relevant u
  targetRelevant : Q.relevant v
  sourceOutside : Q.condition.member u = false
  targetOutside : Q.condition.member v = false
  distinct : u ≠ v
  connection : G.edge u v = true ∨ G.edge v u = true ∨
    ∃ c, Q.relevant c ∧ G.edge u c = true ∧ G.edge v c = true

inductive MoralWalk (Q : Query G) : Fin n → Fin n → Prop where
  | nil (u : Fin n) : Q.MoralWalk u u
  | cons {u v w : Fin n} : Q.MoralEdge u v → Q.MoralWalk v w → Q.MoralWalk u w

def MoralConnection (Q : Query G) : Prop :=
  ∃ x y, Q.left x = true ∧ Q.right y = true ∧ Q.MoralWalk x y

def DConnection (Q : Query G) : Prop :=
  ∃ x y, Q.left x = true ∧ Q.right y = true ∧ DConnected Q.condition x y

private theorem downward_relevant {Q : Query G}
    {s t : State (Fin n)} {visits : List (Fin n)}
    (path : ActiveWalk Q.condition s visits t) (down : s.2 = .down)
    (target : Q.relevant t.1) :
    Q.relevant s.1 := by
  induction path with
  | nil _ => exact target
  | @cons s next _ _ step _ ih =>
    cases dir : next.2 with
    | up =>
      have active : Q.condition.activated s.1 = true := by
        simpa [OpenTurn, down, dir] using step.2
      exact .inl active
    | down =>
      have edge : G.edge s.1 next.1 = true := by simpa [Move, dir] using step.1
      exact relevant_parent edge (ih dir target)

private theorem next_relevant {Q : Query G}
    {s next t : State (Fin n)} {visits : List (Fin n)}
    (step : ActiveStep Q.condition s next)
    (path : ActiveWalk Q.condition next visits t)
    (source : Q.relevant s.1) (target : Q.relevant t.1) :
    Q.relevant next.1 := by
  cases dir : next.2 with
  | down => exact downward_relevant path dir target
  | up =>
    have edge : G.edge next.1 s.1 = true := by simpa [Move, dir] using step.1
    exact relevant_parent edge source

private theorem move_adjacent {s t : State (Fin n)} (move : Move G s t) :
    G.edge s.1 t.1 = true ∨ G.edge t.1 s.1 = true := by
  cases dir : t.2 with
  | up => exact .inr (by simpa [Move, dir] using move)
  | down => exact .inl (by simpa [Move, dir] using move)

private theorem adjacent_distinct {u v : Fin n}
    (adjacent : G.edge u v = true ∨ G.edge v u = true) : u ≠ v := by
  intro same
  subst v
  have edge := adjacent.elim id id
  exact Nat.lt_irrefl _ (G.edge_increases _ _ edge)

private theorem collider_of_conditioned {Q : Query G} {u v : State (Fin n)}
    (conditioned : Q.condition.member u.1 = true)
    (turn : OpenTurn Q.condition u v.2) : u.2 = .down ∧ v.2 = .up := by
  by_cases collider : u.2 = .down ∧ v.2 = .up
  · exact collider
  · simp [OpenTurn, collider, conditioned] at turn

private theorem up_arrival_outside {Q : Query G}
    {s t : State (Fin n)} {visits : List (Fin n)}
    (path : ActiveWalk Q.condition s visits t) (up : s.2 = .up)
    (target : Q.condition.member t.1 = false) :
    Q.condition.member s.1 = false := by
  cases path with
  | nil _ => exact target
  | cons step _ => simpa [OpenTurn, up] using step.2

/-- Remove conditioned colliders by replacing their incident moves with
the moral edges joining their two parents. -/
theorem ActiveWalk.toMoralWalk {Q : Query G}
    {s t : State (Fin n)} {visits : List (Fin n)}
    (path : ActiveWalk Q.condition s visits t) (source : Q.relevant s.1)
    (target : Q.relevant t.1) (so : Q.condition.member s.1 = false)
    (to : Q.condition.member t.1 = false) :
    Q.MoralWalk s.1 t.1 := by
  induction size : visits.length using Nat.strongRecOn generalizing s t visits with
  | ind bound ih =>
    cases path with
    | nil _ => exact .nil _
    | @cons s next t remaining step suffix =>
      have nr := next_relevant step suffix source target
      cases member : Q.condition.member next.1 with
      | false =>
        have small : remaining.length < bound := by simp at size; omega
        have adj := move_adjacent step.1
        refine .cons ⟨source, nr, so, member, adjacent_distinct adj, ?_⟩
          (ih _ small suffix nr target member to rfl)
        rcases adj with fwd | bwd
        · exact .inl fwd
        · exact .inr (.inl bwd)
      | true =>
        cases suffix with
        | nil _ => exact (Bool.false_ne_true (to.symm.trans member)).elim
        | @cons next after t remaining turn tail =>
          obtain ⟨down, up⟩ := collider_of_conditioned member turn.2
          have first : G.edge s.1 next.1 = true := by simpa [Move, down] using step.1
          have last : G.edge after.1 next.1 = true := by simpa [Move, up] using turn.1
          have ar := relevant_parent last nr
          have ao := up_arrival_outside tail up to
          have small : remaining.length < bound := by simp at size; omega
          have rest := ih _ small tail ar target ao to rfl
          by_cases same : s.1 = after.1
          · exact same ▸ rest
          · exact .cons ⟨source, ar, so, ao, same, .inr (.inr ⟨next.1, nr, first, last⟩)⟩ rest

/-- Walk in the DAG with noncolliders open and colliders allowed anywhere
in the query's ancestral closure. A collider outside the ancestors of the
conditioning set can later be replaced by an endpoint-directed segment. -/
private def LooseStep (Q : Query G) (s next : State (Fin n)) : Prop :=
  Move G s next ∧ Q.relevant s.1 ∧
    ((s.2 = .down ∧ next.2 = .up) ∨ Q.condition.member s.1 = false)

private inductive LooseWalk (Q : Query G) : State (Fin n) → State (Fin n) → Prop where
  | nil (s : State (Fin n)) : LooseWalk Q s s
  | cons {s next t : State (Fin n)} : LooseStep Q s next → LooseWalk Q next t → LooseWalk Q s t

private theorem moral_to_loose {Q : Query G} {x y : Fin n}
    (path : Q.MoralWalk x y) (initial : Direction) :
    ∃ arrival, LooseWalk Q (x, initial) (y, arrival) := by
  induction path generalizing initial with
  | nil _ => exact ⟨initial, .nil _⟩
  | @cons u v w edge _ ih =>
    rcases edge.connection with fwd | bwd | ⟨child, childRelevant, first, last⟩
    · obtain ⟨arrival, rest⟩ := ih .down
      exact ⟨arrival, .cons (next := (v, .down)) ⟨fwd, edge.sourceRelevant, .inr edge.sourceOutside⟩ rest⟩
    · obtain ⟨arrival, rest⟩ := ih .up
      exact ⟨arrival, .cons (next := (v, .up)) ⟨bwd, edge.sourceRelevant, .inr edge.sourceOutside⟩ rest⟩
    · obtain ⟨arrival, rest⟩ := ih .up
      exact ⟨arrival, .cons (next := (child, .down))
        ⟨first, edge.sourceRelevant, .inr edge.sourceOutside⟩
        (.cons (next := (v, .up)) ⟨last, childRelevant, .inl ⟨rfl, rfl⟩⟩ rest)⟩

private theorem active_append {C : Conditioning G}
    {s t u : State (Fin n)} {first rest : List (Fin n)}
    (initialWalk : ActiveWalk C s first t) (suffix : ActiveWalk C t rest u) :
    ActiveWalk C s (first ++ rest) u := by
  induction initialWalk with
  | nil _ => exact suffix
  | cons step _ ih => exact .cons step (ih suffix)

private theorem active_snoc {C : Conditioning G}
    {s t u : State (Fin n)} {visits : List (Fin n)}
    (initialWalk : ActiveWalk C s visits t) (step : ActiveStep C t u) :
    ActiveWalk C s (visits ++ [u.1]) u :=
  active_append initialWalk (.cons step (.nil _))

private theorem forward_inactive (C : Conditioning G) {x y : Fin n}
    (inactive : C.activated x = false) (path : G.DirectedWalk x y) (initial : Direction) :
    C.activated y = false ∧ ∃ visits, ActiveWalk C (x, initial) visits (y, .down) := by
  induction path with
  | @single v edge =>
    refine ⟨inactive_child C inactive edge, [v], ?_⟩
    exact .cons (next := (v, .down))
      ⟨edge, by simp [OpenTurn, inactive_outside inactive]⟩ (.nil _)
  | @extend v w _ edge ih =>
    obtain ⟨before, visits, initialWalk⟩ := ih
    exact ⟨inactive_child C before edge, _, active_snoc initialWalk
      (u := (w, .down)) ⟨edge, by simp [OpenTurn, inactive_outside before]⟩⟩

private theorem reverse_inactive (C : Conditioning G) {x y : Fin n}
    (inactive : C.activated x = false) (path : G.DirectedWalk x y) :
    C.activated y = false ∧ ∃ visits, ActiveWalk C (y, .up) visits (x, .up) := by
  induction path with
  | @single v edge =>
    have target := inactive_child C inactive edge
    exact ⟨target, [x], .cons (next := (x, .up))
      ⟨edge, by simp [OpenTurn, inactive_outside target]⟩ (.nil _)⟩
  | @extend v w _ e ih =>
    obtain ⟨before, visits, rest⟩ := ih
    have target := inactive_child C before e
    exact ⟨target, v :: visits, .cons (next := (v, .up)) ⟨e, by simp [OpenTurn, inactive_outside target]⟩ rest⟩

private def ActivePrefix (Q : Query G) (s : State (Fin n)) : Prop :=
  ∃ x, Q.left x = true ∧ ∃ visits, ActiveWalk Q.condition (x, .up) visits s

private theorem extend_prefix {Q : Query G} {s next : State (Fin n)}
    (initialWalk : ActivePrefix Q s) (step : ActiveStep Q.condition s next) :
    ActivePrefix Q next := by
  obtain ⟨x, left, visits, path⟩ := initialWalk
  exact ⟨x, left, _, active_snoc path step⟩

private theorem finish_walk {Q : Query G} {s t : State (Fin n)}
    (initialWalk : ActivePrefix Q s) (suffixEnd : Q.right t.1 = true)
    (targetOutside : Q.condition.member t.1 = false)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (suffix : ∃ visits, ActiveWalk Q.condition s visits t) :
    Q.DConnection := by
  obtain ⟨x, hx, before, initialWalk⟩ := initialWalk
  obtain ⟨after, suffix⟩ := suffix
  obtain ⟨visits, ⟨y, dir⟩, simple, endpoint, nodup, _⟩ :=
    (active_append initialWalk suffix).to_simple
  change y = t.1 at endpoint
  subst y
  exact ⟨x, t.1, hx, suffixEnd, leftOutside x hx, targetOutside, visits, dir, simple, nodup⟩

/-- Follow the loose walk with an active prefix. An inactive collider has
a directed path to the left or right query set. Use that path to replace
the prefix or finish an active walk to the right query set. -/
private theorem repair {Q : Query G} {s t : State (Fin n)}
    (route : LooseWalk Q s t)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (target : Q.right t.1 = true) (initialWalk : ActivePrefix Q s) :
    Q.DConnection := by
  classical
  induction route with
  | nil s => exact finish_walk initialWalk target (rightOutside _ target) leftOutside ⟨[], .nil _⟩
  | @cons s next _ step _ ih =>
    by_cases legal : OpenTurn Q.condition s next.2
    · exact ih target (extend_prefix initialWalk ⟨step.1, legal⟩)
    have collider : s.2 = .down ∧ next.2 = .up := by
      by_cases collider : s.2 = .down ∧ next.2 = .up
      · exact collider
      · exact (legal (by simp [OpenTurn, collider, step.2.2.resolve_left collider])).elim
    have inactive : Q.condition.activated s.1 = false := by
      apply Bool.eq_false_iff.mpr
      intro active
      exact legal (by simp [OpenTurn, collider.1, collider.2, active])
    rcases step.2.1 with active | ⟨x, left, reach⟩ | ⟨y, right, reach⟩
    · exact (Bool.false_ne_true (inactive.symm.trans active)).elim
    · have newPrefix : ActivePrefix Q (s.1, .up) := by
        rcases reach with same | path
        · subst x
          exact ⟨s.1, left, [], .nil _⟩
        · obtain ⟨_, visits, reverseWalk⟩ := reverse_inactive Q.condition inactive path
          exact ⟨x, left, visits, reverseWalk⟩
      have move : Move G (s.1, .up) next := by
        cases dir : next.2 <;> simpa [Move, dir] using step.1
      have turn : OpenTurn Q.condition (s.1, .up) next.2 := by
        simp [OpenTurn, inactive_outside inactive]
      exact ih target (extend_prefix newPrefix ⟨move, turn⟩)
    · rcases reach with same | path
      · subst y
        exact finish_walk initialWalk right (rightOutside _ right) leftOutside ⟨[], .nil _⟩
      · obtain ⟨outside, visits, tail⟩ := forward_inactive Q.condition inactive path s.2
        have tail' : ActiveWalk Q.condition s visits (y, .down) := by
          rcases s with ⟨_, _⟩
          exact tail
        exact finish_walk initialWalk right (inactive_outside outside) leftOutside ⟨visits, tail'⟩

theorem dConnection_iff_moralConnection (Q : Query G)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false) :
    Q.DConnection ↔ Q.MoralConnection := by
  constructor
  · rintro ⟨x, y, hx, hy, outsideX, outsideY, visits, arrival, path, _⟩
    have rx : Q.relevant x := .inr (.inl ⟨x, hx, .inl rfl⟩)
    have ry : Q.relevant y := .inr (.inr ⟨y, hy, .inl rfl⟩)
    exact ⟨x, y, hx, hy, ActiveWalk.toMoralWalk path rx ry outsideX outsideY⟩
  · rintro ⟨x, y, hx, hy, path⟩
    obtain ⟨arrival, route⟩ := moral_to_loose path .up
    exact repair route leftOutside rightOutside hy ⟨x, hx, [], .nil _⟩

/-- Set-valued d-separation is separation in the ancestral moral graph
after deleting the conditioned vertices. -/
theorem dSeparation_iff_no_moralConnection (Q : Query G)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false) :
    ¬ Q.DConnection ↔ ¬ Q.MoralConnection :=
  not_congr (dConnection_iff_moralConnection Q leftOutside rightOutside)

end Query

end

end OpenCausalScience.Moralization
