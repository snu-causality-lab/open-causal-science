module
public import OpenCausalScience.Graph.ColliderAugmentation
public import OpenCausalScience.Graph.MixedAnterior

/-! # Connections in the anterior augmented graph

Expand each augmented edge into a collider walk. The concatenation may
contain a collider outside the directed ancestors of the conditioning set.
Such a collider has a directed path to a query endpoint, which replaces the
prefix or suffix of the walk.

[Richardson and Spirtes (2002), Theorem 3.18](https://doi.org/10.1214/aos/1031689015)
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n}
variable {left right relevant conditioning : Fin n → Bool}

/-- A walk along augmented edges, with conditioned vertices deleted. -/
inductive AugmentedWalk (G : MixedGraph n) (relevant conditioning : Fin n → Bool) :
    Fin n → Fin n → Prop where
  | nil (v : Fin n) : AugmentedWalk G relevant conditioning v v
  | cons {u v w : Fin n} : G.colliderAugmented relevant u v = true →
      conditioning u = false → conditioning v = false →
      AugmentedWalk G relevant conditioning v w → AugmentedWalk G relevant conditioning u w

private def looseTurn (relevant conditioning : Fin n → Bool)
    (state : Arrival n) (outgoing : Bool) : Prop :=
  if state.2 && outgoing then relevant state.1 = true else conditioning state.1 = false

private def LooseStep (G : MixedGraph n) (relevant conditioning : Fin n → Bool)
    (source target : Arrival n) : Prop :=
  ∃ outgoing, G.edge source.1 outgoing target.1 target.2 = true ∧
    looseTurn relevant conditioning source outgoing

private inductive LooseWalk (G : MixedGraph n) (relevant conditioning : Fin n → Bool) :
    Arrival n → Arrival n → Prop where
  | nil (state : Arrival n) : LooseWalk G relevant conditioning state state
  | cons {source middle target : Arrival n} :
      LooseStep G relevant conditioning source middle →
      LooseWalk G relevant conditioning middle target →
      LooseWalk G relevant conditioning source target

private theorem LooseWalk.append {source middle target : Arrival n}
    (front : LooseWalk G relevant conditioning source middle)
    (back : LooseWalk G relevant conditioning middle target) :
    LooseWalk G relevant conditioning source target := by
  induction front with
  | nil => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem ColliderWalk.to_loose {source target : Arrival n}
    (walk : G.ColliderWalk relevant source target) (incoming : Bool)
    (turn : looseTurn relevant conditioning (source.1, incoming) source.2) :
    LooseWalk G relevant conditioning (source.1, incoming) target := by
  induction walk generalizing incoming with
  | single _ _ edge => exact .cons ⟨_, edge, turn⟩ (.nil _)
  | join front _ middle finish =>
    exact (middle incoming turn).append (finish true (by
      simpa [looseTurn] using front.target_relevant))

private theorem AugmentedWalk.to_loose {source target : Fin n}
    (walk : G.AugmentedWalk relevant conditioning source target) (incoming : Bool) :
    ∃ mark, LooseWalk G relevant conditioning (source, incoming) (target, mark) := by
  induction walk generalizing incoming with
  | nil => exact ⟨incoming, .nil _⟩
  | @cons u v _ edge outside _ _ ih =>
    obtain ⟨_, depart, arrive, segment⟩ := (G.collider_augmented_iff relevant _ _).mp edge
    obtain ⟨mark, tail⟩ := ih arrive
    have turn : looseTurn relevant conditioning (u, incoming) depart := by
      simp [looseTurn, outside, segment.source_relevant]
    exact ⟨mark, (segment.to_loose incoming turn).append tail⟩

/-- A prefix from a left endpoint, with a tail at a zero-length prefix. -/
private def ActivePrefix (G : MixedGraph n) (left conditioning : Fin n → Bool)
    (state : Arrival n) : Prop :=
  (left state.1 = true ∧ state.2 = false) ∨
    ∃ first, G.Seed left first ∧ Reach (G.Step conditioning) first state

private theorem ActivePrefix.extend {source target : Arrival n}
    (prior : ActivePrefix G left conditioning source) (step : G.Step conditioning source target) :
    ActivePrefix G left conditioning target := by
  rcases prior with ⟨start, _⟩ | ⟨first, seeded, reached⟩
  · obtain ⟨outgoing, edge, _⟩ := step
    exact .inr ⟨target, ⟨source.1, outgoing, start, edge⟩, .refl _⟩
  · exact .inr ⟨first, seeded, .extend reached step⟩

private theorem ActivePrefix.finish {state : Arrival n}
    (prior : ActivePrefix G left conditioning state) (endpoint : right state.1 = true)
    (disjoint : ∀ v, left v = true → right v = false) :
    G.WalkConnected left right conditioning := by
  rcases prior with ⟨start, _⟩ | ⟨first, seeded, reached⟩
  · rw [disjoint _ start] at endpoint
    contradiction
  · exact ⟨first, state, seeded, reached, endpoint⟩

private theorem inactive_outside {v : Fin n} (inactive : ¬ G.AncestorOf conditioning v) :
    conditioning v = false :=
  Bool.eq_false_iff.mpr fun included => inactive (.conditioned included)

private theorem prefix_left_of_ancestor {v : Fin n} (anc : G.AncestorOf left v)
    (inactive : ¬ G.AncestorOf conditioning v) :
    ActivePrefix G left conditioning (v, false) := by
  induction anc with
  | conditioned start => exact .inl ⟨start, rfl⟩
  | parent edge _ ih =>
    exact (ih (fun child => inactive (.parent edge child))).extend
      ⟨true, (G.symmetric _ _ _ _).symm.trans edge,
        by simpa [openTurn] using inactive_outside (fun child => inactive (.parent edge child))⟩

private theorem finish_right_of_ancestor {v : Fin n} (anc : G.AncestorOf right v)
    (inactive : ¬ G.AncestorOf conditioning v) (incoming : Bool)
    (prior : ActivePrefix G left conditioning (v, incoming))
    (disjoint : ∀ w, left w = true → right w = false) :
    G.WalkConnected left right conditioning := by
  induction anc generalizing incoming with
  | conditioned endpoint => exact prior.finish endpoint disjoint
  | parent edge _ ih =>
    exact ih (fun child => inactive (.parent edge child)) true
      (prior.extend ⟨false, edge, by simpa [openTurn] using inactive_outside inactive⟩)

private theorem repair {source target : Arrival n}
    (route : LooseWalk G (G.anterior (fun v => (left v || right v) || conditioning v))
      conditioning source target)
    (disjoint : ∀ v, left v = true → right v = false) (endpoint : right target.1 = true)
    (front : ActivePrefix G left conditioning source) :
    G.WalkConnected left right conditioning := by
  classical
  induction route with
  | nil => exact front.finish endpoint disjoint
  | @cons current next _ move _ ih =>
    obtain ⟨outgoing, edge, turn⟩ := move
    by_cases opens : G.openTurn conditioning current outgoing
    · exact ih endpoint (front.extend ⟨outgoing, edge, opens⟩)
    have collider : (current.2 && outgoing) = true := by
      by_cases isCollider : (current.2 && outgoing) = true
      · exact isCollider
      · exact (opens (by simpa [openTurn, looseTurn, isCollider] using turn)).elim
    have inactive : ¬ G.AncestorOf conditioning current.1 :=
      fun active => opens (by simpa [openTurn, collider] using active)
    have marks : current.2 = true ∧ outgoing = true := by
      simpa only [Bool.and_eq_true] using collider
    have incident : ∃ v mark, G.edge current.1 true v mark = true :=
      ⟨next.1, next.2, marks.2 ▸ edge⟩
    have included : G.anterior (fun v => (left v || right v) || conditioning v) current.1 = true := by
      simpa [looseTurn, collider] using turn
    have ancestor := ((G.anterior_iff _ _).mp included).to_ancestor incident
    rcases ancestor.union with endpointAncestor | activated
    · rcases endpointAncestor.union with toLeft | toRight
      · have restarted := prefix_left_of_ancestor toLeft inactive
        have step : G.Step conditioning (current.1, false) next :=
          ⟨outgoing, edge, by simpa [openTurn] using inactive_outside inactive⟩
        exact ih endpoint (restarted.extend step)
      · exact finish_right_of_ancestor toRight inactive current.2
          (by simpa using front) disjoint
    · exact (inactive activated).elim

/-- A connection in the augmented anterior graph yields an active walk
in the mixed graph. The query endpoints are disjoint. -/
theorem walkConnected_of_augmentedWalk (G : MixedGraph n)
    (left right conditioning : Fin n → Bool) {source target : Fin n}
    (walk : G.AugmentedWalk (G.anterior (fun v => (left v || right v) || conditioning v))
      conditioning source target)
    (hx : left source = true) (hy : right target = true)
    (disjoint : ∀ v, left v = true → right v = false) :
    G.WalkConnected left right conditioning := by
  obtain ⟨_, loose⟩ := walk.to_loose false
  exact repair loose disjoint hy (.inl ⟨hx, rfl⟩)

end

end OpenCausalScience.MixedGraph
