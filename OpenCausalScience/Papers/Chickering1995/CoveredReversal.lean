module
public import OpenCausalScience.Graph.Moralization

/-! The graph-separation direction of Lemma 1 in Chickering (UAI 1995).
Compare the ancestral moral graphs before and after a covered reversal.
When the old tail drops out of the ancestral set, its neighbors can use
the new tail instead. -/

namespace OpenCausalScience.Papers.Chickering1995.CoveredReversal

open Moralization

@[expose] public section

variable {n : Nat} {G H : DAG n} {a b : Fin n}

/-- The two DAGs differ only by reversing `a → b`, whose endpoints have
the same parents outside the pair in the original DAG. -/
structure Reversal (G H : DAG n) (a b : Fin n) : Prop where
  forward : G.edge a b = true
  reverse : H.edge b a = true
  unchanged : ∀ u v, ¬ (u = a ∧ v = b) → ¬ (u = b ∧ v = a) →
    (G.edge u v = true ↔ H.edge u v = true)
  parents : ∀ u, u ≠ a → u ≠ b → (G.edge u a = true ↔ G.edge u b = true)

namespace Reversal

private theorem edge_distinct {D : DAG n} {u v : Fin n} (edge : D.edge u v = true) :
    u ≠ v := by
  intro same
  subst v
  exact D.no_directed_cycle u (.single edge)

private theorem opposite_absent {D : DAG n} {u v : Fin n} (edge : D.edge u v = true) :
    D.edge v u ≠ true :=
  fun opposite => D.no_directed_cycle u (.extend (.single edge) opposite)

theorem symm (R : Reversal G H a b) : Reversal H G b a where
  forward := R.reverse
  reverse := R.forward
  unchanged u v first second := (R.unchanged u v second first).symm
  parents u hb ha :=
    ((R.unchanged u b (fun e => ha e.1) (fun e => hb e.1)).symm.trans
      (R.parents u ha hb).symm).trans
        (R.unchanged u a (fun e => ha e.1) (fun e => hb e.1))

private theorem retained (R : Reversal G H a b) {u v : Fin n}
    (edge : G.edge u v = true) (kept : ¬ (u = a ∧ v = b)) : H.edge u v = true :=
  (R.unchanged u v kept (by rintro ⟨rfl, rfl⟩; exact opposite_absent R.forward edge)).mp edge

private theorem parent_of_old_tail (R : Reversal G H a b) {u : Fin n}
    (edge : G.edge u a = true) : H.edge u b = true := by
  have ha := edge_distinct edge
  have hb : u ≠ b := by
    rintro rfl
    exact opposite_absent R.forward edge
  exact R.retained ((R.parents u ha hb).mp edge) (fun e => ha e.1)

private theorem relevant_parent {D : DAG n} {Q : Query D} {u v : Fin n}
    (edge : D.edge u v = true) (hv : Q.relevant v) : Q.relevant u := by
  obtain ⟨w, hx, path⟩ := (Q.relevant_iff v).mp hv
  refine (Q.relevant_iff u).mpr ⟨w, hx, .inr ?_⟩
  rcases path with rfl | path
  · exact .single edge
  · clear hx
    induction path with
    | single next => exact .extend (.single edge) next
    | extend _ next ih => exact .extend ih next

private theorem relevant_transfer (R : Reversal G H a b) (Q : Query G) (T : Query H)
    (left : Q.left = T.left) (right : Q.right = T.right)
    (condition : Q.condition.member = T.condition.member)
    {u : Fin n} (ru : Q.relevant u) : T.relevant u ∨ (u = a ∧ T.relevant b) := by
  obtain ⟨w, here, path⟩ := (Q.relevant_iff u).mp ru
  let Good := fun v => T.relevant v ∨ (v = a ∧ T.relevant b)
  have goodEnd : Good w := by
    rw [left, right, condition] at here
    exact .inl ((T.relevant_iff w).mpr ⟨w, here, .inl rfl⟩)
  have step : ∀ x y, G.edge x y = true → Good y → Good x := by
    intro x y edge next
    rcases next with hr | ⟨rfl, hr⟩
    · by_cases removed : x = a ∧ y = b
      · rcases removed with ⟨rfl, rfl⟩
        exact .inr ⟨rfl, hr⟩
      · exact .inl (relevant_parent (R.retained edge removed) hr)
    · exact .inl (relevant_parent (R.parent_of_old_tail edge) hr)
  rcases path with rfl | walk
  · exact goodEnd
  · suffices transfer : ∀ {x y}, G.DirectedWalk x y → Good y → Good x from
      transfer walk goodEnd
    intro x y walk
    induction walk with
    | single edge => exact step _ _ edge
    | extend _ edge ih => exact fun hy => ih (step _ _ edge hy)

private theorem moral_walk_of_connection {D : DAG n} {T : Query D} {u v : Fin n}
    (hu : T.relevant u) (hv : T.relevant v)
    (outsideU : T.condition.member u = false) (outsideV : T.condition.member v = false)
    (link : D.edge u v = true ∨ D.edge v u = true ∨
      ∃ c, T.relevant c ∧ D.edge u c = true ∧ D.edge v c = true) :
    T.MoralWalk u v := by
  by_cases same : u = v
  · subst v
    exact .nil u
  · exact .cons ⟨hu, hv, outsideU, outsideV, same, link⟩ (.nil v)

private theorem parent_of_old_head (R : Reversal G H a b) {u : Fin n}
    (edge : G.edge u b = true) (ne : u ≠ a) : H.edge u a = true :=
  R.retained ((R.parents u ne (edge_distinct edge)).mpr edge) (fun e => ne e.1)

private theorem neighbors_of_lost_tail (R : Reversal G H a b)
    {Q : Query G} {T : Query H}
    (transfer : ∀ {v}, Q.relevant v → T.relevant v ∨ (v = a ∧ T.relevant b))
    (lost : ¬ T.relevant a) {u : Fin n} (kept : T.relevant u)
    (link : Q.MoralEdge a u) : u = b ∨ H.edge u b = true := by
  rcases link.connection with edge | edge | ⟨c, rc, ac, uc⟩
  · by_cases eq : u = b
    · exact .inl eq
    · exact (lost (relevant_parent (R.retained edge (fun e => eq e.2)) kept)).elim
  · exact .inr (R.parent_of_old_tail edge)
  · by_cases eq : c = b
    · subst c
      exact .inr (R.retained uc (fun e => link.distinct e.1.symm))
    · have hc := (transfer rc).resolve_right (fun h => edge_distinct ac h.1.symm)
      exact (lost (relevant_parent (R.retained ac (fun e => eq e.2)) hc)).elim

private theorem flip_moral_edge {D : DAG n} {Q : Query D} {u v : Fin n}
    (e : Q.MoralEdge u v) : Q.MoralEdge v u := by
  refine ⟨e.targetRelevant, e.sourceRelevant, e.targetOutside, e.sourceOutside,
    e.distinct.symm, ?_⟩
  rcases e.connection with uv | vu | ⟨c, hc, uc, vc⟩
  · exact .inr (.inl uv)
  · exact .inl vu
  · exact .inr (.inr ⟨c, hc, vc, uc⟩)

private theorem moral_walk_forward (R : Reversal G H a b) (Q : Query G) (T : Query H)
    (left : Q.left = T.left) (right : Q.right = T.right)
    (condition : Q.condition.member = T.condition.member)
    (connected : Q.MoralConnection) : T.MoralConnection := by
  have transfer {v} := R.relevant_transfer Q T left right condition (u := v)
  have keptLink {u v} (hu : T.relevant u) (hv : T.relevant v) (e : Q.MoralEdge u v) :
      T.MoralWalk u v := by
    apply moral_walk_of_connection hu hv (condition ▸ e.sourceOutside) (condition ▸ e.targetOutside)
    rcases e.connection with uv | vu | ⟨c, rc, uc, vc⟩
    · by_cases removed : u = a ∧ v = b
      · obtain ⟨rfl, rfl⟩ := removed
        exact .inr (.inl R.reverse)
      · exact .inl (R.retained uv removed)
    · by_cases removed : v = a ∧ u = b
      · obtain ⟨rfl, rfl⟩ := removed
        exact .inl R.reverse
      · exact .inr (.inl (R.retained vu removed))
    · by_cases removedU : u = a ∧ c = b
      · obtain ⟨rfl, rfl⟩ := removedU
        exact .inr (.inl (R.parent_of_old_head vc e.distinct.symm))
      · by_cases removedV : v = a ∧ c = b
        · obtain ⟨rfl, rfl⟩ := removedV
          exact .inl (R.parent_of_old_head uc e.distinct)
        · rcases transfer rc with hc | ⟨rfl, hb⟩
          · exact .inr (.inr ⟨c, hc, R.retained uc removedU, R.retained vc removedV⟩)
          · exact .inr (.inr ⟨b, hb, R.parent_of_old_tail uc, R.parent_of_old_tail vc⟩)
  have skirt {z u w} (hz : T.relevant z) (notU : ¬ T.relevant u) (hw : T.relevant w)
      (enter : Q.MoralEdge z u) (leave : Q.MoralEdge u w) : T.MoralWalk z w := by
    obtain ⟨rfl, hb⟩ := (transfer leave.sourceRelevant).resolve_left notU
    by_cases same : z = w
    · subst w
      exact .nil z
    apply moral_walk_of_connection hz hw
      (condition ▸ enter.sourceOutside) (condition ▸ leave.targetOutside)
    rcases R.neighbors_of_lost_tail transfer notU hz (flip_moral_edge enter) with rfl | zb
    · rcases R.neighbors_of_lost_tail transfer notU hw leave with rfl | wb
      · exact (same rfl).elim
      · exact .inr (.inl wb)
    · rcases R.neighbors_of_lost_tail transfer notU hw leave with rfl | wb
      · exact .inl zb
      · exact .inr (.inr ⟨b, hb, zb, wb⟩)
  have append {u v w} (first : T.MoralWalk u v) (rest : T.MoralWalk v w) :
      T.MoralWalk u w := by
    induction first with
    | nil => exact rest
    | cons head _ ih => exact .cons head (ih rest)
  have liftWalk {u y} (walk : Q.MoralWalk u y) :
      T.relevant y →
      (T.relevant u → T.MoralWalk u y) ∧
      (¬ T.relevant u → ∀ {z}, T.relevant z → Q.MoralEdge z u → T.MoralWalk z y) := by
    induction walk with
    | nil => exact fun hy => ⟨fun _ => .nil _, fun no => (no hy).elim⟩
    | @cons u v _ edge _ ih =>
      intro hy
      obtain ⟨keptSuffix, lostSuffix⟩ := ih hy
      refine ⟨?_, ?_⟩
      · intro hu
        by_cases hv : T.relevant v
        · exact append (keptLink hu hv edge) (keptSuffix hv)
        · exact lostSuffix hv hu edge
      · intro no z hz enter
        have hv : T.relevant v := (transfer edge.targetRelevant).resolve_right (by
          rintro ⟨rfl, _⟩
          exact edge.distinct ((transfer edge.sourceRelevant).resolve_left no).1)
        exact append (skirt hz no hv enter edge) (keptSuffix hv)
  obtain ⟨x, y, hx, hy, path⟩ := connected
  rw [left] at hx
  rw [right] at hy
  have hyRelevant := (T.relevant_iff y).mpr ⟨y, .inr (.inl hy), .inl rfl⟩
  exact ⟨x, y, hx, hy, (liftWalk path hyRelevant).1
    ((T.relevant_iff x).mpr ⟨x, .inl hx, .inl rfl⟩)⟩

/-- A single covered reversal preserves set-valued d-connection for
queries disjoint from the conditioning set. -/
theorem dConnection_iff (R : Reversal G H a b) (Q : Query G) (T : Query H)
    (left : Q.left = T.left) (right : Q.right = T.right)
    (condition : Q.condition.member = T.condition.member)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false) :
    Q.DConnection ↔ T.DConnection := by
  have targetLeft : ∀ v, T.left v = true → T.condition.member v = false := by
    simpa only [left, condition] using leftOutside
  have targetRight : ∀ v, T.right v = true → T.condition.member v = false := by
    simpa only [right, condition] using rightOutside
  rw [Q.dConnection_iff_moralConnection leftOutside rightOutside,
    T.dConnection_iff_moralConnection targetLeft targetRight]
  exact ⟨R.moral_walk_forward Q T left right condition,
    R.symm.moral_walk_forward T Q left.symm right.symm condition.symm⟩

def flippedEdge (G : DAG n) (a b u v : Fin n) : Bool :=
  if u = b ∧ v = a then true else if u = a ∧ v = b then false else G.edge u v

def flippedRank (G : DAG n) (a b u : Fin n) : Nat :=
  if u = a then 2 * G.rank a + 1 else if u = b then 2 * G.rank a else 2 * G.rank u

/-- Reverse a covered edge and construct a new acyclicity ranking by
placing its old head just before its old tail. -/
def flip (G : DAG n) (a b : Fin n) (forward : G.edge a b = true)
    (parents : ∀ u, u ≠ a → u ≠ b → (G.edge u a = true ↔ G.edge u b = true)) : DAG n where
  edge := flippedEdge G a b
  rank := flippedRank G a b
  edge_increases u v edge := by
    have distinct := edge_distinct forward
    have rankAB := G.edge_increases _ _ forward
    by_cases reverseEdge : u = b ∧ v = a
    · rcases reverseEdge with ⟨rfl, rfl⟩
      simp [flippedRank, distinct.symm]
    · by_cases forwardEdge : u = a ∧ v = b
      · simp only [flippedEdge, ite_eq_right reverseEdge, ite_eq_left forwardEdge, Bool.false_eq_true] at edge
      · have oldEdge : G.edge u v = true := by
          simpa [flippedEdge, reverseEdge, forwardEdge] using edge
        have rankOld := G.edge_increases _ _ oldEdge
        have neq := edge_distinct oldEdge
        by_cases ua : u = a
        · subst u
          have va : v ≠ a := neq.symm
          have vb : v ≠ b := fun eq => forwardEdge ⟨rfl, eq⟩
          simp [flippedRank, va, vb]
          omega
        · by_cases ub : u = b
          · subst u
            have va : v ≠ a := fun eq => reverseEdge ⟨rfl, eq⟩
            have vb : v ≠ b := neq.symm
            simp [flippedRank, distinct.symm, va, vb]
            omega
          · by_cases va : v = a
            · subst v
              simp [flippedRank, ua, ub]
              omega
            · by_cases vb : v = b
              · subst v
                have rankNew := G.edge_increases u a ((parents u ua ub).mpr oldEdge)
                simp [flippedRank, ua, ub, distinct.symm]
                omega
              · simp [flippedRank, ua, ub, va, vb]
                omega

theorem flip_is_covered_reversal (G : DAG n) (a b : Fin n)
    (forward : G.edge a b = true)
    (parents : ∀ u, u ≠ a → u ≠ b → (G.edge u a = true ↔ G.edge u b = true)) :
    Reversal G (flip G a b forward parents) a b where
  forward := forward
  reverse := by simp [flip, flippedEdge]
  unchanged u v fwd rev := by simp [flip, flippedEdge, fwd, rev]
  parents := parents

end Reversal

end
end OpenCausalScience.Papers.Chickering1995.CoveredReversal
