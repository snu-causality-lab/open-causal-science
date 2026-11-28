module
public import OpenCausalScience.Papers.Chickering2002.ExactActiveWalk
public import OpenCausalScience.Papers.Chickering2002.InclusionStructure

/-! # The endpoint segments after inserting an arrow

Lemma 22 of Chickering (2002). A connection introduced by an insertion
has original-graph segments up to the first use of the inserted arrow and
after its last use. A conditioned head is bypassed by using a parent.
-/

namespace OpenCausalScience.Papers.Chickering2002

open KimEtAl2026.BayesBall KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G D : DAG n}

abbrev Connected (G : DAG n) (C : Fin n → Bool) := DConnected (Conditioning.ofPredicate G C)

private def NewMove (x y : Fin n) (u v : State (Fin n)) : Prop :=
  (u.1 = x ∧ v.1 = y ∧ v.2 = .down) ∨ (u.1 = y ∧ v.1 = x ∧ v.2 = .up)

private theorem move_in_inserted_graph {x y : Fin n} (edit : G.IsInsertion D x y)
    {u v : State (Fin n)} (step : Move D u v) :
    Move G u v ∨ NewMove x y u v := by
  cases direction : v.2 with
  | down =>
    have arrow : D.edge u.1 v.1 = true := by simpa [Move, direction] using step
    rcases (edit _ _).mp arrow with old | ⟨source, target⟩
    · exact .inl (by simpa [Move, direction] using old)
    · exact .inr (.inl ⟨source, target, direction⟩)
  | up =>
    have arrow : D.edge v.1 u.1 = true := by simpa [Move, direction] using step
    rcases (edit _ _).mp arrow with old | ⟨source, target⟩
    · exact .inl (by simpa [Move, direction] using old)
    · exact .inr (.inr ⟨target, source, direction⟩)

private theorem split_first_last {x y : Fin n} (edit : G.IsInsertion D x y)
    {C : Fin n → Bool} {a b : State (Fin n)} (walk : ExactWalk D C a b) :
    ExactWalk G C a b ∨
    ∃ u v p q : State (Fin n),
      ExactWalk G C a u ∧ NewMove x y u v ∧ ExactTurn C u v.2 ∧
        NewMove x y p q ∧ ExactTurn C p q.2 ∧ ExactWalk G C q b := by
  induction walk with
  | nil _ => exact .inl (.nil _)
  | @cons a s b step turn rest ih =>
    rcases move_in_inserted_graph edit step with old | inserted
    · rcases ih with whole | ⟨u, v, p, q, first, uv, turnUV, pq, turnPQ, last⟩
      · exact .inl (.cons old turn whole)
      · exact .inr ⟨u, v, p, q, .cons old turn first, uv, turnUV, pq, turnPQ, last⟩
    · rcases ih with whole | ⟨_, _, p, q, _, _, _, pq, turnPQ, last⟩
      · exact .inr ⟨a, s, a, s, .nil _, inserted, turn, inserted, turn, whole⟩
      · exact .inr ⟨a, s, p, q, .nil _, inserted, turn, pq, turnPQ, last⟩

/-- A segment can meet the inserted arrow at its tail, at its unconditioned
head, or at an original unconditioned parent of its conditioned head. -/
def InsertionSegmentEnd (G : DAG n) (C : Fin n → Bool) (x y u : Fin n) : Prop :=
  u = x ∨ if C y then G.edge u y = true else u = y

private theorem after_head {C : Fin n → Bool} {x y b : Fin n} {arrival : Direction}
    (offB : C b = false) (walk : ExactWalk G C (y, .down) (b, arrival)) :
    ∃ v, InsertionSegmentEnd G C x y v ∧ Connected G C v b := by
  cases member : C y with
  | false =>
    exact ⟨y, .inr (by simp [member]), walk.ordinary_connection member offB⟩
  | true =>
    cases walk with
    | nil => exact (Bool.false_ne_true (offB.symm.trans member)).elim
    | @cons _ next _ step turn rest =>
      have up : next.2 = .up := by
        cases h : next.2 <;> simp_all [ExactTurn]
      have arrow : G.edge next.1 y = true := by simpa [Move, up] using step
      have offNext := rest.start_outside_of_up up offB
      exact ⟨next.1, .inr (by simp [member, arrow]), rest.ordinary_connection offNext offB⟩

private theorem before_head {C : Fin n → Bool} {x y a : Fin n} {arrival : Direction}
    (offA : C a = false) (turn : ExactTurn C (y, arrival) .up)
    (walk : ExactWalk G C (a, .up) (y, arrival)) :
    ∃ u, InsertionSegmentEnd G C x y u ∧ Connected G C a u := by
  cases member : C y with
  | false =>
    exact ⟨y, .inr (by simp [member]), walk.dConnected offA member⟩
  | true =>
    have down : arrival = .down := by
      cases arrival <;> simp_all [ExactTurn]
    subst arrival
    rcases walk.trivial_or_last with equal | ⟨near, first, edge, checked⟩
    · have awful := congrArg Prod.snd equal
      cases awful
    · have arrow : G.edge near.1 y = true := edge
      have offNear : C near.1 = false := by simpa [ExactTurn] using checked
      exact ⟨near.1, .inr (by simp [member, arrow]), first.ordinary_connection offA offNear⟩

/-- Either the connection already existed or the two original-graph
segments have the endpoints described in Lemma 22. At least one segment
ends at the tail of the inserted arrow. -/
theorem insertion_connection_split {x y a b : Fin n} (edit : G.IsInsertion D x y)
    (C : Fin n → Bool) (connection : Connected D C a b) :
    Connected G C a b ∨ ∃ u v, InsertionSegmentEnd G C x y u ∧
      InsertionSegmentEnd G C x y v ∧ (u = x ∨ v = x) ∧
      Connected G C a u ∧ Connected G C v b := by
  obtain ⟨offA, offB, _, last, oldActive, _⟩ := connection
  have expanded := ExactWalk.of_active oldActive
  rcases split_first_last edit expanded with unchanged | ⟨u, v, p, q, first, uv, uvTurn, pq, _, suffix⟩
  · exact .inl (unchanged.dConnected offA offB)
  rcases u with ⟨u, uDir⟩
  rcases v with ⟨v, vDir⟩
  rcases p with ⟨p, pDir⟩
  rcases q with ⟨q, qDir⟩
  simp only [NewMove] at uv pq
  rcases uv with ⟨ux, vy, vDown⟩ | ⟨uy, vx, vUp⟩
  · subst u
    subst v
    subst vDir
    have offX : C x = false := by simpa [ExactTurn] using uvTurn
    have left := first.dConnected offA offX
    rcases pq with ⟨px, qy, qDown⟩ | ⟨py, qx, qUp⟩
    · subst p
      subst q
      subst qDir
      obtain ⟨target, hv, right⟩ := after_head (x := x) offB suffix
      exact .inr ⟨x, target, .inl rfl, hv, .inl rfl, left, right⟩
    · subst p
      subst q
      subst qDir
      exact .inr ⟨x, x, .inl rfl, .inl rfl, .inl rfl, left, suffix.dConnected offX offB⟩
  · subst u
    subst v
    subst vDir
    rcases pq with ⟨px, qy, qDown⟩ | ⟨py, qx, qUp⟩
    · subst p
      subst q
      subst qDir
      cases uDir with
      | down => exact .inl ((first.append suffix).dConnected offA offB)
      | up =>
        have offY : C y = false := by simpa [ExactTurn] using uvTurn
        obtain ⟨arrival, restarted⟩ := suffix.restart offY
        exact .inl ((first.append restarted).dConnected offA offB)
    · subst p
      subst q
      subst qDir
      obtain ⟨source, hu, left⟩ := before_head (x := x) offA uvTurn first
      have offX := suffix.start_outside_of_up rfl offB
      exact .inr ⟨source, x, hu, .inl rfl, .inr rfl, left, suffix.dConnected offX offB⟩

end

end OpenCausalScience.Papers.Chickering2002
