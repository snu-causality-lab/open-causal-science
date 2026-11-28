module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! # Active walks with turns at conditioned vertices

Appendix A of Chickering (2002) uses walks that may repeat vertices.
Each interior occurrence is a collider exactly when its vertex is
conditioned. An ordinary active walk expands into such a walk by a
directed detour from any unconditioned collider to a conditioned
descendant and back.
-/

namespace OpenCausalScience.Papers.Chickering2002

open KimEtAl2026.BayesBall KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat} {G : DAG n}

/-- The rule is checked separately at each occurrence of a vertex. -/
def ExactTurn (condition : Fin n → Bool) (state : State (Fin n)) (next : Direction) : Prop :=
  if state.2 = .down ∧ next = .up then condition state.1 = true
  else condition state.1 = false

inductive ExactWalk (G : DAG n) (condition : Fin n → Bool) : State (Fin n) → State (Fin n) → Prop where
  | nil (u : State (Fin n)) : ExactWalk G condition u u
  | cons {u v w : State (Fin n)} : Move G u v → ExactTurn condition u v.2 →
      ExactWalk G condition v w → ExactWalk G condition u w

namespace ExactWalk

variable {condition : Fin n → Bool} {u v w : State (Fin n)}

theorem append (first : ExactWalk G condition u v) (second : ExactWalk G condition v w) :
    ExactWalk G condition u w := by
  induction first with
  | nil _ => exact second
  | cons approach turn _ ih => exact .cons approach turn (ih second)

theorem active (walk : ExactWalk G condition u v) :
    ∃ visited, ActiveWalk (Conditioning.ofPredicate G condition) u visited v := by
  induction walk with
  | nil u => exact ⟨[], .nil u⟩
  | @cons start next _ move turn _ ih =>
    obtain ⟨visited, rest⟩ := ih
    have opens : OpenTurn (Conditioning.ofPredicate G condition) start next.2 := by
      unfold ExactTurn at turn
      by_cases collider : start.2 = .down ∧ next.2 = .up
      · simp [collider] at turn
        simp [OpenTurn, collider, Conditioning.activated, Conditioning.ofPredicate, turn]
      · simpa [OpenTurn, collider, Conditioning.ofPredicate] using turn
    exact ⟨next.1 :: visited, .cons ⟨move, opens⟩ rest⟩

theorem dConnected {source target : Fin n} {arrival : Direction}
    (outsideSource : condition source = false) (outsideTarget : condition target = false)
    (walk : ExactWalk G condition (source, .up) (target, arrival)) :
    DConnected (Conditioning.ofPredicate G condition) source target := by
  let C := Conditioning.ofPredicate G condition
  apply (corrected_reachable_iff_dconnected C outsideSource outsideTarget).mp
  exact ⟨arrival, (corrected_reachable_iff_active_walk C).mpr walk.active⟩

private theorem directed_first {a b : Fin n} (walk : G.DirectedWalk a b) :
    ∃ c, G.edge a c = true ∧ (c = b ∨ G.DirectedWalk c b) := by
  induction walk with
  | single arrow => exact ⟨_, arrow, .inl rfl⟩
  | extend _ arrow ih =>
    obtain ⟨c, first, rfl | tail⟩ := ih
    · exact ⟨_, first, .inr (.single arrow)⟩
    · exact ⟨_, first, .inr (.extend tail arrow)⟩

private theorem detour {v w : Fin n} (walk : G.DirectedWalk v w)
    (outside : condition v = false) (inside : condition w = true) :
    ExactWalk G condition (v, .down) (v, .up) := by
  obtain ⟨p, first, rest⟩ := directed_first walk
  refine .cons (v := (p, .down)) first (by simpa [ExactTurn] using outside) ?_
  cases chosen : condition p with
  | true =>
    exact .cons (v := (v, .up)) first (by simpa [ExactTurn] using chosen) (.nil _)
  | false =>
    rcases rest with same | onward
    · exact (Bool.false_ne_true (chosen.symm.trans (same ▸ inside))).elim
    · exact (detour onward chosen inside).append
        (.cons (v := (v, .up)) first (by simpa [ExactTurn] using chosen) (.nil _))
termination_by G.rank w - G.rank v
decreasing_by
  have firstRank := G.edge_increases _ _ first
  have tailRank := G.rank_lt_of_directedWalk onward
  omega

theorem of_active {visited : List (Fin n)}
    (walk : ActiveWalk (Conditioning.ofPredicate G condition) u visited v) :
    ExactWalk G condition u v := by
  induction walk with
  | nil state => exact .nil state
  | @cons start next _ _ step _ ih =>
    by_cases collider : start.2 = .down ∧ next.2 = .up
    · cases member : condition start.1 with
      | true => exact .cons step.1 (by simp [ExactTurn, collider, member]) ih
      | false =>
        have selected : (Conditioning.ofPredicate G condition).descendantHit start.1 = true := by
          have turn := step.2
          simpa [OpenTurn, collider, Conditioning.activated, Conditioning.ofPredicate, member] using turn
        obtain ⟨w, inside, directed⟩ :=
          ((Conditioning.ofPredicate G condition).descendant_spec start.1).mp selected
        have excursion := detour directed member inside
        have front : ExactWalk G condition start (start.1, .up) := by
          obtain ⟨_, arrival⟩ := start
          cases collider.1
          exact excursion
        exact front.append (.cons step.1 (by simp [ExactTurn, member]) ih)
    · exact .cons step.1 (by simpa [ExactTurn, OpenTurn, collider, Conditioning.ofPredicate] using step.2) ih

/-- The expanded paths and ordinary d-connection agree. -/
theorem exists_iff_dConnected {source target : Fin n}
    (outsideSource : condition source = false) (outsideTarget : condition target = false) :
    (∃ arrival, ExactWalk G condition (source, .up) (target, arrival)) ↔
      DConnected (Conditioning.ofPredicate G condition) source target := by
  constructor
  · rintro ⟨_, route⟩
    exact route.dConnected outsideSource outsideTarget
  · rintro ⟨_, _, _, arrival, route, _⟩
    exact ⟨arrival, of_active route⟩

/-- At an unconditioned junction, one outgoing incident arrow suffices
for concatenation. This is the oriented junction rule of Lemma 21. -/
theorem append_at_open_vertex {source next : State (Fin n)} {joint : Fin n} {arrival : Direction}
    (off : condition joint = false) (usable : arrival = .up ∨ next.2 = .down)
    (first : ExactWalk G condition source (joint, arrival))
    (step : Move G (joint, arrival) next) (rest : ExactWalk G condition next v) :
    ExactWalk G condition source v := by
  have turn : ExactTurn condition (joint, arrival) next.2 := by
    rcases usable with enters | leaves
    · simp [ExactTurn, enters, off]
    · simp [ExactTurn, leaves, off]
  exact first.append (.cons step turn rest)

/-- The first outgoing arrow may start at the ordinary endpoint state. -/
theorem restart {u v : State (Fin n)} (off : condition u.1 = false)
    (path : ExactWalk G condition u v) :
    ∃ arrival, ExactWalk G condition (u.1, .up) (v.1, arrival) := by
  cases path with
  | nil _ => exact ⟨.up, .nil _⟩
  | cons step _ rest => exact ⟨_, .cons step (by simp [ExactTurn, off]) rest⟩

theorem ordinary_connection {u v : State (Fin n)}
    (offU : condition u.1 = false) (offV : condition v.1 = false)
    (path : ExactWalk G condition u v) :
    DConnected (Conditioning.ofPredicate G condition) u.1 v.1 :=
  (exists_iff_dConnected offU offV).mp (path.restart offU)

theorem start_outside_of_up {u v : State (Fin n)} (up : u.2 = .up)
    (offV : condition v.1 = false) (path : ExactWalk G condition u v) :
    condition u.1 = false := by
  cases path with
  | nil _ => exact offV
  | cons _ turn _ => simpa [ExactTurn, up] using turn

theorem trivial_or_last {u v : State (Fin n)} (path : ExactWalk G condition u v) :
    u = v ∨ ∃ near, ExactWalk G condition u near ∧ Move G near v ∧ ExactTurn condition near v.2 := by
  induction path with
  | nil _ => exact .inl rfl
  | cons step turn _ ih =>
    rcases ih with rfl | ⟨near, prefixWalk, edge, perm⟩
    · exact .inr ⟨_, .nil _, step, turn⟩
    · exact .inr ⟨near, .cons step turn prefixWalk, edge, perm⟩

end ExactWalk

end

end OpenCausalScience.Papers.Chickering2002
