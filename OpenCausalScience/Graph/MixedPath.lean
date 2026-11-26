module
public import OpenCausalScience.Graph.MixedGraph

/-! # Active walks and paths in mixed graphs

An active walk may revisit a vertex with a different incoming mark. When a
loop is removed, the turn at the common vertex still satisfies the collider
and noncollider rules. The proof uses the ancestral graph restriction on
undirected edges. It admits distinct directed and bidirected edges between
the same vertices.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {conditioning : Fin n → Bool}

/-- An active marked walk records the vertices after its initial state.
The last vertex has no turn to test. -/
inductive ActiveWalk (G : MixedGraph n) (conditioning : Fin n → Bool) :
    Arrival n → List (Fin n) → Arrival n → Prop where
  | nil (state : Arrival n) : ActiveWalk G conditioning state [] state
  | cons {start next final : Arrival n} {visited : List (Fin n)} :
      G.Step conditioning start next → ActiveWalk G conditioning next visited final →
      ActiveWalk G conditioning start (next.1 :: visited) final

private theorem ActiveWalk.snoc {start before next : Arrival n} {visited : List (Fin n)}
    (walk : G.ActiveWalk conditioning start visited before) (step : G.Step conditioning before next) :
    G.ActiveWalk conditioning start (visited ++ [next.1]) next := by
  induction walk with
  | nil => exact .cons step (.nil _)
  | cons move _ ih => exact .cons move (ih step)

private theorem ActiveWalk.reachable_from {origin start final : Arrival n}
    {visited : List (Fin n)} (walk : G.ActiveWalk conditioning start visited final)
    (base : Reach (G.Step conditioning) origin start) : Reach (G.Step conditioning) origin final := by
  induction walk with
  | nil => exact base
  | cons move _ ih => exact ih (.extend base move)

theorem reachable_iff_active_walk {start final : Arrival n} :
    Reach (G.Step conditioning) start final ↔ ∃ visited, G.ActiveWalk conditioning start visited final := by
  constructor
  · intro reached
    induction reached with
    | refl => exact ⟨[], .nil _⟩
    | extend _ step ih =>
      obtain ⟨visited, walk⟩ := ih
      exact ⟨visited ++ [_], walk.snoc step⟩
  · rintro ⟨_, walk⟩
    exact walk.reachable_from (.refl _)

private theorem inactive_head_stays_inactive_head {start final : Arrival n}
    {visited : List (Fin n)} (walk : G.ActiveWalk conditioning start visited final)
    (head : start.2 = true) (inactive : ¬ G.AncestorOf conditioning start.1)
    (incident : ∃ w mark, G.edge start.1 true w mark = true) :
    final.2 = true ∧ ¬ G.AncestorOf conditioning final.1 := by
  induction walk with
  | nil => exact ⟨head, inactive⟩
  | @cons start next _ _ move _ ih =>
    obtain ⟨outgoing, edge, turn⟩ := move
    have tail : outgoing = false := by
      cases outgoing with
      | false => rfl
      | true => exact (inactive (by simpa [openTurn, head] using turn)).elim
    have nextHead : next.2 = true := by
      cases arrival : next.2 with
      | true => rfl
      | false =>
        have undirected : G.edge start.1 false next.1 false = true := by
          simpa [tail, arrival] using edge
        obtain ⟨w, mark, arrow⟩ := incident
        rw [G.no_arrow_of_undirected undirected] at arrow
        contradiction
    have directed : G.edge start.1 false next.1 true = true := by
      simpa [tail, nextHead] using edge
    have nextInactive : ¬ G.AncestorOf conditioning next.1 :=
      fun activated => inactive (.parent directed activated)
    have nextIncident : ∃ w mark, G.edge next.1 true w mark = true :=
      ⟨start.1, false, (G.symmetric _ _ _ _).symm.trans directed⟩
    exact ih nextHead nextInactive nextIncident

private theorem ActiveWalk.split_at_visit {start final : Arrival n}
    {visited : List (Fin n)} {u : Fin n} (walk : G.ActiveWalk conditioning start visited final)
    (visit : u ∈ visited) :
    ∃ front middle suffix, visited = front ++ u :: suffix ∧
      G.ActiveWalk conditioning start (front ++ [u]) middle ∧ middle.1 = u ∧
      G.ActiveWalk conditioning middle suffix final := by
  induction walk with
  | nil => simp at visit
  | @cons start next final rest step tail ih =>
    rcases List.mem_cons.mp visit with same | later
    · subst u
      exact ⟨[], next, rest, rfl, .cons step (.nil _), rfl, tail⟩
    · obtain ⟨front, middle, suffix, split, first, same, last⟩ := ih later
      exact ⟨next.1 :: front, middle, suffix, congrArg (next.1 :: ·) split,
        .cons step first, same, last⟩

private theorem ActiveWalk.first_open_if_tail {start final : Arrival n}
    {visited : List (Fin n)} (walk : G.ActiveWalk conditioning start visited final)
    (nonempty : visited ≠ []) (tail : start.2 = false) : conditioning start.1 = false := by
  cases walk with
  | nil => exact (nonempty rfl).elim
  | cons step _ =>
    obtain ⟨outgoing, _, turn⟩ := step
    simpa [openTurn, tail] using turn

/-- Return to the earlier arrival and take the later departure. If that
would create a collider, either the common vertex is already activated or
the removed segment has a directed arrival at every vertex, including at
its last one. -/
private theorem rebase_step {start middle next : Arrival n} {visited : List (Fin n)}
    (front : G.ActiveWalk conditioning start visited middle) (nonempty : visited ≠ [])
    (same : middle.1 = start.1) (departure : G.Step conditioning middle next) :
    G.Step conditioning start next := by
  classical
  obtain ⟨outgoing, edge, turn⟩ := departure
  have moved : G.edge start.1 outgoing next.1 next.2 = true := by
    simpa [same] using edge
  refine ⟨outgoing, moved, ?_⟩
  cases head : start.2 with
  | false =>
    simpa [openTurn, head] using front.first_open_if_tail nonempty head
  | true =>
    cases leaves : outgoing with
    | false =>
      have allowed : conditioning start.1 = false := by
        simpa [openTurn, leaves, same] using turn
      simpa [openTurn, leaves] using allowed
    | true =>
      have activated : G.AncestorOf conditioning start.1 := by
        by_cases active : G.AncestorOf conditioning start.1
        · exact active
        · have incident : ∃ w mark, G.edge start.1 true w mark = true :=
            ⟨next.1, next.2, by simpa [leaves] using moved⟩
          have middleHead := (inactive_head_stays_inactive_head front head active incident).1
          simpa [openTurn, middleHead, leaves, same] using turn
      simpa [openTurn, head, leaves] using activated

private theorem drop_repeated_start {start final : Arrival n} {visited : List (Fin n)}
    (walk : G.ActiveWalk conditioning start visited final) (reappears : start.1 ∈ visited) :
    ∃ shorter last, G.ActiveWalk conditioning start shorter last ∧ last.1 = final.1 ∧
      shorter.length < visited.length ∧ ∀ u ∈ shorter, u ∈ visited := by
  obtain ⟨front, middle, suffix, split, first, same, last⟩ := walk.split_at_visit reappears
  have small : suffix.length < visited.length := by simp [split]; omega
  have subset : ∀ u ∈ suffix, u ∈ visited := by
    intro u mem
    simp [split, List.mem_append, List.mem_cons, mem]
  cases last with
  | nil => exact ⟨[], start, .nil _, same.symm, small, subset⟩
  | cons step tail =>
    have nonempty : front ++ [start.1] ≠ [] := by simp
    exact ⟨_, _, .cons (rebase_step first nonempty same step) tail, rfl, small, subset⟩

/-- An active mixed walk has a vertex-simple active path with the same
endpoints. Only vertices of the original walk are used. -/
theorem ActiveWalk.to_simple {start final : Arrival n} {visited : List (Fin n)}
    (walk : G.ActiveWalk conditioning start visited final) :
    ∃ shorter last, G.ActiveWalk conditioning start shorter last ∧ last.1 = final.1 ∧
      (start.1 :: shorter).Nodup ∧ ∀ u ∈ shorter, u ∈ visited := by
  induction size : visited.length using Nat.strongRecOn generalizing visited start final with
  | ind lengthBound ih =>
    by_cases reappears : start.1 ∈ visited
    · obtain ⟨shorter, mid, erased, endpoint, small, subset⟩ :=
        drop_repeated_start walk reappears
      obtain ⟨path, last, simple, same, nodup, subpath⟩ :=
        ih shorter.length (size ▸ small) erased rfl
      exact ⟨path, last, simple, same.trans endpoint, nodup, fun u mem => subset u (subpath u mem)⟩
    · cases walk with
      | nil => exact ⟨[], start, .nil _, rfl, by simp, fun _ h => by cases h⟩
      | @cons start next final rest move suffix =>
        have small : rest.length < lengthBound := by simp at size; omega
        obtain ⟨path, last, simple, same, nodup, subpath⟩ := ih rest.length small suffix rfl
        have subset : ∀ u ∈ next.1 :: path, u ∈ next.1 :: rest := by
          intro u mem
          rcases List.mem_cons.mp mem with head | tail
          · exact List.mem_cons.mpr (.inl head)
          · exact List.mem_cons.mpr (.inr (subpath _ tail))
        exact ⟨next.1 :: path, last, .cons move simple, same,
          List.nodup_cons.mpr ⟨fun h => reappears (subset _ h), nodup⟩, subset⟩

/-- A vertex-simple active path between the query sets. The first edge is
explicit and every interior turn is checked with its chosen endpoint marks. -/
def PathConnected (G : MixedGraph n) (left right conditioning : Fin n → Bool) : Prop :=
  ∃ source outgoing first visited last,
    left source = true ∧ G.edge source outgoing first.1 first.2 = true ∧
    G.ActiveWalk conditioning first visited last ∧ right last.1 = true ∧
    (source :: first.1 :: visited).Nodup

theorem walkConnected_iff_pathConnected (G : MixedGraph n) (left right conditioning : Fin n → Bool)
    (leftOutside : ∀ v, left v = true → conditioning v = false)
    (leftRightDisjoint : ∀ v, left v = true → right v = false) :
    G.WalkConnected left right conditioning ↔ G.PathConnected left right conditioning := by
  constructor
  · rintro ⟨first, last, ⟨source, outgoing, memLeft, edge⟩, reached, memRight⟩
    obtain ⟨visited, walk⟩ := reachable_iff_active_walk.mp reached
    have firstStep : G.Step conditioning (source, false) first :=
      ⟨outgoing, edge, by simpa [openTurn] using leftOutside source memLeft⟩
    obtain ⟨_, last', simple, same, nodup, _⟩ := (ActiveWalk.cons firstStep walk).to_simple
    have right' : right last'.1 = true := by simpa [same] using memRight
    cases simple with
    | nil =>
      have notRight := leftRightDisjoint source memLeft
      simp [notRight] at right'
    | cons move tail =>
      obtain ⟨outgoing, edge, _⟩ := move
      exact ⟨source, outgoing, _, _, _, memLeft, edge, tail, right', nodup⟩
  · rintro ⟨source, outgoing, first, visited, last, memLeft, edge, walk, memRight, _⟩
    exact ⟨first, last, ⟨source, outgoing, memLeft, edge⟩,
      reachable_iff_active_walk.mpr ⟨visited, walk⟩, memRight⟩

end

end OpenCausalScience.MixedGraph
