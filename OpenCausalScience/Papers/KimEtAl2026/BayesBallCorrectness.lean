module
public import OpenCausalScience.Graph.DAG
public import OpenCausalScience.Papers.KimEtAl2026.BayesBall

/-! # Corrected Bayes-ball on finite DAGs

[Kim et al., corrected version](https://www.sanghacklee.me/ai-corrected/CRL_internal_auxiliaries_AI_corrected_2026-10-15.pdf),
Appendix C, Algorithm 2, lines 5–33. A downward arrival means that the last
arrow pointed into the current vertex. The conditioning test is separated
from the observed-vertex filter applied to the answer. A rank-recursive
descendant test implements nonempty directed reachability. The FIFO search
expands each directional state at most once and returns the seeds together
with the unobserved, unconditioned vertices d-connected to a seed.
-/

namespace OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

open OpenCausalScience
open BayesBall

@[expose] public section

variable {n : Nat}

structure Conditioning (G : DAG n) where
  member : Fin n → Bool
  descendantHit : Fin n → Bool
  descendant_spec : ∀ u, descendantHit u = true ↔
    ∃ w, member w = true ∧ G.DirectedWalk u w

def Conditioning.activated {G : DAG n} (C : Conditioning G) (u : Fin n) : Bool :=
  C.member u || C.descendantHit u

def parents (G : DAG n) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun p => G.edge p u

/-- Test nonempty directed reachability by searching backward through
vertices of strictly smaller rank. -/
def hasDirectedWalk (G : DAG n) (source target : Fin n) : Bool :=
  G.edge source target || (parents G target).attach.any fun parent =>
    have _incoming : G.edge parent.1 target = true := (List.mem_filter.mp parent.2).2
    hasDirectedWalk G source parent.1
termination_by G.rank target
decreasing_by exact G.edge_increases _ _ _incoming

theorem hasDirectedWalk_iff (G : DAG n) (source target : Fin n) :
    hasDirectedWalk G source target = true ↔ G.DirectedWalk source target := by
  constructor
  · intro test
    induction rankEq : G.rank target using Nat.strongRecOn generalizing target with
    | ind rankBound ih =>
      rw [hasDirectedWalk, Bool.or_eq_true_iff] at test
      rcases test with edge | viaParent
      · exact .single edge
      · obtain ⟨parent, _, found⟩ := List.any_eq_true.mp viaParent
        have edge : G.edge parent.1 target = true := (List.mem_filter.mp parent.2).2
        have smaller : G.rank parent.1 < rankBound :=
          rankEq ▸ G.edge_increases _ _ edge
        exact .extend (ih (G.rank parent.1) smaller parent.1 found rfl) edge
  · intro walk
    induction walk with
    | single edge => rw [hasDirectedWalk]; simp [edge]
    | @extend p target _ incoming ih =>
      let parent : {p // p ∈ parents G target} :=
        ⟨p, List.mem_filter.mpr ⟨List.mem_finRange _, incoming⟩⟩
      rw [hasDirectedWalk, Bool.or_eq_true_iff]
      exact Or.inr (List.any_eq_true.mpr ⟨parent, List.mem_attach _ _, ih⟩)

def Conditioning.ofPredicate (G : DAG n) (member : Fin n → Bool) : Conditioning G where
  member := member
  descendantHit := fun u =>
    (List.finRange n).any fun w => member w && hasDirectedWalk G u w
  descendant_spec := by
    intro u
    simp [List.any_eq_true, hasDirectedWalk_iff]

def neighborhood (G : DAG n) (C : Conditioning G) : Neighborhood (Fin n) where
  parents := parents G
  children := fun u => (List.finRange n).filter fun c => G.edge u c
  conditioned := C.member
  hasConditionedDescendant := C.descendantHit

/-- The two consecutive arrows meet head-to-head when the arrival is down
and the departure is up. This is the usual collider rule along a walk. -/
def OpenTurn {G : DAG n} (C : Conditioning G) (state : State (Fin n))
    (outgoing : Direction) : Prop :=
  if state.2 = .down ∧ outgoing = .up then
    C.activated state.1 = true
  else
    C.member state.1 = false

def Move (G : DAG n) (current next : State (Fin n)) : Prop :=
  match next.2 with
  | .up => G.edge next.1 current.1 = true
  | .down => G.edge current.1 next.1 = true

def ActiveStep {G : DAG n} (C : Conditioning G) (current next : State (Fin n)) : Prop :=
  Move G current next ∧ OpenTurn C current next.2

theorem corrected_transition_iff_active_step {G : DAG n} (C : Conditioning G)
    (current next : State (Fin n)) :
    next ∈ nextStates (neighborhood G C) true current ↔ ActiveStep C current next := by
  rcases current with ⟨u, arrival⟩
  rcases next with ⟨v, departure⟩
  cases hc : C.member u <;> cases hd : C.descendantHit u <;>
    cases arrival <;> cases departure <;>
    simp [nextStates, neighborhood, parents, parentStates, childStates, List.mem_map, ActiveStep,
      Move, OpenTurn, Conditioning.activated, hc, hd]

/-- An active walk records the vertices visited after the starting state.
Upward initial state at an unconditioned endpoint permits either first
edge orientation. The final vertex has no turn to test. -/
inductive ActiveWalk {G : DAG n} (C : Conditioning G) :
    State (Fin n) → List (Fin n) → State (Fin n) → Prop where
  | nil (state : State (Fin n)) : ActiveWalk C state [] state
  | cons {start next final : State (Fin n)} {visited : List (Fin n)} :
    ActiveStep C start next → ActiveWalk C next visited final →
    ActiveWalk C start (next.1 :: visited) final

private theorem ActiveWalk.snoc {G : DAG n} {C : Conditioning G}
    {start before next : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited before) (step : ActiveStep C before next) :
    ActiveWalk C start (visited ++ [next.1]) next := by
  induction walk with
  | nil state => exact .cons step (.nil _)
  | cons move _ ih => exact .cons move (ih step)

private theorem ActiveWalk.reachable_from {G : DAG n} {C : Conditioning G}
    {origin start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final)
    (base : Reachable (nextStates (neighborhood G C) true) origin start) :
    Reachable (nextStates (neighborhood G C) true) origin final := by
  induction walk with
  | nil => exact base
  | cons move _ ih =>
    exact ih (.step base ((corrected_transition_iff_active_step C _ _).mpr move))

theorem corrected_reachable_iff_active_walk {G : DAG n} (C : Conditioning G)
    {start final : State (Fin n)} :
    Reachable (nextStates (neighborhood G C) true) start final ↔
      ∃ visited, ActiveWalk C start visited final := by
  constructor
  · intro reached
    induction reached with
    | start => exact ⟨[], .nil _⟩
    | step _ move ih =>
      obtain ⟨visited, walk⟩ := ih
      exact ⟨_, walk.snoc ((corrected_transition_iff_active_step C _ _).mp move)⟩
  · rintro ⟨_, walk⟩
    exact walk.reachable_from .start

private theorem directedWalk_prepend {G : DAG n} {u v w : Fin n}
    (edge : G.edge u v = true) (walk : G.DirectedWalk v w) :
    G.DirectedWalk u w := by
  induction walk with
  | single last => exact .extend (.single edge) last
  | extend _ last ih => exact .extend ih last

private theorem activation_precedes {G : DAG n} {C : Conditioning G} {u v : Fin n}
    (edge : G.edge u v = true) (active : C.activated v = true) :
    C.activated u = true := by
  have hit : C.descendantHit u = true := by
    apply (C.descendant_spec u).mpr
    have split : C.member v = true ∨ C.descendantHit v = true := by
      simpa [Conditioning.activated] using active
    rcases split with here | below
    · exact ⟨v, here, .single edge⟩
    · obtain ⟨w, conditioned, path⟩ := (C.descendant_spec v).mp below
      exact ⟨w, conditioned, directedWalk_prepend edge path⟩
  simp [Conditioning.activated, hit]

private theorem inactive_down_stays_inactive_down {G : DAG n} {C : Conditioning G}
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final)
    (down : start.2 = .down) (inactive : C.activated start.1 = false) :
    final.2 = .down ∧ C.activated final.1 = false := by
  induction walk with
  | nil => exact ⟨down, inactive⟩
  | @cons start next _ _ move _ ih =>
    have nextDown : next.2 = .down := by
      cases nextDir : next.2 with
      | down => rfl
      | up =>
        have turn := move.2
        simp [OpenTurn, down, nextDir, inactive] at turn
    have edge : G.edge start.1 next.1 = true := by
      simpa [Move, nextDown] using move.1
    apply ih nextDown
    cases active : C.activated next.1 with
    | false => rfl
    | true =>
      have contradiction := activation_precedes edge active
      simp [inactive] at contradiction

private theorem ActiveWalk.split_at_visit {G : DAG n} {C : Conditioning G}
    {start final : State (Fin n)} {visited : List (Fin n)} {u : Fin n}
    (walk : ActiveWalk C start visited final) (visit : u ∈ visited) :
    ∃ front middle suffix,
      visited = front ++ u :: suffix ∧
      ActiveWalk C start (front ++ [u]) middle ∧ middle.1 = u ∧
      ActiveWalk C middle suffix final := by
  induction walk with
  | nil => simp at visit
  | @cons start next final rest step tail ih =>
    rcases List.mem_cons.mp visit with same | later
    · subst u
      exact ⟨[], next, rest, rfl, .cons step (.nil _), rfl, tail⟩
    · obtain ⟨front, middle, suffix, split, first, same, last⟩ := ih later
      exact ⟨next.1 :: front, middle, suffix, congrArg (next.1 :: ·) split,
        .cons step first, same, last⟩

private theorem ActiveWalk.first_open_if_up {G : DAG n} {C : Conditioning G}
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final)
    (nonempty : visited ≠ []) (up : start.2 = .up) : C.member start.1 = false := by
  cases walk with
  | nil => exact (nonempty rfl).elim
  | cons step _ => simpa [OpenTurn, up] using step.2

/-- Replace the incoming arrival of the suffix by the earlier arrival at its
vertex. The only possible new collider needs activation. If the earlier
arrival was down at an inactive vertex, no continuation could have switched
to up, so the earlier and later arrivals would both have been down. -/
private theorem rebase_step {G : DAG n} {C : Conditioning G}
    {start middle next : State (Fin n)} {visited : List (Fin n)}
    (front : ActiveWalk C start visited middle) (nonempty : visited ≠ [])
    (same : middle.1 = start.1) (departure : ActiveStep C middle next) :
    ActiveStep C start next := by
  have move : Move G start next := by
    unfold Move at *
    rw [← same]
    exact departure.1
  refine ⟨move, ?_⟩
  by_cases arrival : start.2 = middle.2
  · simpa [OpenTurn, same, ← arrival] using departure.2
  cases startDir : start.2 with
  | up =>
    simp [OpenTurn, startDir, front.first_open_if_up nonempty startDir]
  | down =>
    have middleDir : middle.2 = .up := by
      cases h : middle.2 with
      | up => rfl
      | down => exact (arrival (startDir.trans h.symm)).elim
    have active : C.activated start.1 = true := by
      cases h : C.activated start.1 with
      | true => rfl
      | false =>
        have endDown := (inactive_down_stays_inactive_down front startDir h).1
        exact (arrival (startDir.trans endDown.symm)).elim
    have unconditioned : C.member start.1 = false := by
      simpa [OpenTurn, middleDir, same] using departure.2
    cases next.2 <;> simp [OpenTurn, startDir, active, unconditioned]

private theorem drop_repeated_start {G : DAG n} {C : Conditioning G}
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final) (reappears : start.1 ∈ visited) :
    ∃ shorter last, ActiveWalk C start shorter last ∧ last.1 = final.1 ∧
      shorter.length < visited.length ∧ ∀ u ∈ shorter, u ∈ visited := by
  obtain ⟨front, middle, suffix, split, first, same, last⟩ :=
    walk.split_at_visit reappears
  have small : suffix.length < visited.length := by simp [split]; omega
  have subset : ∀ u ∈ suffix, u ∈ visited := by
    intro u mem
    simp [split, List.mem_append, List.mem_cons, mem]
  cases last with
  | nil => exact ⟨[], start, .nil _, same.symm, small, subset⟩
  | cons step tail =>
    have nonempty : front ++ [start.1] ≠ [] := by simp
    exact ⟨_, _, .cons (rebase_step first nonempty same step) tail, rfl, small, subset⟩

/-- Loop erasure for active DAG walks preserves the two endpoints. The result
also preserves the starting arrival and uses only vertices on the walk. -/
theorem ActiveWalk.to_simple {G : DAG n} {C : Conditioning G}
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final) :
    ∃ shorter last, ActiveWalk C start shorter last ∧ last.1 = final.1 ∧
      (start.1 :: shorter).Nodup ∧ ∀ u ∈ shorter, u ∈ visited := by
  induction size : visited.length using Nat.strongRecOn
    generalizing visited start final with
  | ind lengthBound ih =>
    by_cases reappears : start.1 ∈ visited
    · obtain ⟨shorter, mid, erased, endpoint, small, subset⟩ :=
        drop_repeated_start walk reappears
      obtain ⟨path, last, simple, same, nodup, subpath⟩ :=
        ih shorter.length (size ▸ small) erased rfl
      exact ⟨path, last, simple, same.trans endpoint, nodup,
        fun u mem => subset u (subpath u mem)⟩
    · cases walk with
      | nil =>
        exact ⟨[], start, .nil _, rfl, by simp, fun _ h => by cases h⟩
      | @cons start next final rest move suffix =>
        have small : rest.length < lengthBound := by simp at size; omega
        obtain ⟨path, last, simple, same, nodup, subpath⟩ :=
          ih rest.length small suffix rfl
        have subset : ∀ u ∈ next.1 :: path, u ∈ next.1 :: rest := by
          intro u mem
          rcases List.mem_cons.mp mem with head | tail
          · exact List.mem_cons.mpr (.inl head)
          · exact List.mem_cons.mpr (.inr (subpath _ tail))
        exact ⟨next.1 :: path, last, .cons move simple, same,
          List.nodup_cons.mpr ⟨fun h => reappears (subset _ h), nodup⟩, subset⟩

/-- Standard simple-path d-connection for unconditioned endpoints, including
the zero-edge case used when a seed is itself in the output. The visits are
pairwise distinct and obey the usual collider and noncollider rules. -/
def DConnected {G : DAG n} (C : Conditioning G) (source target : Fin n) : Prop :=
  C.member source = false ∧ C.member target = false ∧
    ∃ visited arrival, ActiveWalk C (source, .up) visited (target, arrival) ∧
      (source :: visited).Nodup

theorem corrected_reachable_iff_dconnected {G : DAG n} (C : Conditioning G)
    {source target : Fin n}
    (sourceOutside : C.member source = false) (targetOutside : C.member target = false) :
    (∃ arrival, Reachable (nextStates (neighborhood G C) true) (source, .up) (target, arrival)) ↔
      DConnected C source target := by
  constructor
  · rintro ⟨arrival, reaches⟩
    obtain ⟨visited, walk⟩ := (corrected_reachable_iff_active_walk C).mp reaches
    obtain ⟨shorter, last, simple, endpoint, nodup, _⟩ := walk.to_simple
    rcases last with ⟨v, dir⟩
    change v = target at endpoint
    subst v
    exact ⟨sourceOutside, targetOutside, shorter, dir, simple, nodup⟩
  · rintro ⟨_, _, visited, arrival, walk, _⟩
    exact ⟨arrival, (corrected_reachable_iff_active_walk C).mpr ⟨visited, walk⟩⟩

/-- Process a FIFO queue over the remaining states. Expanding a state
removes it from the remaining list, while skipping a state shortens the
pending queue. A duplicate-free remaining list prevents repeat expansions. -/
def explore {α : Type} [DecidableEq α] (next : α → List α) (remaining pending : List α) :
    List α :=
  match pending with
  | [] => []
  | state :: tail =>
    if state ∈ remaining then
      state :: explore next (remaining.erase state) (tail ++ next state)
    else
      explore next remaining tail
termination_by (remaining.length, pending.length)
decreasing_by
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem ‹state ∈ remaining›]
    have size := List.length_pos_of_mem ‹state ∈ remaining›
    omega
  · exact Prod.Lex.right _ (by simp)


private theorem explore_covers {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {state : α}
    (unseen : state ∈ remaining) (queued : state ∈ pending) :
    state ∈ explore next remaining pending := by
  induction remaining, pending using explore.induct next with
  | case1 => simp at queued
  | case2 remaining current tail present ih =>
    rw [explore, ite_eq_left present]
    rcases List.mem_cons.mp queued with same | later
    · exact List.mem_cons.mpr (.inl same)
    · by_cases same : state = current
      · exact List.mem_cons.mpr (.inl same)
      · exact List.mem_cons.mpr (.inr (ih ((List.mem_erase_of_ne same).mpr unseen)
          (List.mem_append_left _ later)))
  | case3 remaining current tail absent ih =>
    rw [explore, ite_eq_right absent]
    apply ih unseen
    rcases List.mem_cons.mp queued with same | later
    · exact (absent (same ▸ unseen)).elim
    · exact later

private theorem explore_closed {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {before after : α}
    (reached : before ∈ explore next remaining pending) (move : after ∈ next before)
    (unseen : after ∈ remaining) : after ∈ explore next remaining pending := by
  induction remaining, pending using explore.induct next with
  | case1 => simp [explore] at reached
  | case2 remaining current tail present ih =>
    rw [explore, ite_eq_left present] at reached ⊢
    by_cases same : after = current
    · exact List.mem_cons.mpr (.inl same)
    have stays := (List.mem_erase_of_ne same).mpr unseen
    apply List.mem_cons.mpr
    right
    rcases List.mem_cons.mp reached with eq | later
    · subst before
      exact explore_covers stays (List.mem_append_right _ move)
    · exact ih later stays
  | case3 remaining current tail absent ih =>
    rw [explore, ite_eq_right absent] at reached ⊢
    exact ih reached unseen

private theorem explore_sound {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {P : α → Prop} {state : α}
    (closed : ∀ a b, P a → b ∈ next a → P b)
    (queued : ∀ a ∈ pending, P a)
    (found : state ∈ explore next remaining pending) : P state := by
  induction remaining, pending using explore.induct next with
  | case1 => simp [explore] at found
  | case2 remaining current tail present ih =>
    rw [explore, ite_eq_left present] at found
    have currentP := queued current (List.mem_cons_self)
    rcases List.mem_cons.mp found with eq | later
    · exact eq ▸ currentP
    · apply ih _ later
      intro a mem
      rcases List.mem_append.mp mem with waiting | added
      · exact queued a (List.mem_cons_of_mem _ waiting)
      · exact closed current a currentP added
  | case3 remaining current tail absent ih =>
    rw [explore, ite_eq_right absent] at found
    exact ih (fun a mem => queued a (List.mem_cons_of_mem _ mem)) found

private theorem explore_subset {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {state : α}
    (found : state ∈ explore next remaining pending) : state ∈ remaining := by
  induction remaining, pending using explore.induct next with
  | case1 => simp [explore] at found
  | case2 remaining current tail present ih =>
    rw [explore, ite_eq_left present] at found
    rcases List.mem_cons.mp found with eq | later
    · exact eq ▸ present
    · exact List.mem_of_mem_erase (ih later)
  | case3 remaining current tail absent ih =>
    rw [explore, ite_eq_right absent] at found
    exact ih found

theorem explore_nodup {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} (remainingUnique : remaining.Nodup) :
    (explore next remaining pending).Nodup := by
  induction remaining, pending using explore.induct next with
  | case1 => simp [explore]
  | case2 remaining current tail present ih =>
    rw [explore, ite_eq_left present]
    exact List.nodup_cons.mpr
      ⟨fun found => remainingUnique.not_mem_erase (explore_subset found),
        ih (remainingUnique.erase _)⟩
  | case3 remaining current tail absent ih =>
    rw [explore, ite_eq_right absent]
    exact ih remainingUnique

def allStates (n : Nat) : List (State (Fin n)) :=
  ((List.finRange n).map (·, .up)) ++ ((List.finRange n).map (·, .down))

private theorem mem_allStates (state : State (Fin n)) : state ∈ allStates n := by
  obtain ⟨v, dir⟩ := state
  cases dir <;> simp [allStates, List.mem_map]

private theorem allStates_nodup (n : Nat) : (allStates n).Nodup := by
  have each (direction : Direction) :
      ((List.finRange n).map (·, direction)).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (List.nodup_finRange n).imp fun diff same => diff (congrArg Prod.fst same)
  apply List.nodup_append.mpr
  refine ⟨each .up, each .down, ?_⟩
  intro a up b down
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp up
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp down
  simp

/-- FIFO worklist of directional states visited from the seeds. -/
def visitedStates {G : DAG n} (C : Conditioning G) (seeds : List (Fin n)) :
    List (State (Fin n)) :=
  explore (nextStates (neighborhood G C) true) (allStates n) (seeds.map (·, .up))

theorem visitedStates_nodup {G : DAG n} (C : Conditioning G) (seeds : List (Fin n)) :
    (visitedStates C seeds).Nodup :=
  explore_nodup (allStates_nodup n)

theorem mem_visitedStates_iff {G : DAG n} (C : Conditioning G) (seeds : List (Fin n))
    (state : State (Fin n)) :
    state ∈ visitedStates C seeds ↔ ∃ seed ∈ seeds,
      Reachable (nextStates (neighborhood G C) true) (seed, .up) state := by
  unfold visitedStates
  constructor
  · intro found
    refine explore_sound (P := fun s => ∃ seed ∈ seeds,
      Reachable (nextStates (neighborhood G C) true) (seed, .up) s) ?_ ?_ found
    · rintro a b ⟨seed, mem, reached⟩ step
      exact ⟨seed, mem, .step reached step⟩
    · intro a mem
      obtain ⟨seed, input, rfl⟩ := List.mem_map.mp mem
      exact ⟨seed, input, .start⟩
  · rintro ⟨seed, mem, reached⟩
    induction reached with
    | start =>
      exact explore_covers (mem_allStates _) (List.mem_map.mpr ⟨seed, mem, rfl⟩)
    | step _ move ih =>
      exact explore_closed ih move (mem_allStates _)

/-- The corrected Algorithm 2, with seeds retained as initially supplied.
Reached vertices are added only if they are neither conditioned nor observed.
List order is immaterial to the returned set. -/
def bayesBall (G : DAG n) (seeds : List (Fin n)) (conditioned observed : Fin n → Bool) :
    List (Fin n) :=
  let C := Conditioning.ofPredicate G conditioned
  let candidates := ((visitedStates C seeds).map Prod.fst).filter fun u =>
    !conditioned u && !observed u
  (seeds ++ candidates).eraseDups

theorem mem_bayesBall_iff (G : DAG n) (seeds : List (Fin n))
    (conditioned observed : Fin n → Bool) (target : Fin n) :
    target ∈ bayesBall G seeds conditioned observed ↔
      target ∈ seeds ∨ (observed target = false ∧ ∃ seed ∈ seeds,
        DConnected (Conditioning.ofPredicate G conditioned) seed target) := by
  let C := Conditioning.ofPredicate G conditioned
  constructor
  · intro mem
    rw [bayesBall, List.mem_eraseDups, List.mem_append] at mem
    rcases mem with isSeed | added
    · exact Or.inl isSeed
    by_cases isSeed : target ∈ seeds
    · exact Or.inl isSeed
    have filters := List.mem_filter.mp added
    have outside : C.member target = false ∧ observed target = false := by
      simpa [C, Conditioning.ofPredicate] using filters.2
    obtain ⟨⟨v, arrival⟩, visited, same⟩ := List.mem_map.mp filters.1
    change v = target at same
    subst v
    obtain ⟨seed, input, reached⟩ := (mem_visitedStates_iff C seeds _).mp visited
    obtain ⟨vertices, walk⟩ := (corrected_reachable_iff_active_walk C).mp reached
    have nonempty : vertices ≠ [] := by
      intro empty
      rw [empty] at walk
      cases walk
      exact isSeed input
    have sourceOutside := walk.first_open_if_up nonempty rfl
    exact Or.inr ⟨outside.2, seed, input,
      (corrected_reachable_iff_dconnected C sourceOutside outside.1).mp ⟨arrival, reached⟩⟩
  · intro answer
    rw [bayesBall, List.mem_eraseDups, List.mem_append]
    rcases answer with input | ⟨unobserved, seed, input, connected⟩
    · exact Or.inl input
    obtain ⟨arrival, reached⟩ :=
      (corrected_reachable_iff_dconnected C connected.1 connected.2.1).mpr connected
    refine Or.inr (List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(target, arrival), ?_, rfl⟩, ?_⟩)
    · exact (mem_visitedStates_iff C seeds _).mpr ⟨seed, input, reached⟩
    · have outside : conditioned target = false := connected.2.1
      simp [outside, unobserved]

end

end OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
