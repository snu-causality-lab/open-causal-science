module
public import OpenCausalScience.Graph.MixedGraph

/-! # The mixed-graph separation search

CGA first follows directed edges backwards from the conditioning set. It
then searches arrival states (vertex, incoming arrowhead) from the edges
incident to the left set. The transition tests collider activation and
noncollider blocking. The Boolean denotes absence of a reached right
endpoint.

The finite lists below enumerate the states of this search. The worklist
proof characterizes its visited set by seeds and transitions, so the order
used to enumerate edges does not affect the result.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat}

/-- A stack over the remaining set. The head is the top of the stack.
A successor enters the stack only while it is unprocessed and absent from
the stack. The mixed-graph seed and successor lists contain distinct states. -/
def exploreStack {α : Type} [DecidableEq α] (next : α → List α)
    (remaining pending : List α) : List α :=
  match pending with
  | [] => []
  | state :: tail =>
    if state ∈ remaining then
      state :: exploreStack next (remaining.erase state)
        (((next state).filter (fun candidate =>
          decide (candidate ∈ remaining.erase state) && !decide (candidate ∈ tail))).reverse ++ tail)
    else
      exploreStack next remaining tail
termination_by (remaining.length, pending.length)
decreasing_by
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem ‹state ∈ remaining›]
    have size := List.length_pos_of_mem ‹state ∈ remaining›
    omega
  · exact Prod.Lex.right _ (by simp)

private theorem stack_covers {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {state : α}
    (unseen : state ∈ remaining) (queued : state ∈ pending) :
    state ∈ exploreStack next remaining pending := by
  induction remaining, pending using exploreStack.induct next with
  | case1 => simp at queued
  | case2 remaining current tail present ih =>
    rw [exploreStack, ite_eq_left present]
    rcases List.mem_cons.mp queued with same | later
    · exact List.mem_cons.mpr (.inl same)
    · by_cases same : state = current
      · exact List.mem_cons.mpr (.inl same)
      · exact List.mem_cons.mpr (.inr (ih ((List.mem_erase_of_ne same).mpr unseen)
          (List.mem_append_right _ later)))
  | case3 remaining current tail absent ih =>
    rw [exploreStack, ite_eq_right absent]
    apply ih unseen
    rcases List.mem_cons.mp queued with same | later
    · exact (absent (same ▸ unseen)).elim
    · exact later

private theorem stack_closed {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {before after : α}
    (reached : before ∈ exploreStack next remaining pending) (move : after ∈ next before)
    (unseen : after ∈ remaining) : after ∈ exploreStack next remaining pending := by
  induction remaining, pending using exploreStack.induct next with
  | case1 => simp [exploreStack] at reached
  | case2 remaining current tail present ih =>
    rw [exploreStack, ite_eq_left present] at reached ⊢
    by_cases same : after = current
    · exact List.mem_cons.mpr (.inl same)
    have stays := (List.mem_erase_of_ne same).mpr unseen
    apply List.mem_cons.mpr
    right
    rcases List.mem_cons.mp reached with eq | later
    · subst before
      by_cases waiting : after ∈ tail
      · exact stack_covers stays (List.mem_append_right _ waiting)
      · have added : after ∈ (next current).filter (fun candidate =>
            decide (candidate ∈ remaining.erase current) && !decide (candidate ∈ tail)) :=
          List.mem_filter.mpr ⟨move, by simp [stays, waiting]⟩
        exact stack_covers stays (List.mem_append_left _ (by simpa using added))
    · exact ih later stays
  | case3 remaining current tail absent ih =>
    rw [exploreStack, ite_eq_right absent] at reached ⊢
    exact ih reached unseen

private theorem stack_sound {α : Type} [DecidableEq α] {next : α → List α}
    {remaining pending : List α} {P : α → Prop} {state : α}
    (closed : ∀ a b, P a → b ∈ next a → P b)
    (queued : ∀ a ∈ pending, P a)
    (found : state ∈ exploreStack next remaining pending) : P state := by
  induction remaining, pending using exploreStack.induct next with
  | case1 => simp [exploreStack] at found
  | case2 remaining current tail present ih =>
    rw [exploreStack, ite_eq_left present] at found
    have currentP := queued current List.mem_cons_self
    rcases List.mem_cons.mp found with eq | later
    · exact eq ▸ currentP
    · apply ih _ later
      intro a mem
      rcases List.mem_append.mp mem with added | waiting
      · have fresh : a ∈ (next current).filter (fun candidate =>
            decide (candidate ∈ remaining.erase current) && !decide (candidate ∈ tail)) := by
          simpa using added
        exact closed current a currentP (List.mem_filter.mp fresh).1
      · exact queued a (List.mem_cons_of_mem _ waiting)
  | case3 remaining current tail absent ih =>
    rw [exploreStack, ite_eq_right absent] at found
    exact ih (fun a mem => queued a (List.mem_cons_of_mem _ mem)) found

/-- The order of a finite stack search does not affect membership in its
visited set. The universe contains every state of the transition relation. -/
theorem mem_exploreStack_iff {α : Type} [DecidableEq α] {next : α → List α}
    {states seeds : List α} {state : α} (complete : ∀ a, a ∈ states) :
    state ∈ exploreStack next states seeds ↔
      ∃ seed, seed ∈ seeds ∧ Reach (fun a b => b ∈ next a) seed state := by
  constructor
  · intro found
    refine stack_sound (P := fun current => ∃ seed, seed ∈ seeds ∧
      Reach (fun a b => b ∈ next a) seed current) ?_ ?_ found
    · rintro a b ⟨seed, initial, reached⟩ move
      exact ⟨seed, initial, .extend reached move⟩
    · intro seed initial
      exact ⟨seed, initial, .refl seed⟩
  · rintro ⟨seed, initial, reached⟩
    induction reached with
    | refl => exact stack_covers (complete seed) initial
    | extend _ move ih => exact stack_closed ih move (complete _)

/-- Parents in the directed part of the mixed graph. -/
def directedParents (G : MixedGraph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun u => G.edge u false v true

/-- The reflexive directed ancestors of the conditioning set. -/
def ancestorVertices (G : MixedGraph n) (conditioning : Fin n → Bool) : List (Fin n) :=
  exploreStack G.directedParents (List.finRange n) ((List.finRange n).filter conditioning)

theorem mem_ancestorVertices_iff (G : MixedGraph n) (conditioning : Fin n → Bool) (v : Fin n) :
    v ∈ G.ancestorVertices conditioning ↔ G.AncestorOf conditioning v := by
  unfold ancestorVertices
  constructor
  · intro found
    refine stack_sound (P := G.AncestorOf conditioning) ?_ ?_ found
    · intro a b reached parent
      exact .parent (List.mem_filter.mp parent).2 reached
    · intro a seed
      exact .conditioned (List.mem_filter.mp seed).2
  · intro ancestor
    induction ancestor with
    | conditioned present =>
      exact stack_covers (List.mem_finRange _) (List.mem_filter.mpr ⟨List.mem_finRange _, present⟩)
    | parent edge _ ih =>
      exact stack_closed ih (List.mem_filter.mpr ⟨List.mem_finRange _, edge⟩) (List.mem_finRange _)

def allArrivals (n : Nat) : List (Arrival n) :=
  ((List.finRange n).map (·, false)) ++ ((List.finRange n).map (·, true))

private theorem mem_allArrivals (s : Arrival n) : s ∈ allArrivals n := by
  obtain ⟨u, mark⟩ := s
  cases mark <;> simp [allArrivals, List.mem_map]

/-- Start by traversing one edge, retaining the arrival arrowhead. -/
def seedArrivals (G : MixedGraph n) (left : Fin n → Bool) : List (Arrival n) :=
  (allArrivals n).filter fun s =>
    (List.finRange n).any fun x =>
      left x && (G.edge x false s.1 s.2 || G.edge x true s.1 s.2)

theorem mem_seedArrivals_iff (G : MixedGraph n) (left : Fin n → Bool) (s : Arrival n) :
    s ∈ G.seedArrivals left ↔ G.Seed left s := by
  simp only [seedArrivals, List.mem_filter, mem_allArrivals, true_and, List.any_eq_true,
    List.mem_finRange, Bool.and_eq_true, Bool.or_eq_true_iff, Seed]
  constructor
  · rintro ⟨x, hx, tail | head⟩
    · exact ⟨x, false, hx, tail⟩
    · exact ⟨x, true, hx, head⟩
  · rintro ⟨x, outgoing, hx, edge⟩
    cases outgoing
    · exact ⟨x, hx, .inl edge⟩
    · exact ⟨x, hx, .inr edge⟩

def openTurnBool (ancestors : List (Fin n)) (conditioning : Fin n → Bool)
    (s : Arrival n) (outgoing : Bool) : Bool :=
  if s.2 && outgoing then decide (s.1 ∈ ancestors) else !conditioning s.1

private theorem openTurnBool_iff (G : MixedGraph n) (conditioning : Fin n → Bool) (s : Arrival n)
    (outgoing : Bool) :
    openTurnBool (G.ancestorVertices conditioning) conditioning s outgoing = true ↔
      G.openTurn conditioning s outgoing := by
  by_cases mark : (s.2 && outgoing) = true
  · simp [openTurnBool, openTurn, mark, mem_ancestorVertices_iff]
  · simp [openTurnBool, openTurn, mark]

/-- The next states over both possible outgoing marks. -/
def nextArrivals (G : MixedGraph n) (ancestors : List (Fin n)) (conditioning : Fin n → Bool)
    (s : Arrival n) : List (Arrival n) :=
  (allArrivals n).filter fun t =>
    (G.edge s.1 false t.1 t.2 && openTurnBool ancestors conditioning s false) ||
    (G.edge s.1 true t.1 t.2 && openTurnBool ancestors conditioning s true)

theorem mem_nextArrivals_iff (G : MixedGraph n) (conditioning : Fin n → Bool) (s t : Arrival n) :
    t ∈ G.nextArrivals (G.ancestorVertices conditioning) conditioning s ↔ G.Step conditioning s t := by
  simp only [nextArrivals, List.mem_filter, mem_allArrivals, true_and, Bool.or_eq_true_iff,
    Bool.and_eq_true, openTurnBool_iff, Step]
  constructor
  · rintro (⟨h, hop⟩ | ⟨h, hop⟩)
    · exact ⟨false, h, hop⟩
    · exact ⟨true, h, hop⟩
  · rintro ⟨outgoing, h, hop⟩
    cases outgoing
    · exact .inl ⟨h, hop⟩
    · exact .inr ⟨h, hop⟩

/-- Compute the ancestor set once, then explore from the seed states. -/
def visitedArrivals (G : MixedGraph n) (left conditioning : Fin n → Bool) : List (Arrival n) :=
  exploreStack (G.nextArrivals (G.ancestorVertices conditioning) conditioning) (allArrivals n)
    (G.seedArrivals left)

theorem mem_visitedArrivals_iff (G : MixedGraph n) (left conditioning : Fin n → Bool) (s : Arrival n) :
    s ∈ G.visitedArrivals left conditioning ↔
      ∃ first, G.Seed left first ∧ Reach (G.Step conditioning) first s := by
  unfold visitedArrivals
  constructor
  · intro found
    refine stack_sound (P := fun arrival => ∃ first, G.Seed left first ∧
      Reach (G.Step conditioning) first arrival) ?_ ?_ found
    · rintro a b ⟨first, seeded, reached⟩ move
      exact ⟨first, seeded, .extend reached ((G.mem_nextArrivals_iff conditioning a b).mp move)⟩
    · intro a member
      exact ⟨a, (G.mem_seedArrivals_iff left a).mp member, .refl a⟩
  · rintro ⟨first, seeded, reached⟩
    have start : first ∈ exploreStack (G.nextArrivals (G.ancestorVertices conditioning) conditioning)
        (allArrivals n) (G.seedArrivals left) :=
      stack_covers (mem_allArrivals first) ((G.mem_seedArrivals_iff left first).mpr seeded)
    induction reached with
    | refl => exact start
    | extend _ move ih =>
      exact stack_closed ih ((G.mem_nextArrivals_iff conditioning _ _).mpr move) (mem_allArrivals _)

/-- True exactly when the arrival search cannot reach the right set. -/
def mSeparated (G : MixedGraph n) (left right conditioning : Fin n → Bool) : Bool :=
  !((G.visitedArrivals left conditioning).any fun s => right s.1)

theorem m_separated_iff_no_walk (G : MixedGraph n) (left right conditioning : Fin n → Bool) :
    G.mSeparated left right conditioning = true ↔ ¬ G.WalkConnected left right conditioning := by
  have hits : ((G.visitedArrivals left conditioning).any fun s => right s.1) = true ↔
      G.WalkConnected left right conditioning := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨last, visited, target⟩
      obtain ⟨first, seeded, reached⟩ := (G.mem_visitedArrivals_iff left conditioning last).mp visited
      exact ⟨first, last, seeded, reached, target⟩
    · rintro ⟨first, last, seeded, reached, target⟩
      exact ⟨last, (G.mem_visitedArrivals_iff left conditioning last).mpr ⟨first, seeded, reached⟩,
        target⟩
  rw [mSeparated, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr hits


/-- A right endpoint can be detected at initialization or when considering
a successor, before the successor is queued. This is the discovery-time
target predicate of CGA's search. -/
theorem walk_connected_iff_discovered_target (G : MixedGraph n)
    (left right conditioning : Fin n → Bool) :
    G.WalkConnected left right conditioning ↔
      (∃ seed, G.Seed left seed ∧ right seed.1 = true) ∨
      ∃ before after, before ∈ G.visitedArrivals left conditioning ∧
        G.Step conditioning before after ∧ right after.1 = true := by
  constructor
  · rintro ⟨first, last, seeded, reached, target⟩
    cases reached with
    | refl => exact .inl ⟨_, seeded, target⟩
    | extend walkSoFar step =>
      exact .inr ⟨_, _, (G.mem_visitedArrivals_iff left conditioning _).mpr
        ⟨first, seeded, walkSoFar⟩, step, target⟩
  · rintro (⟨seed, seeded, target⟩ | ⟨before, after, visited, step, target⟩)
    · exact ⟨seed, seed, seeded, .refl seed, target⟩
    · obtain ⟨first, seeded, reached⟩ :=
        (G.mem_visitedArrivals_iff left conditioning before).mp visited
      exact ⟨first, after, seeded, .extend reached step, target⟩

end

end OpenCausalScience.MixedGraph
