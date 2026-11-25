module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
public import OpenCausalScience.Papers.JungEtAl2024.StageGraph

/-! # Executable queries and the DAG equivalence signature

The finite search `DAG.dSeparated` has the same answers as the active-path
relation for distinct endpoints outside the conditioning set. A mismatch of
the graph signature then requires a different answer to an executable query.
-/

namespace OpenCausalScience.Papers.VermaPearl1990.ExecutableQuery

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026
open BayesBall BayesBallCorrectness DAGEquivalence

@[expose] public section

variable {n : Nat}

private theorem directedWalk_prepend {G : DAG n} {u v w : Fin n}
    (edge : G.edge u v = true) (walk : G.DirectedWalk v w) : G.DirectedWalk u w := by
  induction walk with
  | single last => exact .extend (.single edge) last
  | extend _ last ih => exact .extend ih last

private theorem parent_activated {G : DAG n} {C : Conditioning G} {u v : Fin n}
    (incoming : G.edge u v = true) (active : C.activated v = true) :
    C.activated u = true := by
  apply Bool.or_eq_true_iff.mpr
  right
  apply (C.descendant_spec u).mpr
  rcases Bool.or_eq_true_iff.mp active with member | descendant
  · exact ⟨v, member, .single incoming⟩
  · obtain ⟨w, member, downward⟩ := (C.descendant_spec v).mp descendant
    exact ⟨w, member, directedWalk_prepend incoming downward⟩

/-- Every vertex found by the ancestor closure is conditioned or has
a conditioned descendant. -/
theorem activated_of_mem_conditioningAncestors (G : DAG n) (cond : List (Fin n)) {u : Fin n}
    (inClosure : u ∈ G.conditioningAncestors cond) :
    (Conditioning.ofPredicate G cond.contains).activated u = true := by
  let C := Conditioning.ofPredicate G cond.contains
  let step (known : List (Fin n)) :=
    (List.finRange n).filter fun v => known.contains v || known.any (G.edge v)
  have found : u ∈ (List.range n).foldl (fun known _ => step known) cond := inClosure
  have invariant (rounds : List Nat) (known : List (Fin n))
      (base : ∀ v ∈ known, C.activated v = true)
      (mem : u ∈ rounds.foldl (fun known _ => step known) known) : C.activated u = true := by
    induction rounds generalizing known with
    | nil => exact base u mem
    | cons _ rest ih =>
      apply ih (step known) _ mem
      intro v next
      have added : known.contains v || known.any (G.edge v) := (List.mem_filter.mp next).2
      rcases Bool.or_eq_true_iff.mp added with present | child
      · exact base v (List.contains_iff_mem.mp present)
      · obtain ⟨w, seen, arrow⟩ := List.any_eq_true.mp child
        exact parent_activated arrow (base w seen)
  apply invariant _ _ _ found
  intro v mem
  exact Bool.or_eq_true_iff.mpr (.inl (List.contains_iff_mem.mpr mem))

private def ValidArrival {G : DAG n} (C : Conditioning G) (previous : Option (Fin n))
    (start : State (Fin n)) : Prop :=
  match previous with
  | none => start.2 = .up ∧ C.member start.1 = false
  | some prev => Move G (prev, .up) start

private theorem reverse_edge_false {G : DAG n} {a b : Fin n} (edge : G.edge a b = true) :
    G.edge b a = false := by
  apply Bool.eq_false_iff.mpr
  intro opposite
  exact G.no_directed_cycle a (.extend (.single edge) opposite)

private theorem search_turn_is_open {G : DAG n} {C : Conditioning G}
    {cond activated : List (Fin n)} (member : ∀ v, C.member v = cond.contains v)
    (closure : ∀ v, activated.contains v = true → C.activated v = true)
    {previous : Option (Fin n)} {start next : State (Fin n)}
    (openTest : (match previous with
      | none => true
      | some prev => if G.edge prev start.1 && G.edge next.1 start.1 then
          activated.contains start.1 else !(cond.contains start.1)) = true)
    (arrived : ValidArrival C previous start) (move : Move G start next) :
    OpenTurn C start next.2 := by
  cases previous with
  | none =>
    obtain ⟨direction, outside⟩ := arrived
    simp [OpenTurn, direction, outside]
  | some prev =>
    have incoming : G.edge prev start.1 = true ↔ start.2 = .down := by
      cases dir : start.2 with
      | down =>
        simpa [ValidArrival, Move, dir] using arrived
      | up =>
        have pointsOut : G.edge start.1 prev = true := by
          simpa [ValidArrival, Move, dir] using arrived
        simp [reverse_edge_false pointsOut]
    have outgoing : G.edge next.1 start.1 = true ↔ next.2 = .up := by
      cases dir : next.2 with
      | up => simpa [Move, dir] using move
      | down =>
        have pointsOut : G.edge start.1 next.1 = true := by
          simpa [Move, dir] using move
        simp [reverse_edge_false pointsOut]
    by_cases turn : start.2 = .down ∧ next.2 = .up
    · have fromPrev := incoming.mpr turn.1
      have fromNext := outgoing.mpr turn.2
      have active : activated.contains start.1 = true := by
        simpa [fromPrev, fromNext] using openTest
      simpa [OpenTurn, turn] using closure start.1 active
    · have noCollider : ¬ (G.edge prev start.1 && G.edge next.1 start.1) = true := by
        intro yes
        obtain ⟨fromPrev, fromNext⟩ := Bool.and_eq_true_iff.mp yes
        exact turn ⟨incoming.mp fromPrev, outgoing.mp fromNext⟩
      have unconditioned : cond.contains start.1 = false := by
        simpa [noCollider] using openTest
      simpa [OpenTurn, turn, member] using unconditioned

private theorem search_produces_active_walk {G : DAG n} {C : Conditioning G}
    {target : Fin n} {cond activated : List (Fin n)}
    (member : ∀ v, C.member v = cond.contains v)
    (closure : ∀ v, activated.contains v = true → C.activated v = true)
    (fuel : Nat) (previous : Option (Fin n)) (start : State (Fin n))
    (unvisited : List (Fin n)) (arrived : ValidArrival C previous start)
    (found : G.searchActivePath target cond activated fuel previous start.1 unvisited = true) :
    ∃ visited arrival, ActiveWalk C start visited (target, arrival) := by
  induction fuel generalizing previous start unvisited with
  | zero => cases found
  | succ fuel ih =>
    by_cases done : start.1 = target
    · rcases start with ⟨v, direction⟩
      change v = target at done
      subst v
      exact ⟨[], direction, .nil _⟩
    · rw [DAG.searchActivePath, ite_eq_right fun same => done (beq_iff_eq.mp same)] at found
      obtain ⟨v, _, chosen⟩ := List.any_eq_true.mp found
      obtain ⟨edgeTurn, accepted⟩ := Bool.and_eq_true_iff.mp chosen
      obtain ⟨edge, openTest⟩ := Bool.and_eq_true_iff.mp edgeTurn
      obtain ⟨departure, move⟩ : ∃ d, Move G start (v, d) := by
        rcases Bool.or_eq_true_iff.mp edge with forward | backward
        · exact ⟨.down, forward⟩
        · exact ⟨.up, backward⟩
      have nextArrival : ValidArrival C (some start.1) (v, departure) := move
      obtain ⟨later, arrival, tail⟩ := ih (some start.1) (v, departure) _ nextArrival accepted
      exact ⟨v :: later, arrival, .cons ⟨move, search_turn_is_open (next := (v, departure)) member closure openTest arrived move⟩ tail⟩

theorem dConnected_of_dSeparated_false {G : DAG n} {x y : Fin n} {cond : List (Fin n)}
    (connected : G.dSeparated x y cond = some false) :
    DConnected (Conditioning.ofPredicate G cond.contains) x y := by
  unfold DAG.dSeparated at connected
  split at connected
  · cases connected
  · rename_i valid
    have endpoints : (x == y) = false ∧ cond.contains x = false ∧ cond.contains y = false := by
      simpa [Bool.or_eq_true, not_or, and_assoc] using valid
    have found : G.searchActivePath y cond (G.conditioningAncestors cond) n none x
        ((List.finRange n).filter (· != x)) = true := by
      simpa using connected
    let C := Conditioning.ofPredicate G cond.contains
    have closure : ∀ v, (G.conditioningAncestors cond).contains v = true → C.activated v = true :=
      fun _ active => activated_of_mem_conditioningAncestors G cond
        (List.contains_iff_mem.mp active)
    obtain ⟨_, _, walk⟩ :=
      search_produces_active_walk (C := C) (fun _ => rfl) closure n none (x, .up) _
        ⟨rfl, endpoints.2.1⟩ found
    obtain ⟨simple, last, activeWalk, target, distinct, _⟩ := walk.to_simple
    rcases last with ⟨v, arrival⟩
    change v = y at target
    subst v
    exact ⟨endpoints.2.1, endpoints.2.2, simple, arrival, activeWalk, distinct⟩

private theorem valid_endpoint_guard {x y : Fin n} {cond : List (Fin n)}
    (different : x ≠ y) (xOutside : cond.contains x = false) (yOutside : cond.contains y = false) :
    (x == y || cond.contains x || cond.contains y) ≠ true := by
  intro bad
  rcases Bool.or_eq_true_iff.mp bad with first | endHit
  · rcases Bool.or_eq_true_iff.mp first with same | startHit
    · exact different (beq_iff_eq.mp same)
    · exact Bool.false_ne_true (xOutside.symm.trans startHit)
  · exact Bool.false_ne_true (yOutside.symm.trans endHit)

theorem dSeparated_false_iff_dConnected (G : DAG n) {x y : Fin n} {cond : List (Fin n)}
    (different : x ≠ y) :
    G.dSeparated x y cond = some false ↔
      DConnected (Conditioning.ofPredicate G cond.contains) x y := by
  refine ⟨dConnected_of_dSeparated_false, ?_⟩
  intro connected
  cases result : G.dSeparated x y cond with
  | none =>
    have xOutside : cond.contains x = false := connected.1
    have yOutside : cond.contains y = false := connected.2.1
    rw [DAG.dSeparated, ite_eq_right (valid_endpoint_guard different xOutside yOutside)] at result
    cases result
  | some resultValue =>
    cases resultValue with
    | false => rfl
    | true =>
      exact ((JungEtAl2024.StageGraph.dSeparatedBy_of_dSeparated result).2.2.2 connected).elim

theorem dSeparated_true_iff_dSeparatedBy (G : DAG n) {x y : Fin n} {cond : List (Fin n)} :
    G.dSeparated x y cond = some true ↔
      JungEtAl2024.StageGraph.DSeparatedBy (Conditioning.ofPredicate G cond.contains) x y := by
  refine ⟨JungEtAl2024.StageGraph.dSeparatedBy_of_dSeparated, ?_⟩
  rintro ⟨different, xOutside, yOutside, separated⟩
  cases result : G.dSeparated x y cond with
  | none =>
    have guard : (x == y || cond.contains x || cond.contains y) ≠ true :=
      valid_endpoint_guard different xOutside yOutside
    rw [DAG.dSeparated, ite_eq_right guard] at result
    cases result
  | some resultValue =>
    cases resultValue with
    | false => exact (separated (dConnected_of_dSeparated_false result)).elim
    | true => rfl

private theorem contains_filter_finRange (member : Fin n → Bool) :
    ((List.finRange n).filter member).contains = member := by
  funext v
  cases h : member v <;> simp [h]

/-- If two DAGs answer every executable query identically, they have the
same semantic singleton d-connections. -/
theorem sameDConnections_of_same_dSeparated {G H : DAG n}
    (equivalent : ∀ x y cond, G.dSeparated x y cond = H.dSeparated x y cond) :
    SameDConnections G H := by
  intro member x y
  by_cases different : x = y
  · subst y
    exact ⟨fun h => ⟨h.1, h.1, [], .up, .nil _, by simp⟩,
      fun h => ⟨h.1, h.1, [], .up, .nil _, by simp⟩⟩
  · let cond := (List.finRange n).filter member
    have members : cond.contains = member := contains_filter_finRange member
    rw [← members, ← dSeparated_false_iff_dConnected G different,
      ← dSeparated_false_iff_dConnected H different, equivalent]

/-- A mismatch of the CGA-style signature entails a different answer by
the executable d-separation test for two distinct unconditioned vertices. -/
theorem distinguishing_dSeparated_of_signaturesMismatch {G H : DAG n}
    (mismatch : signaturesMatch G H = false) :
    ∃ x y cond, x ≠ y ∧ cond.contains x = false ∧ cond.contains y = false ∧
      G.dSeparated x y cond ≠ H.dSeparated x y cond := by
  classical
  obtain ⟨member, x, y, differentAnswer⟩ := distinguishing_query_of_signaturesMismatch mismatch
  let cond := (List.finRange n).filter member
  have members : cond.contains = member := contains_filter_finRange member
  have distinct : x ≠ y := by
    intro same
    subst y
    exact differentAnswer ⟨fun h => ⟨h.1, h.1, [], .up, .nil _, by simp⟩,
      fun h => ⟨h.1, h.1, [], .up, .nil _, by simp⟩⟩
  have xOutside : cond.contains x = false := by
    rw [members]
    apply Bool.eq_false_iff.mpr
    intro inside
    exact differentAnswer ⟨fun h => (Bool.false_ne_true (h.1.symm.trans inside)).elim,
      fun h => (Bool.false_ne_true (h.1.symm.trans inside)).elim⟩
  have yOutside : cond.contains y = false := by
    rw [members]
    apply Bool.eq_false_iff.mpr
    intro inside
    exact differentAnswer ⟨fun h => (Bool.false_ne_true (h.2.1.symm.trans inside)).elim,
      fun h => (Bool.false_ne_true (h.2.1.symm.trans inside)).elim⟩
  refine ⟨x, y, cond, distinct, xOutside, yOutside, ?_⟩
  intro same
  apply differentAnswer
  rw [← members, ← dSeparated_false_iff_dConnected G distinct,
    ← dSeparated_false_iff_dConnected H distinct, same]

end

end OpenCausalScience.Papers.VermaPearl1990.ExecutableQuery
