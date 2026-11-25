module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! # Adjacencies and unshielded colliders from d-separation

Verma and Pearl (UAI 1990), Lemmas 1–2 and the necessary direction of
Theorem 1, in [Equivalence and Synthesis of Causal Models](https://arxiv.org/abs/1304.1108).
A missing edge has a d-separator among the parents of an endpoint. For an
unshielded triple, every separating set omits its middle exactly when it is a
collider. These facts determine the skeleton and unshielded colliders from
the singleton d-connection relation on labelled finite DAGs.
-/

namespace OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026
open BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Adjacency in the undirected skeleton. -/
def Adjacent (G : DAG n) (x y : Fin n) : Prop :=
  G.edge x y = true ∨ G.edge y x = true

private theorem adjacent_symm {G : DAG n} {x y : Fin n} :
    Adjacent G x y → Adjacent G y x := Or.symm

private theorem adjacent_distinct {G : DAG n} {x y : Fin n} (edge : Adjacent G x y) :
    x ≠ y := by
  intro same
  subst y
  have selfEdge : G.edge x x = true := by
    rcases edge with forward | backward
    · exact forward
    · exact backward
  exact G.no_directed_cycle x (.single selfEdge)

/-- The arrows of a triple meet head-to-head at its middle. -/
def HeadToHead (G : DAG n) (x middle y : Fin n) : Prop :=
  G.edge x middle = true ∧ G.edge y middle = true

/-- A head-to-head triple whose endpoints are distinct and nonadjacent. -/
def UnshieldedCollider (G : DAG n) (x middle y : Fin n) : Prop :=
  x ≠ y ∧ ¬ Adjacent G x y ∧ HeadToHead G x middle y

/-- Equivalence of graphical conditional independence for all singleton
queries and all Boolean conditioning predicates on the labelled vertices. -/
def SameDConnections (G H : DAG n) : Prop :=
  ∀ (member : Fin n → Bool) (x y : Fin n),
    DConnected (Conditioning.ofPredicate G member) x y ↔
      DConnected (Conditioning.ofPredicate H member) x y

private theorem adjacent_move {G : DAG n} {x y : Fin n} (edge : Adjacent G x y)
    (arrival : BayesBall.Direction) : ∃ departure, Move G (x, arrival) (y, departure) := by
  rcases edge with forward | backward
  · exact ⟨.down, forward⟩
  · exact ⟨.up, backward⟩

/-- A single edge is active for every conditioning set avoiding its endpoints. -/
theorem adjacent_dConnected {G : DAG n} (C : Conditioning G) {x y : Fin n}
    (edge : Adjacent G x y) (xOutside : C.member x = false)
    (yOutside : C.member y = false) : DConnected C x y := by
  obtain ⟨departure, move⟩ := adjacent_move edge .up
  have openStart : OpenTurn C (x, .up) departure := by simp [OpenTurn, xOutside]
  refine ⟨xOutside, yOutside, [y], departure, .cons ⟨move, openStart⟩ (.nil _), ?_⟩
  simp [adjacent_distinct edge]

def parentCondition (G : DAG n) (x : Fin n) : Conditioning G :=
  Conditioning.ofPredicate G (fun p => G.edge p x)

private theorem descendant_inactive (G : DAG n) {x v : Fin n}
    (descendant : G.DirectedWalk x v) : (parentCondition G x).activated v = false := by
  have after := G.rank_lt_of_directedWalk descendant
  apply Bool.eq_false_iff.mpr
  intro activation
  rcases Bool.or_eq_true_iff.mp activation with member | hit
  · have edge : G.edge v x = true := member
    have before := G.edge_increases _ _ edge
    omega
  · obtain ⟨p, parent, via⟩ := ((parentCondition G x).descendant_spec v).mp hit
    have edge : G.edge p x = true := parent
    have before := G.edge_increases _ _ edge
    have later := G.rank_lt_of_directedWalk via
    omega

private theorem downward_walk_preserves_descendance {G : DAG n} {x : Fin n}
    {start final : BayesBall.State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk (parentCondition G x) start visited final)
    (downward : start.2 = .down) (descendant : G.DirectedWalk x start.1) :
    G.DirectedWalk x final.1 := by
  induction walk with
  | nil _ => exact descendant
  | @cons start next final rest step _ ih =>
    cases departure : next.2 with
    | up =>
      have active : (parentCondition G x).activated start.1 = true := by
        simpa [OpenTurn, downward, departure] using step.2
      rw [descendant_inactive G descendant] at active
      cases active
    | down =>
      have edge : G.edge start.1 next.1 = true := by
        simpa [Move, departure] using step.1
      exact ih departure (.extend descendant edge)

private theorem walk_stops_at_conditioned_upward {G : DAG n} {C : Conditioning G}
    {start final : BayesBall.State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final) (upward : start.2 = .up)
    (conditioned : C.member start.1 = true) : final.1 = start.1 := by
  cases walk with
  | nil _ => rfl
  | cons step _ =>
    have unconditioned : C.member start.1 = false := by
      simpa [OpenTurn, upward] using step.2
    rw [conditioned] at unconditioned
    cases unconditioned

private theorem walk_from_parent_conditioned_vertex {G : DAG n} {x : Fin n}
    {final : BayesBall.State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk (parentCondition G x) (x, .up) visited final) :
    final.1 = x ∨ G.edge final.1 x = true ∨ G.DirectedWalk x final.1 := by
  cases walk with
  | nil => exact Or.inl rfl
  | @cons _ next _ _ first rest =>
    cases arrival : next.2 with
    | up =>
      have edge : G.edge next.1 x = true := by simpa [Move, arrival] using first.1
      have stopped := walk_stops_at_conditioned_upward rest arrival edge
      exact Or.inr (Or.inl (stopped.symm ▸ edge))
    | down =>
      have edge : G.edge x next.1 = true := by simpa [Move, arrival] using first.1
      exact Or.inr (Or.inr (downward_walk_preserves_descendance rest arrival (.single edge)))

/-- A vertex is d-separated by its parents from every distinct vertex which
is neither a parent nor its descendant. -/
theorem parents_dSeparate {G : DAG n} {x y : Fin n}
    (distinct : x ≠ y) (notParent : G.edge y x ≠ true)
    (notDescendant : ¬ G.DirectedWalk x y) :
    ¬ DConnected (parentCondition G x) x y := by
  rintro ⟨_, _, visited, arrival, walk, _⟩
  rcases walk_from_parent_conditioned_vertex walk with same | parent | descendant
  · exact distinct same.symm
  · exact notParent parent
  · exact notDescendant descendant

/-- A missing edge admits a separator avoiding both endpoints. The endpoint
with greater rank can be used as the source for the parent-set proof. -/
theorem nonadjacent_has_separator {G : DAG n} {x y : Fin n}
    (distinct : x ≠ y) (missing : ¬ Adjacent G x y) :
    (¬ DConnected (parentCondition G x) x y) ∨
      (¬ DConnected (parentCondition G y) y x) := by
  by_cases rankOrder : G.rank y ≤ G.rank x
  · exact Or.inl (parents_dSeparate distinct (fun edge => missing (.inr edge))
      (fun walk => Nat.not_lt_of_ge rankOrder (G.rank_lt_of_directedWalk walk)))
  · have opposite : G.rank x ≤ G.rank y := by omega
    exact Or.inr (parents_dSeparate (Ne.symm distinct) (fun edge => missing (.inl edge))
      (fun walk => Nat.not_lt_of_ge opposite (G.rank_lt_of_directedWalk walk)))

private theorem adjacent_in_equivalent_dag {G H : DAG n} (equivalent : SameDConnections G H)
    {x y : Fin n} (edge : Adjacent G x y) : Adjacent H x y := by
  by_cases present : Adjacent H x y
  · exact present
  · exfalso
    have xSelf : H.edge x x = false := by
      apply Bool.eq_false_iff.mpr
      exact fun self => H.no_directed_cycle x (.single self)
    have ySelf : H.edge y y = false := by
      apply Bool.eq_false_iff.mpr
      exact fun self => H.no_directed_cycle y (.single self)
    rcases nonadjacent_has_separator (adjacent_distinct edge) present with forward | backward
    · apply forward
      have yOutside := Bool.eq_false_iff.mpr (fun incoming => present (.inr incoming))
      exact (equivalent (fun p => H.edge p x) x y).mp (adjacent_dConnected _ edge xSelf yOutside)
    · apply backward
      have xOutside := Bool.eq_false_iff.mpr (fun incoming => present (.inl incoming))
      exact (equivalent (fun p => H.edge p y) y x).mp
        (adjacent_dConnected _ (adjacent_symm edge) ySelf xOutside)

/-- Verma–Pearl Lemma 1 as skeleton invariance. -/
theorem sameSkeleton_of_sameDConnections {G H : DAG n} (equivalent : SameDConnections G H) :
    ∀ x y, Adjacent G x y ↔ Adjacent H x y :=
  fun _ _ => ⟨adjacent_in_equivalent_dag equivalent,
    adjacent_in_equivalent_dag (fun member x y => (equivalent member x y).symm)⟩

private theorem triple_visits_distinct {G : DAG n} {x middle y : Fin n}
    (xMiddle : Adjacent G x middle) (yMiddle : Adjacent G y middle) (distinct : x ≠ y) :
    (x :: [middle, y]).Nodup := by
  simp [adjacent_distinct xMiddle, Ne.symm (adjacent_distinct yMiddle), distinct]

private theorem dConnected_through_conditioned_collider {G : DAG n} (C : Conditioning G)
    {x middle y : Fin n} (collider : HeadToHead G x middle y) (distinct : x ≠ y)
    (xOutside : C.member x = false) (yOutside : C.member y = false)
    (middleInside : C.member middle = true) : DConnected C x y := by
  have first : ActiveStep C (x, .up) (middle, .down) :=
    ⟨collider.1, by simp [OpenTurn, xOutside]⟩
  have second : ActiveStep C (middle, .down) (y, .up) :=
    ⟨collider.2, by simp [OpenTurn, Conditioning.activated, middleInside]⟩
  exact ⟨xOutside, yOutside, [middle, y], .up, .cons first (.cons second (.nil _)),
    triple_visits_distinct (.inl collider.1) (.inl collider.2) distinct⟩

private theorem dConnected_through_unconditioned_noncollider {G : DAG n} (C : Conditioning G)
    {x middle y : Fin n} (xMiddle : Adjacent G x middle) (yMiddle : Adjacent G y middle)
    (noncollider : ¬ HeadToHead G x middle y) (distinct : x ≠ y)
    (xOutside : C.member x = false) (yOutside : C.member y = false)
    (middleOutside : C.member middle = false) : DConnected C x y := by
  obtain ⟨firstDir, firstMove⟩ := adjacent_move xMiddle .up
  obtain ⟨secondDir, secondMove⟩ := adjacent_move (adjacent_symm yMiddle) firstDir
  have firstOpen : OpenTurn C (x, .up) firstDir := by simp [OpenTurn, xOutside]
  have secondOpen : OpenTurn C (middle, firstDir) secondDir := by
    have turn : ¬ (firstDir = .down ∧ secondDir = .up) := by
      rintro ⟨rfl, rfl⟩
      exact noncollider ⟨firstMove, secondMove⟩
    simpa [OpenTurn, turn] using middleOutside
  exact ⟨xOutside, yOutside, [middle, y], secondDir,
    .cons ⟨firstMove, firstOpen⟩ (.cons ⟨secondMove, secondOpen⟩ (.nil _)),
    triple_visits_distinct xMiddle yMiddle distinct⟩

/-- Verma–Pearl Lemma 2 for a separating set of an unshielded triple.
The middle is omitted exactly when the triple is head-to-head. -/
theorem middle_omitted_iff_headToHead_of_separating {G : DAG n} (C : Conditioning G)
    {x middle y : Fin n} (xMiddle : Adjacent G x middle) (yMiddle : Adjacent G y middle)
    (distinct : x ≠ y) (xOutside : C.member x = false) (yOutside : C.member y = false)
    (separated : ¬ DConnected C x y) : C.member middle = false ↔ HeadToHead G x middle y := by
  constructor
  · intro outside
    by_cases collider : HeadToHead G x middle y
    · exact collider
    · exact (separated (dConnected_through_unconditioned_noncollider C xMiddle yMiddle
        collider distinct xOutside yOutside outside)).elim
  · intro collider
    apply Bool.eq_false_iff.mpr
    exact fun inside => separated
      (dConnected_through_conditioned_collider C collider distinct xOutside yOutside inside)

private theorem unshieldedCollider_in_equivalent_dag {G H : DAG n}
    (equivalent : SameDConnections G H) {x middle y : Fin n}
    (collider : UnshieldedCollider G x middle y) : UnshieldedCollider H x middle y := by
  obtain ⟨distinct, missing, arrows⟩ := collider
  have skeleton := sameSkeleton_of_sameDConnections equivalent
  have xMiddle : Adjacent G x middle := Or.inl arrows.1
  have yMiddle : Adjacent G y middle := Or.inl arrows.2
  have transfer {source target : Fin n} (member : Fin n → Bool)
      (sourceMiddle : Adjacent G source middle) (targetMiddle : Adjacent G target middle)
      (different : source ≠ target) (sourceOutside : member source = false)
      (targetOutside : member target = false) (headToHead : HeadToHead G source middle target)
      (separated : ¬ DConnected (Conditioning.ofPredicate G member) source target) :
      HeadToHead H source middle target := by
    have outside : member middle = false :=
      (middle_omitted_iff_headToHead_of_separating _ sourceMiddle targetMiddle
        different sourceOutside targetOutside separated).mpr headToHead
    have alsoSeparated : ¬ DConnected (Conditioning.ofPredicate H member) source target :=
      fun connection => separated ((equivalent member source target).mpr connection)
    exact (middle_omitted_iff_headToHead_of_separating _ ((skeleton _ _).mp sourceMiddle)
      ((skeleton _ _).mp targetMiddle) different sourceOutside targetOutside alsoSeparated).mp outside
  refine ⟨distinct, fun edge => missing ((skeleton _ _).mpr edge), ?_⟩
  rcases nonadjacent_has_separator distinct missing with forward | backward
  · exact transfer (fun p => G.edge p x) xMiddle yMiddle distinct
      (Bool.eq_false_iff.mpr (fun edge => G.no_directed_cycle x (.single edge)))
      (Bool.eq_false_iff.mpr (fun edge => missing (.inr edge))) arrows forward
  · have opposite := transfer (fun p => G.edge p y) yMiddle xMiddle distinct.symm
      (Bool.eq_false_iff.mpr (fun edge => G.no_directed_cycle y (.single edge)))
      (Bool.eq_false_iff.mpr (fun edge => missing (.inl edge))) ⟨arrows.2, arrows.1⟩ backward
    exact ⟨opposite.2, opposite.1⟩

/-- Verma–Pearl Lemma 2 as invariance of unshielded colliders. -/
theorem sameUnshieldedColliders_of_sameDConnections {G H : DAG n}
    (equivalent : SameDConnections G H) :
    ∀ x middle y, UnshieldedCollider G x middle y ↔ UnshieldedCollider H x middle y :=
  fun _ _ _ => ⟨unshieldedCollider_in_equivalent_dag equivalent,
    unshieldedCollider_in_equivalent_dag (fun member x y => (equivalent member x y).symm)⟩

/-- The necessary direction of Verma–Pearl Theorem 1 on finite DAGs. -/
theorem sameSkeleton_and_sameUnshieldedColliders_of_sameDConnections {G H : DAG n}
    (equivalent : SameDConnections G H) :
    (∀ x y, Adjacent G x y ↔ Adjacent H x y) ∧
      (∀ x middle y, UnshieldedCollider G x middle y ↔ UnshieldedCollider H x middle y) :=
  ⟨sameSkeleton_of_sameDConnections equivalent,
    sameUnshieldedColliders_of_sameDConnections equivalent⟩

def adjacentTest (G : DAG n) (x y : Fin n) : Bool :=
  G.edge x y || G.edge y x

def unshieldedTest (G : DAG n) (x middle y : Fin n) : Bool :=
  (x != y) && !adjacentTest G x y && G.edge x middle && G.edge y middle

private theorem adjacentTest_true (G : DAG n) (x y : Fin n) :
    adjacentTest G x y = true ↔ Adjacent G x y :=
  Bool.or_eq_true_iff

private theorem unshieldedTest_true (G : DAG n) (x middle y : Fin n) :
    unshieldedTest G x middle y = true ↔ UnshieldedCollider G x middle y := by
  simp [unshieldedTest, adjacentTest, Adjacent, UnshieldedCollider, HeadToHead, and_assoc]

private theorem bool_beq_iff_true (a b : Bool) :
    (a == b) = true ↔ (a = true ↔ b = true) := by cases a <;> cases b <;> decide

/-- Compare the skeleton and unshielded collider indicators for two labelled
DAGs. This expresses the signature compared by the CGA DAG-equivalence API. -/
def signaturesMatch (G H : DAG n) : Bool :=
  let vertices := List.finRange n
  (vertices.all fun x => vertices.all fun y => adjacentTest G x y == adjacentTest H x y) &&
    (vertices.all fun x => vertices.all fun middle => vertices.all fun y =>
      unshieldedTest G x middle y == unshieldedTest H x middle y)

theorem signaturesMatch_iff (G H : DAG n) :
    signaturesMatch G H = true ↔
      (∀ x y, Adjacent G x y ↔ Adjacent H x y) ∧
      (∀ x middle y, UnshieldedCollider G x middle y ↔ UnshieldedCollider H x middle y) := by
  simp only [signaturesMatch, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    bool_beq_iff_true, adjacentTest_true, unshieldedTest_true]

theorem signaturesMatch_of_sameDConnections {G H : DAG n} (equivalent : SameDConnections G H) :
    signaturesMatch G H = true :=
  (signaturesMatch_iff G H).mpr
    (sameSkeleton_and_sameUnshieldedColliders_of_sameDConnections equivalent)

/-- A rejected signature guarantees a conditioning query answered
differently by the two graphs. -/
theorem distinguishing_query_of_signaturesMismatch {G H : DAG n}
    (mismatch : signaturesMatch G H = false) :
    ∃ (member : Fin n → Bool) (x y : Fin n),
      ¬ (DConnected (Conditioning.ofPredicate G member) x y ↔
        DConnected (Conditioning.ofPredicate H member) x y) := by
  classical
  by_cases found : ∃ (member : Fin n → Bool) (x y : Fin n),
      ¬ (DConnected (Conditioning.ofPredicate G member) x y ↔
        DConnected (Conditioning.ofPredicate H member) x y)
  · exact found
  · exfalso
    have equivalent : SameDConnections G H := by
      intro member x y
      exact Classical.byContradiction (fun disagree => found ⟨member, x, y, disagree⟩)
    rw [signaturesMatch_of_sameDConnections equivalent] at mismatch
    cases mismatch

end

end OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
