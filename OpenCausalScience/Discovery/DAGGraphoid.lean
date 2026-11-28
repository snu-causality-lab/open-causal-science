module
public import OpenCausalScience.Discovery.OrderBoundary
public import OpenCausalScience.Papers.SadeghiLauritzen2014.Markov

/-! # Faithfulness and the graphoid axioms on finite DAGs

Embed a DAG into the marked mixed-graph type. The mixed-graph active walk
uses the same turns as the directional search on a DAG. Faithful CI
therefore inherits intersection and composition from Sadeghi and Lauritzen
(2014), Theorem 1. -/

namespace OpenCausalScience.Discovery

open Probability.CI Moralization
open Papers.KimEtAl2026.BayesBall
open Papers.KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Represent each DAG arrow as one mixed-graph edge with one head. -/
def dagAsMixed (G : DAG n) : MixedGraph n where
  edge u a v b := match a, b with
    | false, true => G.edge u v
    | true, false => G.edge v u
    | _, _ => false
  symmetric u a v b := by cases a <;> cases b <;> rfl
  loop_free u a b := by
    have noLoop : G.edge u u = false := Bool.eq_false_iff.mpr fun edge => G.no_directed_cycle u (.single edge)
    cases a <;> cases b <;> simp [noLoop]
  no_arrow_of_undirected := by intro _ _ _ _ undirected; contradiction

private theorem walk_prepend {G : DAG n} {u v w : Fin n} (edge : G.edge u v = true)
    (path : G.DirectedWalk v w) : G.DirectedWalk u w := by
  induction path with
  | single last => exact .extend (.single edge) last
  | extend _ last ih => exact .extend ih last

private theorem path_into_mixed_ancestry {G : DAG n} {Z : Mask n} {u v : Fin n}
    (path : G.DirectedWalk u v) (tail : (dagAsMixed G).AncestorOf Z v) :
    (dagAsMixed G).AncestorOf Z u := by
  induction path with
  | single arrow => exact .parent arrow tail
  | extend _ arrow ih => exact ih (.parent arrow tail)

private theorem hits_conditioned_iff_ancestor (G : DAG n) (Z : Mask n) (u : Fin n) :
    (Conditioning.ofPredicate G Z).activated u = true ↔ (dagAsMixed G).AncestorOf Z u := by
  let C := Conditioning.ofPredicate G Z
  change C.activated u = true ↔ _
  constructor
  · rw [Conditioning.activated, Bool.or_eq_true_iff, C.descendant_spec]
    rintro (here | ⟨w, member, path⟩)
    · exact .conditioned here
    · exact path_into_mixed_ancestry path (.conditioned member)
  · intro ancestor
    have witness : ∃ w, Z w = true ∧ (u = w ∨ G.DirectedWalk u w) := by
      induction ancestor with
      | conditioned member => exact ⟨_, member, .inl rfl⟩
      | parent arrow _ ih =>
        obtain ⟨w, member, rfl | path⟩ := ih
        · exact ⟨_, member, .inr (.single arrow)⟩
        · exact ⟨w, member, .inr (walk_prepend arrow path)⟩
    rw [Conditioning.activated, Bool.or_eq_true_iff, C.descendant_spec]
    obtain ⟨w, member, rfl | path⟩ := witness
    · exact .inl member
    · exact .inr ⟨w, member, path⟩

private def toDirection (head : Bool) : Direction := if head then .down else .up

private def toMark (dir : Direction) : Bool := match dir with
  | .up => false
  | .down => true

private def toArrival (state : State (Fin n)) : MixedGraph.Arrival n := (state.1, toMark state.2)

private def toState (state : MixedGraph.Arrival n) : State (Fin n) := (state.1, toDirection state.2)

private theorem state_roundtrip (s : MixedGraph.Arrival n) : toArrival (toState s) = s := by
  obtain ⟨u, mark⟩ := s
  cases mark <;> rfl

private theorem direction_roundtrip (s : State (Fin n)) : toState (toArrival s) = s := by
  obtain ⟨u, direction⟩ := s
  cases direction <;> rfl

private theorem edge_between_iff (G : DAG n) (x : Fin n) (s : State (Fin n)) :
    (∃ mark, (dagAsMixed G).edge x mark s.1 (toMark s.2) = true) ↔ Move G (x, .up) s := by
  rcases s with ⟨v, dir⟩
  cases dir <;> constructor
  · rintro ⟨mark, edge⟩
    cases mark <;> simp_all [dagAsMixed, Move, toMark]
  · intro edge
    exact ⟨true, edge⟩
  · rintro ⟨mark, edge⟩
    cases mark <;> simp_all [dagAsMixed, Move, toMark]
  · intro edge
    exact ⟨false, edge⟩

private theorem dag_step_iff (G : DAG n) (Z : Mask n) (s t : State (Fin n)) :
    (dagAsMixed G).Step Z (toArrival s) (toArrival t) ↔
      ActiveStep (Conditioning.ofPredicate G Z) s t := by
  rcases s with ⟨x, start⟩
  rcases t with ⟨y, finish⟩
  have ancestor := hits_conditioned_iff_ancestor G Z x
  constructor
  · cases start <;> cases finish <;>
      rintro ⟨outgoing, edge, turn⟩ <;> cases outgoing <;>
      simp_all [MixedGraph.openTurn, toArrival, toMark, dagAsMixed, ActiveStep, Move, OpenTurn, Conditioning.ofPredicate]
  · rintro ⟨edge, turn⟩
    refine ⟨!toMark finish, ?_, ?_⟩
    · cases finish <;> exact edge
    · cases start <;> cases finish <;>
        simp_all [MixedGraph.openTurn, toArrival, toMark, dagAsMixed, OpenTurn, Conditioning.ofPredicate]

private theorem mixed_walk_of_dag {G : DAG n} {Z : Mask n}
    {s t : State (Fin n)} {visited : List (Fin n)}
    (path : ActiveWalk (Conditioning.ofPredicate G Z) s visited t) :
    (dagAsMixed G).ActiveWalk Z (toArrival s) visited (toArrival t) := by
  induction path with
  | nil => exact .nil _
  | cons next _ ih => exact .cons ((dag_step_iff G Z _ _).mpr next) ih

private theorem dag_walk_of_mixed {G : DAG n} {Z : Mask n}
    {s t : MixedGraph.Arrival n} {visited : List (Fin n)}
    (path : (dagAsMixed G).ActiveWalk Z s visited t) :
    ActiveWalk (Conditioning.ofPredicate G Z) (toState s) visited (toState t) := by
  induction path with
  | nil => exact .nil _
  | cons next _ ih =>
    apply ActiveWalk.cons _ ih
    apply (dag_step_iff G Z _ _).mp
    simpa only [state_roundtrip] using next

/-- The DAG query and the corresponding mixed graph have the same open walks
between disjoint sets whose members are outside the conditioning set. -/
theorem dag_connection_iff_mixed_walk (G : DAG n) (X Y Z : Mask n)
    (disjoint : Disjoint3 X Y Z) :
    (show Query G from ⟨X, Y, Conditioning.ofPredicate G Z⟩).DConnection ↔
      (dagAsMixed G).WalkConnected X Y Z := by
  constructor
  · rintro ⟨x, y, inX, inY, _, _, visited, direction, path, _⟩
    cases path with
    | nil =>
      have noY := disjoint.1 x inX
      exact (Bool.false_ne_true (noY.symm.trans inY)).elim
    | @cons _ start final _ first rest =>
      obtain ⟨mark, edge⟩ := (edge_between_iff G x start).mpr first.1
      exact ⟨toArrival start, toArrival (y, direction), ⟨x, mark, inX, edge⟩,
        MixedGraph.reachable_iff_active_walk.mpr ⟨_, mixed_walk_of_dag rest⟩, inY⟩
  · rintro ⟨s, t, ⟨x, mark, inX, edge⟩, path, inY⟩
    obtain ⟨visited, rest⟩ := MixedGraph.reachable_iff_active_walk.mp path
    let C := Conditioning.ofPredicate G Z
    have first : ActiveStep C (x, .up) (toState s) := by
      have motion := (edge_between_iff G x (toState s)).mp ⟨mark, by
        change (dagAsMixed G).edge x mark (toArrival (toState s)).1 (toArrival (toState s)).2 = true
        simpa only [state_roundtrip] using edge⟩
      exact ⟨motion, by simpa [C, OpenTurn, Conditioning.ofPredicate] using disjoint.2.1 x inX⟩
    have walk := (ActiveWalk.cons first (dag_walk_of_mixed rest))
    refine ⟨x, t.1, inX, inY, ?_⟩
    apply (corrected_reachable_iff_dconnected C (disjoint.2.1 x inX) (disjoint.2.2 t.1 inY)).mp
    exact ⟨(toState t).2, (corrected_reachable_iff_active_walk C).mpr ⟨_, walk⟩⟩

/-- Agreement with d-separation for disjoint variable sets. -/
def DAGFaithful (G : DAG n) (J : Relation n) : Prop :=
  ∀ X Y Z, Disjoint3 X Y Z →
    (J X Y Z ↔ ¬ (show Query G from ⟨X, Y, Conditioning.ofPredicate G Z⟩).DConnection)

/-- For a faithful CI relation, the graph's separation oracle answers every
valid singleton query with the corresponding CI statement. -/
theorem graph_oracle_matches_faithful {G : DAG n} {J : Relation n}
    (faithful : DAGFaithful G J) : MatchesOracle J (graphOracle G) := by
  intro x y Z different xOutside yOutside
  let Q : Query G := ⟨single x, single y, Conditioning.ofPredicate G Z⟩
  have outsideLeft : Disjoint (single x) Z := by
    intro v hx
    have same : v = x := by simpa [single] using hx
    simpa [same] using xOutside
  have outsideRight : Disjoint (single y) Z := by
    intro v hy
    have same : v = y := by simpa [single] using hy
    simpa [same] using yOutside
  have separate : Disjoint (single x) (single y) := by
    intro v hx
    have same : v = x := by simpa [single] using hx
    exact Bool.eq_false_iff.mpr (fun hy => different (same.symm.trans (beq_iff_eq.mp hy)))
  exact (Q.dagMoralSeparated_eq_true_iff outsideLeft outsideRight).trans
    (faithful (single x) (single y) Z ⟨separate, outsideLeft, outsideRight⟩).symm

private theorem faithful_iff_m_independent {G : DAG n} {J : Relation n} (faithful : DAGFaithful G J)
    {X Y Z : Mask n} (disjoint : Disjoint3 X Y Z) :
    J X Y Z ↔ (dagAsMixed G).MIndependent X Y Z :=
  (faithful X Y Z disjoint).trans (not_congr (dag_connection_iff_mixed_walk G X Y Z disjoint))

private theorem disjoint_union_left {A B C : Mask n} (ac : Disjoint A C) (bc : Disjoint B C) :
    Disjoint (union A B) C :=
  fun v hv => (Bool.or_eq_true_iff.mp hv).elim (ac v) (bc v)

private theorem disjoint_union_right {A B C : Mask n} (ab : Disjoint A B) (ac : Disjoint A C) :
    Disjoint A (union B C) := (disjoint_union_left ab.symm ac.symm).symm

/-- A faithful semigraphoid CI relation is a graphoid. -/
theorem faithful_graphoid {G : DAG n} {J : Relation n} (faithful : DAGFaithful G J)
    (sg : Semigraphoid J) : Graphoid J where
  toSemigraphoid := sg
  intersection {X Y W Z} disjoint hY hW := by
    obtain ⟨⟨xy, xw, yw⟩, xz, yz, wz⟩ := disjoint
    have dY : Disjoint3 X Y (union Z W) := ⟨xy, disjoint_union_right xz xw, disjoint_union_right yz yw⟩
    have dW : Disjoint3 X W (union Z Y) := ⟨xw, disjoint_union_right xz xy, disjoint_union_right wz yw.symm⟩
    have dAll : Disjoint3 X (union Y W) Z := ⟨disjoint_union_right xy xw, xz, disjoint_union_left yz wz⟩
    exact (faithful_iff_m_independent faithful dAll).mpr
      (MixedGraph.m_independent_intersection ((faithful_iff_m_independent faithful dY).mp hY)
        ((faithful_iff_m_independent faithful dW).mp hW))

/-- A CI relation faithful to a DAG is closed under composition of disjoint
variable sets. -/
theorem faithful_composition {G : DAG n} {J : Relation n} (faithful : DAGFaithful G J)
    ⦃X Y W Z : Mask n⦄ (disjoint : Disjoint4 X Y W Z) (hY : J X Y Z) (hW : J X W Z) :
    J X (union Y W) Z := by
  obtain ⟨⟨xy, xw, _⟩, xz, yz, wz⟩ := disjoint
  have dAll : Disjoint3 X (union Y W) Z := ⟨disjoint_union_right xy xw, xz, disjoint_union_left yz wz⟩
  exact (faithful_iff_m_independent faithful dAll).mpr
    (MixedGraph.m_independent_union_iff.mpr
      ⟨(faithful_iff_m_independent faithful ⟨xy, xz, yz⟩).mp hY,
        (faithful_iff_m_independent faithful ⟨xw, xz, wz⟩).mp hW⟩)

end

end OpenCausalScience.Discovery
