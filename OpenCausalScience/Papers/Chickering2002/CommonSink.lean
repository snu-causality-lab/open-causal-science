module
public import OpenCausalScience.Discovery.DAGGraphoid
public import OpenCausalScience.Papers.Chickering2002.DeletionIndependence

/-! # Independence maps with a common sink

Chickering (2002), Appendix A, Lemma 25 and Step 4 of Lemma 30.
The lifted comparison uses ordered local Markov statements. -/

namespace OpenCausalScience.Papers.Chickering2002

open Discovery Probability.CI RaskuttiUhler2018 Moralization
open VermaPearl1990.DAGEquivalence
open KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

def GraphCI (G : DAG n) : Relation n := fun A B C =>
  ¬ (show Query G from ⟨A, B, Conditioning.ofPredicate G C⟩).DConnection

private theorem trim_endpoints {G : DAG n} (A B C : Mask n) :
    GraphCI G A B C ↔ GraphCI G (diff A C) (diff B C) C := by
  unfold GraphCI
  apply not_congr
  constructor
  · rintro ⟨x, y, inA, inB, path⟩
    have xOff : C x = false := path.1
    have yOff : C y = false := path.2.1
    change A x = true at inA
    change B y = true at inB
    exact ⟨x, y, by simp [diff, inA, xOff], by simp [diff, inB, yOff], path⟩
  · rintro ⟨x, y, inA, inB, path⟩
    exact ⟨x, y, (Bool.and_eq_true_iff.mp inA).1, (Bool.and_eq_true_iff.mp inB).1, path⟩

private theorem union_disjoint_left {A B C : Mask n} (ac : Disjoint A C) (bc : Disjoint B C) :
    Disjoint (union A B) C := fun v hv => (Bool.or_eq_true_iff.mp hv).elim (ac v) (bc v)

private theorem union_disjoint_right {A B C : Mask n} (ab : Disjoint A B) (ac : Disjoint A C) :
    Disjoint A (union B C) := (union_disjoint_left ab.symm ac.symm).symm

private theorem ci_iff_m_independent (G : DAG n) {A B C : Mask n} (apart : Disjoint3 A B C) :
    GraphCI G A B C ↔ (dagAsMixed G).MIndependent A B C :=
  not_congr (dag_connection_iff_mixed_walk G A B C apart)

private theorem graph_ci_semigraphoid (G : DAG n) : Semigraphoid (GraphCI G) where
  empty_right := by
    intro X Z connected
    obtain ⟨_, _, _, impossible, _⟩ := connected
    contradiction
  symmetry := by
    intro A B C h
    apply (trim_endpoints B A C).mpr
    have narrowed := (trim_endpoints A B C).mp h
    have offA := disjoint_diff_right A C
    have offB := disjoint_diff_right B C
    have apart : Disjoint (diff A C) (diff B C) := by
      intro v inA
      apply Bool.eq_false_iff.mpr
      intro inB
      have outside := offA v inA
      exact narrowed ⟨v, v, inA, inB, outside, outside, [], .up, .nil _, by simp⟩
    exact (ci_iff_m_independent G ⟨apart.symm, offB, offA⟩).mpr
      (MixedGraph.m_independent_symmetry offA offB apart
        ((ci_iff_m_independent G ⟨apart, offA, offB⟩).mp narrowed))
  decomposition := by
    intro A B D C apart sep
    obtain ⟨⟨ab, ad, _⟩, ac, bc, dc⟩ := apart
    have joined := (ci_iff_m_independent G ⟨union_disjoint_right ab ad, ac, union_disjoint_left bc dc⟩).mp sep
    exact (ci_iff_m_independent G ⟨ab, ac, bc⟩).mpr (MixedGraph.m_independent_union_iff.mp joined).1
  weak_union := by
    intro A B D C apart sep
    obtain ⟨⟨ab, ad, bd⟩, ac, bc, dc⟩ := apart
    have joined := (ci_iff_m_independent G ⟨union_disjoint_right ab ad, ac, union_disjoint_left bc dc⟩).mp sep
    exact (ci_iff_m_independent G ⟨ab, union_disjoint_right ac ad, union_disjoint_right bc bd⟩).mpr
      (MixedGraph.m_independent_weak_union joined)
  contraction := by
    intro A B D C apart left right
    obtain ⟨⟨ab, ad, bd⟩, ac, bc, dc⟩ := apart
    exact (ci_iff_m_independent G ⟨union_disjoint_right ab ad, ac, union_disjoint_left bc dc⟩).mpr
      (MixedGraph.m_independent_contraction ((ci_iff_m_independent G ⟨ab, ac, bc⟩).mp left)
        ((ci_iff_m_independent G ⟨ad, union_disjoint_right ac ab, union_disjoint_right dc bd.symm⟩).mp right))

theorem graph_ci_graphoid (G : DAG n) : Graphoid (GraphCI G) :=
  faithful_graphoid (fun _ _ _ _ => Iff.rfl : DAGFaithful G (GraphCI G)) (graph_ci_semigraphoid G)

/-- Vertex `s` has no children. -/
def IsSink (G : DAG n) (s : Fin n) : Prop := ∀ v, G.edge s v = false

private theorem sink_no_directed_walk {G : DAG n} {s v : Fin n} (sink : IsSink G s)
    (path : G.DirectedWalk s v) : False := by
  induction path with
  | single h => exact Bool.false_ne_true ((sink _).symm.trans h)
  | extend _ _ ih => exact ih

private theorem no_self_arrow (G : DAG n) (v : Fin n) : G.edge v v = false :=
  Bool.eq_false_iff.mpr (fun arrow => G.no_directed_cycle v (.single arrow))

private theorem single_off {x : Fin n} {A : Mask n} (off : A x = false) : Disjoint (single x) A := by
  intro v hv
  obtain rfl := beq_iff_eq.mp hv
  exact off

private theorem graph_ci_parent_set (G : DAG n) (v : Fin n) (U : Mask n) (away : U v = false)
    (nondescendants : ∀ w, U w = true → ¬ G.DirectedWalk v w) :
    GraphCI G (single v) (diff U fun u => G.edge u v) (fun u => G.edge u v) := by
  rintro ⟨x, y, atX, atY, path⟩
  have same : x = v := beq_iff_eq.mp atX
  subst x
  have inU := (Bool.and_eq_true_iff.mp atY).1
  have different : v ≠ y := by intro eq; subst y; simp [away] at inU
  have nonparent := Bool.eq_false_iff.mp (disjoint_diff_right U (fun u => G.edge u v) y atY)
  exact parents_dSeparate different nonparent (nondescendants y inU) path

/-- Move the chosen sink after all other vertices in a topological ranking. -/
def sinkLastRank (G : DAG n) (s v : Fin n) : Nat :=
  if v = s then n else (topologicalOrder G).idxOf v

private theorem idx_bound (G : DAG n) (v : Fin n) : (topologicalOrder G).idxOf v < n := by
  have complete := topological_order_perm G
  have bound := List.idxOf_lt_length_iff.mpr (complete.mem_iff.mpr (List.mem_finRange v))
  simpa [complete.length_eq] using bound

private theorem sink_last_injective (G : DAG n) (s : Fin n) (u v : Fin n)
    (same : sinkLastRank G s u = sinkLastRank G s v) : u = v := by
  by_cases su : u = s
  · by_cases sv : v = s
    · exact su.trans sv.symm
    · simp [sinkLastRank, su, sv] at same
      have bound := idx_bound G v
      omega
  · by_cases sv : v = s
    · simp [sinkLastRank, su, sv] at same
      have bound := idx_bound G u
      omega
    · apply idxOf_injective (topological_order_perm G)
      simpa [sinkLastRank, su, sv] using same

private theorem sink_last_topological {G : DAG n} {s : Fin n} (sink : IsSink G s)
    (u v : Fin n) (edge : G.edge u v = true) : sinkLastRank G s u < sinkLastRank G s v := by
  have su : u ≠ s := by
    intro eq
    subst u
    exact Bool.false_ne_true ((sink _).symm.trans edge)
  by_cases sv : v = s
  · simpa [sinkLastRank, su, sv] using idx_bound G u
  · simpa [sinkLastRank, su, sv] using topological_order_increases G u v edge

private theorem sink_last_predecessors (G : DAG n) (s : Fin n) :
    predecessors (sinkLastRank G s) s = fun v => v != s := by
  funext v
  by_cases same : v = s
  · subst v
    simp [predecessors]
  · simp [predecessors, sinkLastRank, same, idx_bound]

private theorem topological_walk {G : DAG n} (order : Fin n → Nat)
    (topo : ∀ u v, G.edge u v = true → order u < order v) {u v : Fin n}
    (walk : G.DirectedWalk u v) : order u < order v := by
  induction walk with
  | single edge => exact topo _ _ edge
  | extend _ edge ih => exact Nat.lt_trans ih (topo _ _ edge)

/-- Comparisons after omitting the common sink from endpoints and conditioning. -/
def IndependenceMapAway (s : Fin n) (G H : DAG n) : Prop :=
  ∀ (Z : Mask n) (x y : Fin n), x ≠ s → y ≠ s → Z s = false →
    DConnected (Conditioning.ofPredicate G Z) x y → DConnected (Conditioning.ofPredicate H Z) x y

/-- With a common sink, preservation away from the sink and inclusion of its
parent sets suffice for the full independence-map relation. -/
theorem common_sink_lift {G H : DAG n} {s : Fin n} (sinkG : IsSink G s) (sinkH : IsSink H s)
    (outside : IndependenceMapAway s G H)
    (parentsIncluded : ∀ p, G.edge p s = true → H.edge p s = true) : IndependenceMap G H := by
  let order := sinkLastRank H s
  let J := GraphCI G
  have g : Graphoid J := graph_ci_graphoid G
  have topo := sink_last_topological sinkH
  have agrees : MatchesOracle J (graphOracle G) :=
    graph_oracle_matches_faithful (fun _ _ _ _ => Iff.rfl : DAGFaithful G J)
  apply markov_of_ordered_local g.toSemigraphoid agrees order (sink_last_injective H s) topo
  intro v
  let U := predecessors order v
  let P : Mask n := fun u => H.edge u v
  have vOff : U v = false := by simp [U, predecessors]
  have pSub : Subset P U := fun p edge => decide_eq_true (topo p v edge)
  change GraphCI G (single v) (diff U P) P
  by_cases isSink : v = s
  · subst v
    let A : Mask n := fun u => G.edge u s
    have old : GraphCI G (single s) (diff U A) A :=
      graph_ci_parent_set G s U vOff (fun _ _ walk => sink_no_directed_walk sinkG walk)
    have included : Subset A P := parentsIncluded
    have off : Disjoint (single s) U := single_off vOff
    have subA := included.trans pSub
    have split : union (diff U P) (diff P A) = diff U A := by
      funext w
      cases hp : P w
      · have ha : A w = false := Bool.eq_false_iff.mpr (fun ha => Bool.false_ne_true (hp.symm.trans (included w ha)))
        simp [union, diff, hp, ha]
      · simp [union, diff, hp, pSub w hp]
    have apart : Disjoint4 (single s) (diff U P) (diff P A) A :=
      ⟨⟨off.restrict_right (subset_diff_left _ _), off.restrict_right ((subset_diff_left _ _).trans pSub),
        (disjoint_diff_right _ _).restrict_right (subset_diff_left _ _)⟩,
        off.restrict_right subA, (disjoint_diff_right _ _).restrict_right included, disjoint_diff_right _ _⟩
    have weak := g.weak_union apart (by rw [split]; exact old)
    rwa [union_eq_of_subset_diff included] at weak
  · have sOff : U s = false := by
      have bound := idx_bound H v
      simp [U, predecessors, order, sinkLastRank, isSink]
      omega
    have pOff : P s = false := sinkH v
    have inH : GraphCI H (single v) (diff U P) P :=
      graph_ci_parent_set H v U vOff (fun w yes walk =>
        (Nat.not_lt_of_ge (Nat.le_of_lt (of_decide_eq_true yes))) (topological_walk order topo walk))
    rintro ⟨x, y, hx, hy, path⟩
    have eq : x = v := beq_iff_eq.mp hx
    subst x
    have inU := (Bool.and_eq_true_iff.mp hy).1
    have yOutside : y ≠ s := by intro eq; subst y; rw [sOff] at inU; contradiction
    exact inH ⟨v, y, hx, hy, outside P v y isSink yOutside pOff path⟩


private theorem walk_of_away_edge_eq {G H : DAG n} {s u v : Fin n} (sink : IsSink G s)
    (same : ∀ a b, a ≠ s → b ≠ s → G.edge a b = H.edge a b)
    (vOff : v ≠ s) (walk : G.DirectedWalk u v) : H.DirectedWalk u v := by
  induction walk with
  | single edge =>
    have notSink : u ≠ s := by
      intro eq
      subst u
      exact Bool.false_ne_true ((sink _).symm.trans edge)
    exact .single ((same _ _ notSink vOff).symm.trans edge)
  | @extend mid target _ edge ih =>
    have notSink : mid ≠ s := by
      intro eq
      subst mid
      exact Bool.false_ne_true ((sink _).symm.trans edge)
    exact .extend (ih notSink) ((same _ _ notSink vOff).symm.trans edge)

/-- Changing a sink's incoming arrows preserves every comparison that
mentions the remaining vertices only. -/
theorem independence_away_of_same_edges {G H : DAG n} {s : Fin n} (sink : IsSink G s)
    (same : ∀ u v, u ≠ s → v ≠ s → G.edge u v = H.edge u v) : IndependenceMapAway s G H := by
  intro Z x y xOff yOff zOff connected
  let A : Query G := ⟨single x, single y, Conditioning.ofPredicate G Z⟩
  let B : Query H := ⟨single x, single y, Conditioning.ofPredicate H Z⟩
  have landsOff {w : Fin n} (mem : single x w = true ∨ single y w = true ∨ Z w = true) : w ≠ s := by
    intro eq
    subst w
    rcases mem with left | right | conditioned
    · exact xOff (beq_iff_eq.mp left).symm
    · exact yOff (beq_iff_eq.mp right).symm
    · simp [zOff] at conditioned
  have relevant {w : Fin n} (inG : A.relevant w) : w ≠ s ∧ B.relevant w := by
    obtain ⟨v, mem, rfl | path⟩ := (A.relevant_iff w).mp inG
    · exact ⟨landsOff mem, (B.relevant_iff _).mpr ⟨_, mem, .inl rfl⟩⟩
    · refine ⟨?_, (B.relevant_iff _).mpr ⟨_, mem, .inr (walk_of_away_edge_eq sink same (landsOff mem) path)⟩⟩
      intro eq
      subst w
      exact sink_no_directed_walk sink path
  have lift {u v : Fin n} (e : A.MoralEdge u v) : B.MoralEdge u v := by
    have ⟨notU, relU⟩ := relevant e.sourceRelevant
    have ⟨notV, relV⟩ := relevant e.targetRelevant
    refine ⟨relU, relV, e.sourceOutside, e.targetOutside, e.distinct, ?_⟩
    rcases e.connection with arrow | arrow | ⟨c, rel, xArrow, yArrow⟩
    · exact .inl ((same u v notU notV).symm.trans arrow)
    · exact .inr (.inl ((same v u notV notU).symm.trans arrow))
    · have ⟨notC, relC⟩ := relevant rel
      exact .inr (.inr ⟨c, relC, (same u c notU notC).symm.trans xArrow, (same v c notV notC).symm.trans yArrow⟩)
  have liftWalk {u v : Fin n} (route : A.MoralWalk u v) : B.MoralWalk u v := by
    induction route with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons (lift edge) ih
  have zLeft : Disjoint (single x) Z := single_off connected.1
  have zRight : Disjoint (single y) Z := single_off connected.2.1
  have joined : A.DConnection := ⟨x, y, by simp [A, single], by simp [A, single], connected⟩
  obtain ⟨u, v, hx, hy, route⟩ := (A.dConnection_iff_moralConnection zLeft zRight).mp joined
  obtain ⟨u', v', hx', hy', route'⟩ := (B.dConnection_iff_moralConnection zLeft zRight).mpr
    ⟨u, v, hx, hy, liftWalk route⟩
  have sourceEq : u' = x := beq_iff_eq.mp hx'
  have targetEq : v' = y := beq_iff_eq.mp hy'
  simpa [sourceEq, targetEq] using route'

/-- Inclusion preserves every arrow into a sink in the containing DAG. -/
theorem parent_subset_of_map_at_sink {G H : DAG n} {s : Fin n} (sinkH : IsSink H s)
    (included : IndependenceMap G H) {p : Fin n} (parent : G.edge p s = true) : H.edge p s = true := by
  apply Classical.byContradiction
  intro absent
  have distinct : p ≠ s := by
    intro eq
    subst p
    simp [no_self_arrow] at parent
  let Z : Mask n := fun v => H.edge v s
  have pOff : Z p = false := Bool.eq_false_iff.mpr absent
  have sOff : Z s = false := no_self_arrow H s
  have separated := parents_dSeparate distinct.symm absent (sink_no_directed_walk sinkH)
  have active := adjacent_dConnected (Conditioning.ofPredicate G Z) (.inr parent) sOff pOff
  exact separated (included.dConnection Z s p active)

/-- Step 4 in Lemma 30. Adding a missing parent of a common sink preserves
the independence-map relation whenever that parent occurs in the target. -/
theorem insert_to_common_sink_keeps_map {G H K : DAG n} {s p : Fin n}
    (sinkG : IsSink G s) (sinkH : IsSink H s) (included : IndependenceMap G H)
    (inH : H.edge p s = true) (edit : G.IsInsertion K p s) : IndependenceMap K H := by
  have distinct : p ≠ s := by intro eq; subst p; simp [no_self_arrow] at inH
  have sinkK : IsSink K s := by
    intro v
    apply Bool.eq_false_iff.mpr
    intro e
    rcases (edit s v).mp e with old | added
    · exact Bool.false_ne_true ((sinkG _).symm.trans old)
    · exact distinct added.1.symm
  apply common_sink_lift sinkK sinkH
  · have maps := independence_away_of_same_edges sinkK (H := G)
      (fun u v _ vOff => Bool.eq_iff_iff.mpr ((edit u v).trans (or_iff_left (fun new => vOff new.2))))
    intro Z x y xOff yOff zOff dconn
    exact included.dConnection Z x y (maps Z x y xOff yOff zOff dconn)
  · intro u arrow
    rcases (edit u s).mp arrow with old | added
    · exact parent_subset_of_map_at_sink sinkH included old
    · simpa [added.1] using inH

/-- The Step 4 insertion always exists, since the common sink has no outgoing
walk to the proposed parent. -/
theorem exists_insert_to_common_sink {G H : DAG n} {s p : Fin n}
    (sinkG : IsSink G s) (sinkH : IsSink H s) (included : IndependenceMap G H)
    (inH : H.edge p s = true) : ∃ K, G.IsInsertion K p s ∧ IndependenceMap K H := by
  have distinct : p ≠ s := by intro eq; subst p; simp [no_self_arrow] at inH
  obtain ⟨K, edit⟩ := (G.exists_insertion_iff distinct).mpr (sink_no_directed_walk sinkG)
  exact ⟨K, edit, insert_to_common_sink_keeps_map sinkG sinkH included inH edit⟩


/-- Remove the vertex's incident arrows while keeping the common labelled
vertex set. The removed vertex is represented by an isolated vertex. -/
def isolateSink (G : DAG n) (s : Fin n) : DAG n where
  edge u v := G.edge u v && (u != s && v != s)
  rank := G.rank
  edge_increases u v edge := G.edge_increases u v (Bool.and_eq_true_iff.mp edge).1

private theorem isolated_sink (G : DAG n) (s : Fin n) : IsSink (isolateSink G s) s := by
  intro v
  simp [isolateSink]

private theorem isolated_away_eq (G : DAG n) (s : Fin n) {u v : Fin n}
    (uOff : u ≠ s) (vOff : v ≠ s) : (isolateSink G s).edge u v = G.edge u v := by
  simp [isolateSink, uOff, vOff]

/-- Lemma 25. Removing a common sink with identical parent sets preserves and
reflects independence-map inclusion among all labelled-vertex DAGs. -/
theorem common_sink_reduction_iff {G H : DAG n} {s : Fin n} (sinkG : IsSink G s)
    (sinkH : IsSink H s) (sameParents : ∀ p, G.edge p s = H.edge p s) :
    IndependenceMap G H ↔ IndependenceMap (isolateSink G s) (isolateSink H s) := by
  have intoIsolate (K : DAG n) (sink : IsSink K s) : IndependenceMapAway s K (isolateSink K s) :=
    independence_away_of_same_edges sink (fun _ _ uOff vOff => (isolated_away_eq K s uOff vOff).symm)
  have intoOriginal (K : DAG n) : IndependenceMapAway s (isolateSink K s) K :=
    independence_away_of_same_edges (isolated_sink K s) (fun _ _ => isolated_away_eq K s)
  constructor
  · intro full
    apply common_sink_lift (isolated_sink G s) (isolated_sink H s)
    · intro Z x y xOff yOff zOff conn
      exact intoIsolate H sinkH Z x y xOff yOff zOff
        (full.dConnection Z x y (intoOriginal G Z x y xOff yOff zOff conn))
    · simp [isolateSink]
  · intro reduced
    apply common_sink_lift sinkG sinkH
    · intro Z x y xOff yOff zOff conn
      exact intoOriginal H Z x y xOff yOff zOff
        (reduced.dConnection Z x y (intoIsolate G sinkG Z x y xOff yOff zOff conn))
    · intro p parent
      simpa only [← sameParents p] using parent

end

end OpenCausalScience.Papers.Chickering2002
