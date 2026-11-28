module
public import OpenCausalScience.Papers.Chickering2002.InclusionStructure

/-! # Inclusion for a shortcut along a directed two-edge path

Chickering (2002), Figure 2, Step 7. The shortcut preserves ancestral
closures. Its extra moral edges can be replaced through the intermediate
vertex when that vertex is outside the conditioning set.
-/

namespace OpenCausalScience.Papers.Chickering2002

open KimEtAl2026.BayesBallCorrectness
open VermaPearl1990.DAGEquivalence
open OpenCausalScience.Moralization
open LauritzenEtAl1990.MoralFactorization (parent_is_relevant moral_walk_extend)

@[expose] public section

variable {n : Nat} {G H G' : DAG n}

private theorem append_directed {a b c : Fin n} (first : G.DirectedWalk a b)
    (second : G.DirectedWalk b c) : G.DirectedWalk a c := by
  induction second with
  | single next => exact .extend first next
  | extend _ last ih => exact .extend ih last

theorem shortcut_preserves_directed_walk {x z : Fin n} (shortcut : G.DirectedWalk x z)
    (edit : G.IsInsertion G' x z) (u w : Fin n) :
    G'.DirectedWalk u w ↔ G.DirectedWalk u w := by
  have added {u v : Fin n} (arrow : G'.edge u v = true) : G.DirectedWalk u v := by
    rcases (edit u v).mp arrow with old | ⟨rfl, rfl⟩
    · exact .single old
    · exact shortcut
  constructor
  · intro route
    induction route with
    | single arrow => exact added arrow
    | extend _ last ih => exact append_directed ih (added last)
  · intro route
    induction route with
    | single arrow => exact .single ((edit _ _).mpr (.inl arrow))
    | extend _ last ih => exact .extend ih ((edit _ _).mpr (.inl last))

private theorem shortcut_relevance {x z : Fin n} (shortcut : G.DirectedWalk x z)
    (edit : G.IsInsertion G' x z) (L R C : Fin n → Bool) (u : Fin n) :
    (show Query G' from ⟨L, R, Conditioning.ofPredicate G' C⟩).relevant u ↔
    (show Query G from ⟨L, R, Conditioning.ofPredicate G C⟩).relevant u := by
  rw [Query.relevant_iff, Query.relevant_iff]
  simp only [Conditioning.ofPredicate, Ancestor, shortcut_preserves_directed_walk shortcut edit]

private def ShortcutEdge (G : DAG n) (x z u v : Fin n) : Prop :=
  u = x ∧ (v = z ∨ G.edge v z = true) ∨ v = x ∧ (u = z ∨ G.edge u z = true)

private theorem shortcut_edge_cases {x z : Fin n} (shortcut : G.DirectedWalk x z)
    (edit : G.IsInsertion G' x z) (L R C : Fin n → Bool) {u v : Fin n}
    (step : (show Query G' from ⟨L, R, Conditioning.ofPredicate G' C⟩).MoralEdge u v) :
    let Q : Query G := ⟨L, R, Conditioning.ofPredicate G C⟩
    Q.MoralEdge u v ∨ Q.relevant z ∧ ShortcutEdge G x z u v := by
  let Q : Query G := ⟨L, R, Conditioning.ofPredicate G C⟩
  have rel := fun w => (shortcut_relevance shortcut edit L R C w).mp
  have oldEdge (connection : G.edge u v = true ∨ G.edge v u = true ∨
      ∃ c, Q.relevant c ∧ G.edge u c = true ∧ G.edge v c = true) :
      Q.MoralEdge u v :=
    ⟨rel u step.sourceRelevant, rel v step.targetRelevant, step.sourceOutside,
      step.targetOutside, step.distinct, connection⟩
  rcases step.connection with forward | backward | ⟨child, childRel, one, two⟩
  · rcases (edit u v).mp forward with previous | ⟨rfl, rfl⟩
    · exact .inl (oldEdge (.inl previous))
    · exact .inr ⟨rel _ step.targetRelevant, .inl ⟨rfl, .inl rfl⟩⟩
  · rcases (edit v u).mp backward with previous | ⟨rfl, rfl⟩
    · exact .inl (oldEdge (.inr (.inl previous)))
    · exact .inr ⟨rel _ step.sourceRelevant, .inr ⟨rfl, .inl rfl⟩⟩
  · rcases (edit u child).mp one with first | ⟨rfl, rfl⟩
    · rcases (edit v child).mp two with second | ⟨rfl, rfl⟩
      · exact .inl (oldEdge (.inr (.inr ⟨child, rel child childRel, first, second⟩)))
      · exact .inr ⟨rel _ childRel, .inr ⟨rfl, .inr first⟩⟩
    · rcases (edit v _).mp two with second | ⟨rfl, _⟩
      · exact .inr ⟨rel _ childRel, .inl ⟨rfl, .inr second⟩⟩
      · exact (step.distinct rfl).elim

/-- In the Step 7 query case where the intermediate vertex is unconditioned,
the shortcut creates no new d-connections. -/
theorem shortcut_no_new_connection {x y z a b : Fin n}
    (xy : G.edge x y = true) (yz : G.edge y z = true) (edit : G.IsInsertion G' x z)
    (C : Fin n → Bool) (offY : C y = false)
    (connection : DConnected (Conditioning.ofPredicate G' C) a b) :
    DConnected (Conditioning.ofPredicate G C) a b := by
  let L : Fin n → Bool := (· == a)
  let R : Fin n → Bool := (· == b)
  let Q' : Query G' := ⟨L, R, Conditioning.ofPredicate G' C⟩
  let Q : Query G := ⟨L, R, Conditioning.ofPredicate G C⟩
  have shortcut : G.DirectedWalk x z := .extend (.single xy) yz
  have rel := fun w => (shortcut_relevance shortcut edit L R C w).mp
  have patch {u v : Fin n} (step : Q'.MoralEdge u v) : Q.MoralWalk u v := by
    rcases shortcut_edge_cases shortcut edit L R C step with existing | ⟨zRel, added⟩
    · exact .cons existing (.nil _)
    have yRel := parent_is_relevant yz zRel
    have one : x ≠ y := by
      rintro rfl
      exact G.no_directed_cycle _ (.single xy)
    have two : y ≠ z := by
      rintro rfl
      exact G.no_directed_cycle _ (.single yz)
    have tailWalk {v : Fin n} (vOff : C v = false) (vRel : Q.relevant v)
        (why : v = z ∨ G.edge v z = true) : Q.MoralWalk y v := by
      rcases why with rfl | parent
      · exact .cons ⟨yRel, zRel, offY, vOff, two, .inl yz⟩ (.nil _)
      · by_cases same : y = v
        · subst v
          exact .nil _
        · exact .cons ⟨yRel, vRel, offY, vOff, same, .inr (.inr ⟨z, zRel, yz, parent⟩)⟩ (.nil _)
    rcases added with ⟨rfl, why⟩ | ⟨rfl, why⟩
    · exact .cons ⟨rel _ step.sourceRelevant, yRel, step.sourceOutside, offY, one, .inl xy⟩
        (tailWalk step.targetOutside (rel v step.targetRelevant) why)
    · exact reverse_moral_walk
        (.cons ⟨rel _ step.targetRelevant, yRel, step.targetOutside, offY, one, .inl xy⟩
        (tailWalk step.sourceOutside (rel u step.sourceRelevant) why))
  have translate {u v : Fin n} (walk : Q'.MoralWalk u v) : Q.MoralWalk u v := by
    induction walk with
    | nil _ => exact .nil _
    | cons edge _ ih => exact append_moral_walk (patch edge) ih
  exact (singleton_query_connected connection.1 connection.2.1).mpr
    (translate ((singleton_query_connected connection.1 connection.2.1).mp connection))

private theorem route_to_vertex {a b d : Fin n} (Q : Query G)
    (all : ∀ u, Q.relevant u → Ancestor G u a ∨ Ancestor G u b ∨
      ∃ c, Q.condition.member c = true ∧ Ancestor G u c)
    (bRelevant : Q.relevant b) (separated : ¬ Q.MoralWalk a b)
    (offA : Q.condition.member a = false) (offD : Q.condition.member d = false)
    (path : Q.MoralWalk a d) :
    DConnected (Conditioning.ofPredicate G Q.condition.member) a d := by
  let T : Query G := ⟨(· == a), (· == d), Conditioning.ofPredicate G Q.condition.member⟩
  have keep {u : Fin n} (reach : Q.MoralWalk a u) (rel : Q.relevant u) : T.relevant u := by
    have keepCondition {c : Fin n} (member : Q.condition.member c = true) (anc : Ancestor G u c) :
        T.relevant u := (T.relevant_iff u).mpr ⟨c, .inr (.inr member), anc⟩
    rcases all u rel with toA | toB | ⟨c, member, anc⟩
    · exact (T.relevant_iff u).mpr ⟨a, .inl (by simp [T]), toA⟩
    · by_cases found : ∃ c, Q.condition.member c = true ∧ Ancestor G u c
      · obtain ⟨c, member, anc⟩ := found
        exact keepCondition member anc
      · have off (c : Fin n) (anc : Ancestor G u c) : Q.condition.member c = false :=
          Bool.eq_false_iff.mpr fun member => found ⟨c, member, anc⟩
        exact (separated (append_moral_walk reach (directed_moral_walk Q off toB bRelevant))).elim
    · exact keepCondition member anc
  have lift {u v : Fin n} (reaches : Q.MoralWalk a u)
      (walk : Q.MoralWalk u v) : T.MoralWalk u v := by
    induction walk with
    | nil _ => exact .nil _
    | @cons u w _ step _ ih =>
      have next := moral_walk_extend reaches step
      refine .cons ⟨keep reaches step.sourceRelevant, keep next step.targetRelevant,
        step.sourceOutside, step.targetOutside, step.distinct, ?_⟩ (ih next)
      rcases step.connection with forward | backward | ⟨c, relevant, one, two⟩
      · exact .inl forward
      · exact .inr (.inl backward)
      have turned : T.relevant c := by
        cases h : Q.condition.member c
        · have distinct : u ≠ c := by
            rintro rfl
            exact G.no_directed_cycle _ (.single one)
          have direct : Q.MoralEdge u c :=
            ⟨step.sourceRelevant, relevant, step.sourceOutside, h, distinct, .inl one⟩
          exact keep (moral_walk_extend reaches direct) relevant
        · exact (T.relevant_iff c).mpr ⟨c, .inr (.inr h), .inl rfl⟩
      exact .inr (.inr ⟨c, turned, one, two⟩)
  exact (singleton_query_connected offA offD).mpr (lift (.nil _) path)

private theorem split_off_edges {Q : Query G} {Q' : Query G'} {a b : Fin n}
    (P : Fin n → Prop) (C : Fin n → Bool)
    (classify : ∀ u v, Q'.MoralEdge u v → Q.MoralEdge u v ∨
      (P u ∧ P v ∧ C u = false ∧ C v = false))
    (path : Q'.MoralWalk a b) :
    Q.MoralWalk a b ∨ ∃ u v, P u ∧ P v ∧ C u = false ∧ C v = false ∧
      Q.MoralWalk a u ∧ Q.MoralWalk v b := by
  induction path with
  | nil _ => exact .inl (.nil _)
  | @cons a w b edge _ ih =>
    rcases classify a w edge with old | ⟨pA, pW, offA, offW⟩
    · rcases ih with whole | ⟨u, v, pu, pv, hu, hv, first, last⟩
      · exact .inl (.cons old whole)
      · exact .inr ⟨u, v, pu, pv, hu, hv, .cons old first, last⟩
    · rcases ih with whole | ⟨_, v, _, pv, _, hv, _, last⟩
      · exact .inr ⟨a, w, pA, pW, offA, offW, .nil _, whole⟩
      · exact .inr ⟨a, v, pA, pv, offA, hv, .nil _, last⟩

/-- Step 7 preserves the independence map when the intermediate vertex
of the shortcut is a sink in the target DAG. -/
theorem step_seven_preserves_inclusion {x y z : Fin n}
    (map : IndependenceMap G H) (sink : ∀ v, H.edge y v = false)
    (xy : G.edge x y = true) (yz : G.edge y z = true) (edit : G.IsInsertion G' x z) :
    IndependenceMap G' H := by
  intro a b C _ offA offB hSep
  apply (Discovery.graphOracle_eq_true_iff G' a b C offA offB).mpr
  intro addedConnection
  have hNo := (Discovery.graphOracle_eq_true_iff H a b C offA offB).mp hSep
  cases inY : C y
  · exact hNo (map.dConnection _ _ _ (shortcut_no_new_connection xy yz edit C inY addedConnection))
  let L : Fin n → Bool := (· == a)
  let R : Fin n → Bool := (· == b)
  let Q : Query G := ⟨L, R, Conditioning.ofPredicate G C⟩
  let Q' : Query G' := ⟨L, R, Conditioning.ofPredicate G' C⟩
  let T : Query H := ⟨L, R, Conditioning.ofPredicate H C⟩
  have route : Q'.MoralWalk a b := (singleton_query_connected offA offB).mp addedConnection
  have parentOfSink (u : Fin n) (near : Adjacent H u y) : H.edge u y = true := by
    exact near.resolve_right (fun arrow => Bool.false_ne_true ((sink u).symm.trans arrow))
  have parentX := parentOfSink x (map.adjacent (.inl xy))
  have parentNear (u : Fin n) (openU : C u = false) (near : u = z ∨ G.edge u z = true) :
      H.edge u y = true := by
    rcases near with rfl | uz
    · exact parentOfSink _ (map.adjacent (.inr yz))
    by_cases adjacent : Adjacent G u y
    · exact parentOfSink _ (map.adjacent adjacent)
    · have distinct : u ≠ y := fun h => Bool.false_ne_true ((h ▸ openU).symm.trans inY)
      rcases map.collider_or_shielded (z := z) (x := u) (y := y)
          ⟨distinct, adjacent, uz, yz⟩ with retained | shielded
      · exact (Bool.false_ne_true ((sink z).symm.trans retained.2.2.2)).elim
      · exact parentOfSink _ shielded
  have shortcut : G.DirectedWalk x z := .extend (.single xy) yz
  have classify (u v : Fin n) (edge : Q'.MoralEdge u v) :
      Q.MoralEdge u v ∨ (H.edge u y = true ∧ H.edge v y = true ∧ C u = false ∧ C v = false) := by
    rcases shortcut_edge_cases shortcut edit L R C edge with old | ⟨_, ⟨rfl, near⟩ | ⟨rfl, near⟩⟩
    · exact .inl old
    · exact .inr ⟨parentX, parentNear _ edge.targetOutside near, edge.sourceOutside, edge.targetOutside⟩
    · exact .inr ⟨parentNear _ edge.sourceOutside near, parentX, edge.sourceOutside, edge.targetOutside⟩
  have sepG : ¬ Q.MoralWalk a b := fun stored =>
    hNo (map.dConnection _ _ _ ((singleton_query_connected offA offB).mpr stored))
  rcases split_off_edges (fun u => H.edge u y = true) C classify route with stored | crossing
  · exact sepG stored
  obtain ⟨u, v, pyU, pyV, offU, offV, beginning, ending⟩ := crossing
  have classG (w : Fin n) (rel : Q.relevant w) : Ancestor G w a ∨ Ancestor G w b ∨
      ∃ c, C c = true ∧ Ancestor G w c := by
    obtain ⟨c, member, anc⟩ := (Q.relevant_iff w).mp rel
    rcases member with left | right | chosen
    · change (c == a) = true at left
      obtain rfl := beq_iff_eq.mp left
      exact .inl anc
    · change (c == b) = true at right
      obtain rfl := beq_iff_eq.mp right
      exact .inr (.inl anc)
    · exact .inr (.inr ⟨c, chosen, anc⟩)
  have aRelG := (Q.relevant_iff a).mpr ⟨a, .inl (by simp [Q, L]), .inl rfl⟩
  have bRelG := (Q.relevant_iff b).mpr ⟨b, .inr (.inl (by simp [Q, R])), .inl rfl⟩
  have first := map.dConnection _ _ _
    (route_to_vertex Q classG bRelG sepG offA offU beginning)
  have second := map.dConnection _ _ _
    (route_to_vertex Q (fun w rel => by
      rcases classG w rel with toA | toB | other
      · exact .inr (.inl toA)
      · exact .inl toB
      · exact .inr (.inr other)) aRelG (fun walk => sepG (reverse_moral_walk walk))
      offB offV (reverse_moral_walk ending))
  have yRel := (T.relevant_iff y).mpr ⟨y, .inr (.inr inY), .inl rfl⟩
  have uRel := parent_is_relevant pyU yRel
  have vRel := parent_is_relevant pyV yRel
  have aRelH := (T.relevant_iff a).mpr ⟨a, .inl (by simp [T, L]), .inl rfl⟩
  have bRelH := (T.relevant_iff b).mpr ⟨b, .inr (.inl (by simp [T, R])), .inl rfl⟩
  obtain ⟨_, _, _, _, firstWalk, _⟩ := first
  obtain ⟨_, _, _, _, secondWalk, _⟩ := second
  have bridge : T.MoralWalk u v := by
    by_cases same : u = v
    · subst v
      exact .nil _
    · exact .cons ⟨uRel, vRel, offU, offV, same, .inr (.inr ⟨y, yRel, pyU, pyV⟩)⟩ (.nil _)
  apply hNo
  apply (singleton_query_connected offA offB).mpr
  exact append_moral_walk (Query.ActiveWalk.toMoralWalk (Q := T) firstWalk aRelH uRel offA offU)
    (append_moral_walk bridge (reverse_moral_walk (Query.ActiveWalk.toMoralWalk (Q := T) secondWalk bRelH vRel offB offV)))

end

end OpenCausalScience.Papers.Chickering2002
