module
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap
public import OpenCausalScience.Papers.LauritzenEtAl1990.MoralFactorization

/-! # Skeleton, collider and descendant-root consequences of DAG inclusion

Chickering (2002), Appendix A, Lemma 26 through Lemma 29.
-/

namespace OpenCausalScience.Papers.Chickering2002

open KimEtAl2026.BayesBallCorrectness
open VermaPearl1990.DAGEquivalence
open OpenCausalScience.Moralization
open LauritzenEtAl1990.MoralFactorization (parent_is_relevant moral_walk_extend)

@[expose] public section

variable {n : Nat} {G H : DAG n}

def jointParents (G : DAG n) (x y : Fin n) (v : Fin n) : Bool :=
  G.edge v x || G.edge v y

private theorem joint_parents_outside {x y : Fin n} (missing : ¬ Adjacent G x y) :
    jointParents G x y x = false ∧ jointParents G x y y = false := by
  have xLoop := Bool.eq_false_iff.mpr (fun arrow => G.no_directed_cycle x (.single arrow))
  have yLoop := Bool.eq_false_iff.mpr (fun arrow => G.no_directed_cycle y (.single arrow))
  have forward := Bool.eq_false_iff.mpr (fun arrow => missing (.inl arrow))
  have reverse := Bool.eq_false_iff.mpr (fun arrow => missing (.inr arrow))
  simp [jointParents, xLoop, yLoop, forward, reverse]

theorem moral_edge_symm {Q : Query G} {x y : Fin n}
    (edge : Q.MoralEdge x y) : Q.MoralEdge y x where
  sourceRelevant := edge.targetRelevant
  targetRelevant := edge.sourceRelevant
  sourceOutside := edge.targetOutside
  targetOutside := edge.sourceOutside
  distinct := edge.distinct.symm
  connection := by
    rcases edge.connection with forward | reverse | ⟨c, rel, xc, yc⟩
    · exact .inr (.inl forward)
    · exact .inl reverse
    · exact .inr (.inr ⟨c, rel, yc, xc⟩)

theorem reverse_moral_walk {Q : Query G} {x y : Fin n}
    (walk : Q.MoralWalk x y) : Q.MoralWalk y x := by
  induction walk with
  | nil _ => exact .nil _
  | cons step _ rest => exact moral_walk_extend rest (moral_edge_symm step)

theorem append_moral_walk {Q : Query G} {x y z : Fin n}
    (first : Q.MoralWalk x y) (second : Q.MoralWalk y z) : Q.MoralWalk x z := by
  induction first with
  | nil _ => exact second
  | cons edge _ ih => exact .cons edge (ih second)

theorem singleton_query_connected {x y : Fin n} {condition : Fin n → Bool}
    (xOutside : condition x = false) (yOutside : condition y = false) :
    let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
    DConnected Q.condition x y ↔ Q.MoralWalk x y := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  have leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false := by
    intro v hv
    change (v == x) = true at hv
    have same := beq_iff_eq.mp hv
    simpa [Q, Conditioning.ofPredicate, same] using xOutside
  have rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false := by
    intro v hv
    change (v == y) = true at hv
    have same := beq_iff_eq.mp hv
    simpa [Q, Conditioning.ofPredicate, same] using yOutside
  have iff := Q.dConnection_iff_moralConnection leftOutside rightOutside
  constructor
  · intro route
    obtain ⟨a, b, first, last, walk⟩ := iff.mp ⟨x, y, by simp [Q], by simp [Q], route⟩
    change (a == x) = true at first
    change (b == y) = true at last
    simpa only [beq_iff_eq.mp first, beq_iff_eq.mp last] using walk
  · intro walk
    obtain ⟨a, b, first, last, route⟩ := iff.mpr ⟨x, y, by simp [Q], by simp [Q], walk⟩
    change (a == x) = true at first
    change (b == y) = true at last
    simpa only [beq_iff_eq.mp first, beq_iff_eq.mp last] using route

/-- The union of the parent sets of two nonadjacent vertices separates them. -/
theorem nonadjacent_joint_parents_separate {x y : Fin n}
    (distinct : x ≠ y) (missing : ¬ Adjacent G x y) :
    ¬ DConnected (Conditioning.ofPredicate G (jointParents G x y)) x y := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G (jointParents G x y)⟩
  obtain ⟨offX, offY⟩ := joint_parents_outside missing
  have bound {v t : Fin n} (xBelow : G.rank x ≤ G.rank t) (yBelow : G.rank y ≤ G.rank t)
      (rel : Q.relevant v) : G.rank v ≤ G.rank t := by
    obtain ⟨w, seed, ancestor⟩ := (Q.relevant_iff v).mp rel
    have wBelow : G.rank w ≤ G.rank t := by
      rcases seed with left | right | parents
      · change (w == x) = true at left
        simpa [beq_iff_eq.mp left] using xBelow
      · change (w == y) = true at right
        simpa [beq_iff_eq.mp right] using yBelow
      · rcases Bool.or_eq_true_iff.mp parents with first | second
        · exact Nat.le_trans (Nat.le_of_lt (G.edge_increases _ _ first)) xBelow
        · exact Nat.le_trans (Nat.le_of_lt (G.edge_increases _ _ second)) yBelow
    rcases ancestor with rfl | path
    · exact wBelow
    · exact Nat.le_trans (Nat.le_of_lt (G.rank_lt_of_directedWalk path)) wBelow
  have isolated {t : Fin n} (atEnd : t = x ∨ t = y)
      (xBelow : G.rank x ≤ G.rank t) (yBelow : G.rank y ≤ G.rank t) (v : Fin n)
      (edge : Q.MoralEdge t v) : False := by
    rcases edge.connection with outgoing | incoming | ⟨a, rel, first, _⟩
    · exact Nat.not_lt_of_ge (bound xBelow yBelow edge.targetRelevant) (G.edge_increases _ _ outgoing)
    · have selected : jointParents G x y v = true := by
        rcases atEnd with rfl | rfl <;> simp [jointParents, incoming]
      exact Bool.false_ne_true (edge.targetOutside.symm.trans selected)
    · exact Nat.not_lt_of_ge (bound xBelow yBelow rel) (G.edge_increases _ _ first)
  intro connected
  have route : Q.MoralWalk x y := (singleton_query_connected offX offY).mp connected
  by_cases earlier : G.rank y ≤ G.rank x
  · cases route with
    | nil => exact distinct rfl
    | cons edge _ => exact isolated (.inl rfl) (Nat.le_refl _) earlier _ edge
  · have reversed := reverse_moral_walk route
    cases reversed with
    | nil => exact distinct rfl
    | cons edge _ => exact isolated (.inr rfl) (by omega) (Nat.le_refl _) _ edge

/-- Proposition 27. Skeleton edges persist under the independence-map order. -/
theorem IndependenceMap.adjacent (map : IndependenceMap G H) {x y : Fin n}
    (edge : Adjacent G x y) : Adjacent H x y := by
  classical
  apply Classical.byContradiction
  intro missing
  have distinct : x ≠ y := by
    rintro rfl
    exact G.no_directed_cycle x (.single (edge.elim id id))
  obtain ⟨xOutside, yOutside⟩ := joint_parents_outside missing
  exact nonadjacent_joint_parents_separate distinct missing
    (map.dConnection _ x y (adjacent_dConnected _ edge xOutside yOutside))

/-- Lemma 28. An unshielded collider is preserved unless its endpoints gain
an adjacency. -/
theorem IndependenceMap.collider_or_shielded (map : IndependenceMap G H)
    {x z y : Fin n} (collider : UnshieldedCollider G x z y) :
    UnshieldedCollider H x z y ∨ Adjacent H x y := by
  by_cases present : Adjacent H x y
  · exact .inr present
  obtain ⟨distinct, _, headToHead⟩ := collider
  have xz : Adjacent G x z := .inl headToHead.1
  have yz : Adjacent G y z := .inl headToHead.2
  obtain ⟨offX, offY⟩ := joint_parents_outside present
  have hSep := nonadjacent_joint_parents_separate distinct present
  have gSep : ¬ DConnected (Conditioning.ofPredicate G (jointParents H x y)) x y :=
    fun route => hSep (map.dConnection _ x y route)
  have zOutside := (middle_omitted_iff_headToHead_of_separating _ xz yz distinct offX offY gSep).mpr headToHead
  have newCollider := (middle_omitted_iff_headToHead_of_separating _
    (map.adjacent xz) (map.adjacent yz) distinct offX offY hSep).mp zOutside
  exact .inl ⟨distinct, present, newCollider⟩

theorem directed_moral_walk (Q : Query G) {root v : Fin n}
    (off : ∀ u, Ancestor G root u → Q.condition.member u = false)
    (desc : Ancestor G root v) (relevant : Q.relevant v) : Q.MoralWalk root v := by
  rcases desc with rfl | path
  · exact .nil _
  · induction path with
    | @single x arrow =>
      have other := parent_is_relevant arrow relevant
      have distinct : root ≠ x := by
        rintro rfl
        exact G.no_directed_cycle root (.single arrow)
      exact .cons ⟨other, relevant, off _ (.inl rfl), off _ (.inr (.single arrow)),
        distinct, .inl arrow⟩ (.nil _)
    | @extend u w walk arrow ih =>
      have uRelevant := parent_is_relevant arrow relevant
      have distinct : u ≠ w := by
        rintro rfl
        exact G.no_directed_cycle u (.single arrow)
      exact moral_walk_extend (ih uRelevant) ⟨uRelevant, relevant, off _ (.inr walk),
        off _ (.inr (.extend walk arrow)), distinct, .inl arrow⟩

theorem dConnected_of_common_ancestor {root x y : Fin n} {condition : Fin n → Bool}
    (left : Ancestor G root x) (right : Ancestor G root y)
    (noDescendant : ∀ u, Ancestor G root u → condition u = false) :
    DConnected (Conditioning.ofPredicate G condition) x y := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  have xRel := (Q.relevant_iff x).mpr ⟨x, .inl (by simp [Q]), .inl rfl⟩
  have yRel := (Q.relevant_iff y).mpr ⟨y, .inr (.inl (by simp [Q])), .inl rfl⟩
  exact (singleton_query_connected (noDescendant x left) (noDescendant y right)).mpr
    (append_moral_walk (reverse_moral_walk (directed_moral_walk Q noDescendant left xRel))
      (directed_moral_walk Q noDescendant right yRel))

/-- A root of the subgraph of H on the reflexive descendants of y in G. -/
def DescendantRoot (G H : DAG n) (y d : Fin n) : Prop :=
  Ancestor G y d ∧ ∀ v, Ancestor G y v → H.edge v d = false

private theorem descendant_root_exists {y v : Fin n} (member : Ancestor G y v) :
    ∃ d, DescendantRoot G H y d ∧ Ancestor H d v := by
  classical
  by_cases incoming : ∃ u, Ancestor G y u ∧ H.edge u v = true
  · obtain ⟨u, uMember, arrow⟩ := incoming
    obtain ⟨d, root, path⟩ := descendant_root_exists uMember
    refine ⟨d, root, .inr ?_⟩
    rcases path with rfl | route
    · exact .single arrow
    · exact .extend route arrow
  · refine ⟨v, ⟨member, ?_⟩, .inl rfl⟩
    intro u hu
    exact Bool.eq_false_iff.mpr (fun arrow => incoming ⟨u, hu, arrow⟩)
termination_by H.rank v
decreasing_by exact H.edge_increases _ _ arrow

/-- Lemma 29. The subgraph of H induced by the reflexive descendants of
a vertex in G has a unique root, which reaches all these descendants in H. -/
theorem IndependenceMap.unique_descendant_root (map : IndependenceMap G H) (y : Fin n) :
    ∃ d, DescendantRoot G H y d ∧ (∀ e, DescendantRoot G H y e → e = d) ∧
      ∀ v, Ancestor G y v → Ancestor H d v := by
  have unique {d e : Fin n} (hd : DescendantRoot G H y d) (he : DescendantRoot G H y e) : d = e := by
    classical
    apply Classical.byContradiction
    intro distinct
    have missing : ¬ Adjacent H d e := by
      rintro (first | second)
      · exact Bool.false_ne_true ((he.2 d hd.1).symm.trans first)
      · exact Bool.false_ne_true ((hd.2 e he.1).symm.trans second)
    have outside (u : Fin n) (member : Ancestor G y u) : jointParents H d e u = false := by
      simp [jointParents, hd.2 u member, he.2 u member]
    exact nonadjacent_joint_parents_separate distinct missing
      (map.dConnection _ d e (dConnected_of_common_ancestor hd.1 he.1 outside))
  obtain ⟨d, root, _⟩ := descendant_root_exists (G := G) (H := H) (.inl (rfl : y = y))
  refine ⟨d, root, fun _ other => unique other root, ?_⟩
  intro v member
  obtain ⟨other, otherRoot, reaches⟩ := descendant_root_exists (G := G) (H := H) member
  simpa only [unique otherRoot root] using reaches

end

end OpenCausalScience.Papers.Chickering2002
