module
public import OpenCausalScience.Papers.Chickering2002.InclusionSelection
public import OpenCausalScience.Papers.Chickering2002.InclusionStructure
public import OpenCausalScience.Papers.Chickering2002.InsertionConnections

/-! # Ancestral moral graphs in the unconditioned case of Step 8

Chickering (2002), Appendix A, Lemma 30. This argument transports moral
walks on the ancestral query sets. In particular, an incoming insertion
can only change a query if its head is relevant to that query.
-/

namespace OpenCausalScience.Papers.Chickering2002

open Moralization KimEtAl2026.BayesBallCorrectness
open LauritzenEtAl1990.MoralFactorization (parent_is_relevant)

@[expose] public section

variable {n : Nat} {G H K : DAG n}

private abbrev pairQuery (D : DAG n) (C : Fin n → Bool) (a b : Fin n) : Query D :=
  ⟨(· == a), (· == b), Conditioning.ofPredicate D C⟩

private theorem ancestor_trans {x y z : Fin n} (left : Ancestor G x y) (right : Ancestor G y z) :
    Ancestor G x z := by
  rcases left with rfl | first
  · exact right
  rcases right with rfl | second
  · exact .inr first
  apply Or.inr
  induction second with
  | single arrow => exact .extend first arrow
  | extend _ arrow ih => exact .extend ih arrow

private theorem relevant_of_ancestor {Q : Query G} {u v : Fin n}
    (route : Ancestor G u v) (target : Q.relevant v) : Q.relevant u := by
  obtain ⟨w, selected, ancestor⟩ := (Q.relevant_iff v).mp target
  exact (Q.relevant_iff u).mpr ⟨w, selected, ancestor_trans route ancestor⟩

private theorem relevant_left {C : Fin n → Bool} {a b : Fin n} : (pairQuery G C a b).relevant a :=
  ((pairQuery G C a b).relevant_iff a).mpr ⟨a, .inl (by simp), .inl rfl⟩

private theorem relevant_right {C : Fin n → Bool} {a b : Fin n} : (pairQuery G C a b).relevant b :=
  ((pairQuery G C a b).relevant_iff b).mpr ⟨b, .inr (.inl (by simp)), .inl rfl⟩

private theorem transfer_relevance {Q P : Query G}
    (fromLeft : ∀ v, Q.left v = true → P.relevant v)
    (fromRight : ∀ v, Q.right v = true → P.relevant v)
    (fromCondition : ∀ v, Q.condition.member v = true → P.relevant v)
    {v : Fin n} (rel : Q.relevant v) : P.relevant v := by
  obtain ⟨w, seed, route⟩ := (Q.relevant_iff v).mp rel
  apply relevant_of_ancestor route
  exact seed.elim (fromLeft w) (fun h => h.elim (fromRight w) (fromCondition w))

private theorem transfer_moral_walk {Q : Query G} {P : Query H}
    (conditionMatch : Q.condition.member = P.condition.member)
    (relevance : ∀ v, Q.relevant v → P.relevant v)
    (arrows : ∀ u v, Q.relevant v → G.edge u v = true → H.edge u v = true)
    {a b : Fin n} (route : Q.MoralWalk a b) : P.MoralWalk a b := by
  induction route with
  | nil _ => exact .nil _
  | @cons u v _ edge _ ih =>
    refine .cons ⟨relevance _ edge.sourceRelevant, relevance _ edge.targetRelevant,
      conditionMatch ▸ edge.sourceOutside, conditionMatch ▸ edge.targetOutside, edge.distinct, ?_⟩ ih
    rcases edge.connection with direct | reverse | ⟨c, rel, first, second⟩
    · exact .inl (arrows u v edge.targetRelevant direct)
    · exact .inr (.inl (arrows v u edge.sourceRelevant reverse))
    · exact .inr (.inr ⟨c, relevance _ rel, arrows u c rel first, arrows v c rel second⟩)

private theorem transfer_pair_walk {C : Fin n → Bool} {a b u v : Fin n}
    (relA : (pairQuery G C u v).relevant a) (relB : (pairQuery G C u v).relevant b)
    (route : (pairQuery G C a b).MoralWalk a b) : (pairQuery G C u v).MoralWalk a b := by
  refine transfer_moral_walk (Q := pairQuery G C a b) (P := pairQuery G C u v) rfl
    (fun _ => transfer_relevance (Q := pairQuery G C a b) (P := pairQuery G C u v) ?_ ?_ ?_)
    (fun _ _ _ arrow => arrow) route
  · intro w h
    obtain rfl : w = a := beq_iff_eq.mp h
    exact relA
  · intro w h
    obtain rfl : w = b := beq_iff_eq.mp h
    exact relB
  · intro w seed
    exact ((pairQuery G C u v).relevant_iff w).mpr ⟨w, .inr (.inr seed), .inl rfl⟩

private theorem connection_symm {C : Fin n → Bool} {a b : Fin n}
    (route : Connected G C a b) : Connected G C b a :=
  (singleton_query_connected route.2.1 route.1).mpr
    (reverse_moral_walk (transfer_pair_walk relevant_right relevant_left
      ((singleton_query_connected route.1 route.2.1).mp route)))

private theorem incoming_preserves_descendants {x y w : Fin n} (edit : G.IsInsertion K x y)
    (route : Ancestor K y w) : Ancestor G y w := by
  rcases route with rfl | path
  · exact .inl rfl
  apply Or.inr
  induction path with
  | single arrow =>
    rcases (edit _ _).mp arrow with original | ⟨_, same⟩
    · exact .single original
    · exact (K.no_directed_cycle _ (.single (same ▸ arrow))).elim
  | extend prior arrow ih =>
    rcases (edit _ _).mp arrow with original | ⟨_, same⟩
    · exact .extend ih original
    · have loop := DAG.DirectedWalk.extend prior arrow
      rw [same] at loop
      exact (K.no_directed_cycle y loop).elim

private theorem new_connection_head_relevant {C : Fin n → Bool} {x y a b : Fin n}
    (edit : G.IsInsertion K x y) (added : Connected K C a b) (absent : ¬ Connected G C a b) :
    (pairQuery K C a b).relevant y := by
  classical
  apply Classical.byContradiction
  intro irrelevant
  let Q := pairQuery K C a b
  let P := pairQuery G C a b
  have keepArrow u v (rel : Q.relevant v) (arrow : K.edge u v = true) : G.edge u v = true := by
    rcases (edit _ _).mp arrow with original | ⟨_, same⟩
    · exact original
    · exact (irrelevant (same ▸ rel)).elim
  have keepWalk {u v : Fin n} (route : K.DirectedWalk u v) (rel : Q.relevant v) :
      G.DirectedWalk u v := by
    induction route with
    | single arrow => exact .single (keepArrow _ _ rel arrow)
    | extend _ arrow ih =>
      exact .extend (ih (parent_is_relevant arrow rel)) (keepArrow _ _ rel arrow)
  have keepRelevance v (rel : Q.relevant v) : P.relevant v := by
    obtain ⟨w, seed, same | path⟩ := (Q.relevant_iff v).mp rel
    · exact (P.relevant_iff v).mpr ⟨w, seed, .inl same⟩
    · have wRel := (Q.relevant_iff w).mpr ⟨w, seed, .inl rfl⟩
      exact (P.relevant_iff v).mpr ⟨w, seed, .inr (keepWalk path wRel)⟩
  exact absent ((singleton_query_connected (G := G) (condition := C) added.1 added.2.1).mpr
    (transfer_moral_walk (Q := Q) (P := P) rfl keepRelevance keepArrow
      ((singleton_query_connected (G := K) (condition := C) added.1 added.2.1).mp added)))

private theorem connect_through_relevant {C : Fin n → Bool} {a b d : Fin n}
    (left : Connected G C a d) (right : Connected G C d b)
    (middle : (pairQuery G C a b).relevant d) : Connected G C a b := by
  apply (singleton_query_connected left.1 right.2.1).mpr
  exact append_moral_walk
    (transfer_pair_walk relevant_left middle ((singleton_query_connected left.1 left.2.1).mp left))
    (transfer_pair_walk middle relevant_right ((singleton_query_connected right.1 right.2.1).mp right))

private theorem connect_to_descendant_of_child {C : Fin n → Bool} {a u z d : Fin n}
    (first : Connected G C a u) (edge : G.edge u z = true) (reaches : Ancestor G z d)
    (outside : ∀ v, Ancestor G z v → C v = false) : Connected G C a d := by
  let Q := pairQuery G C a d
  have relD : Q.relevant d := relevant_right
  have relZ := relevant_of_ancestor (Q := Q) reaches relD
  have relU := parent_is_relevant edge relZ
  have notSame : u ≠ z := by
    rintro rfl
    exact G.no_directed_cycle _ (.single edge)
  have walkUD : Q.MoralWalk u d := .cons
    ⟨relU, relZ, first.2.1, outside z (.inl rfl), notSame, .inl edge⟩
    (directed_moral_walk Q outside reaches relD)
  exact (singleton_query_connected first.1 (outside d reaches)).mpr
    (append_moral_walk (transfer_pair_walk relevant_left relU
      ((singleton_query_connected first.1 first.2.1).mp first)) walkUD)

/-- The unconditioned Step 8 case when no descendant of the selected child
is conditioned. The two original-graph segments are supplied by Lemma 22. -/
theorem step8_unconditioned_without_conditioned_descendant
    {C : Fin n → Bool} {x y z d a b u v : Fin n}
    (map : IndependenceMap G H) (selection : SelectedDescendantChild G H y z d)
    (parent : G.edge x z = true) (edit : G.IsInsertion K x y)
    (outside : ∀ w, Ancestor G z w → C w = false)
    (added : Connected K C a b) (absent : ¬ Connected G C a b)
    (endU : u = x ∨ u = y) (endV : v = x ∨ v = y)
    (left : Connected G C a u) (right : Connected G C v b) : Connected H C a b := by
  have childEdge (w : Fin n) (endAt : w = x ∨ w = y) : G.edge w z = true :=
    endAt.elim (fun same => same ▸ parent) (fun same => same ▸ selection.child)
  have leftD := connect_to_descendant_of_child left (childEdge u endU) selection.reaches outside
  have rightD := connection_symm (connect_to_descendant_of_child (connection_symm right)
    (childEdge v endV) selection.reaches outside)
  obtain ⟨w, seed, ancestor⟩ := ((pairQuery K C a b).relevant_iff y).mp
    (new_connection_head_relevant edit added absent)
  obtain ⟨_, _, unique, allReach⟩ := map.unique_descendant_root y
  have ancestorH : Ancestor H d w := by
    rw [unique d selection.descendant_root]
    exact allReach w (incoming_preserves_descendants edit ancestor)
  exact connect_through_relevant (map.dConnection _ _ _ leftD) (map.dConnection _ _ _ rightD)
    (((pairQuery H C a b).relevant_iff _).mpr ⟨w, seed, ancestorH⟩)

end

end OpenCausalScience.Papers.Chickering2002
