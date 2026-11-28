module
public import OpenCausalScience.Papers.Chickering2002.InsertionConnections
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap

/-! # D-connection through an activated child after insertion

Chickering (2002), Appendix A, Corollary 24 and the first two cases
of the Step 8 argument in Lemma 30.
-/

namespace OpenCausalScience.Papers.Chickering2002

open KimEtAl2026.BayesBall KimEtAl2026.BayesBallCorrectness
open VermaPearl1990.DAGEquivalence
open OpenCausalScience.Moralization

@[expose] public section

variable {n : Nat} {G H D : DAG n}

private theorem append_active_walk {R : Conditioning G} {a b c : State (Fin n)}
    {first middle : List (Fin n)} (before : ActiveWalk R a first b)
    (after : ActiveWalk R b middle c) : ActiveWalk R a (first ++ middle) c := by
  induction before with
  | nil _ => exact after
  | cons step _ ih => exact .cons step (ih after)

/-- Compose d-connections through two incoming arrows at an activated
child. The child may be visited twice along the combined walk. -/
theorem connect_via_activated_child {C : Fin n → Bool} {a b u v child : Fin n}
    (first : Connected G C a u) (second : Connected G C v b)
    (up : G.edge u child = true) (vp : G.edge v child = true)
    (active : (Conditioning.ofPredicate G C).activated child = true) :
    Connected G C a b := by
  let R := Conditioning.ofPredicate G C
  obtain ⟨offA, offU, firstVisits, arrivalU, towardU, _⟩ := first
  obtain ⟨_offV, offB, lastVisits, arrivalB, fromV, _⟩ := second
  have firstStep : ActiveStep R (u, arrivalU) (child, .down) :=
    ⟨up, by simpa [OpenTurn, R] using offU⟩
  have nextStep : ActiveStep R (child, .down) (v, .up) :=
    ⟨vp, by simpa [OpenTurn, R] using active⟩
  have through := append_active_walk towardU (.cons firstStep (.cons nextStep fromV))
  apply (corrected_reachable_iff_dconnected R offA offB).mp
  exact ⟨arrivalB, (corrected_reachable_iff_active_walk R).mpr ⟨_, through⟩⟩

theorem activated_of_conditioned_descendant {C : Fin n → Bool} {z d : Fin n}
    (reaches : Ancestor G z d) (inSet : C d = true) :
    (Conditioning.ofPredicate G C).activated z = true := by
  rcases reaches with rfl | way
  · simp [Conditioning.activated, Conditioning.ofPredicate, inSet]
  · let R := Conditioning.ofPredicate G C
    have hit : R.descendantHit z = true := (R.descendant_spec z).mpr ⟨d, inSet, way⟩
    change R.activated z = true
    simp [Conditioning.activated, hit]

/-- An insertion into a conditioned head preserves inclusion for this
query if the target graph contains the inserted arrow and all original
incoming arrows to the head. -/
theorem conditioned_head_insertion_connection {x y a b : Fin n}
    (map : IndependenceMap G H) (edit : G.IsInsertion D x y)
    (incoming : ∀ t, G.edge t y = true → H.edge t y = true)
    (newArrow : H.edge x y = true) (C : Fin n → Bool) (conditioned : C y = true)
    (route : Connected D C a b) : Connected H C a b := by
  rcases insertion_connection_split edit C route with existing | ⟨u, v, atU, atV, _, left, right⟩
  · exact map.dConnection _ _ _ existing
  have parent (t : Fin n) (atEnd : InsertionSegmentEnd G C x y t) : H.edge t y = true := by
    rcases atEnd with rfl | old
    · exact newArrow
    · exact incoming t (by simpa [conditioned] using old)
  exact connect_via_activated_child (map.dConnection _ _ _ left) (map.dConnection _ _ _ right)
    (parent u atU) (parent v atV) (activated_of_conditioned_descendant (.inl rfl) conditioned)

/-- The Step 8 query with Y conditioned is covered by the target sink
and the existing two arrows into Z. -/
theorem step_eight_conditioned_connection {x y z a b : Fin n}
    (map : IndependenceMap G H) (sink : ∀ v, H.edge y v = false)
    (different : x ≠ y) (xz : G.edge x z = true) (yz : G.edge y z = true)
    (edit : G.IsInsertion D x y) (C : Fin n → Bool) (conditioned : C y = true)
    (route : Connected D C a b) : Connected H C a b := by
  have pointsIn (u : Fin n) (attached : Adjacent H u y) : H.edge u y = true :=
    attached.resolve_right (fun edge => Bool.false_ne_true ((sink u).symm.trans edge))
  have visibleXY : Adjacent H x y := by
    by_cases before : Adjacent G x y
    · exact map.adjacent before
    rcases map.collider_or_shielded (z := z) ⟨different, before, xz, yz⟩ with retained | nowAdjacent
    · exact (Bool.false_ne_true ((sink z).symm.trans retained.2.2.2)).elim
    · exact nowAdjacent
  exact conditioned_head_insertion_connection map edit
    (fun u edge => pointsIn u (map.adjacent (.inl edge))) (pointsIn x visibleXY) C conditioned route

/-- An unconditioned Y has no novel Step 8 connection when a descendant
of Z is conditioned. Both original segments join through the activated Z. -/
theorem step_eight_conditioned_descendant_connection {x y z d a b : Fin n}
    (xz : G.edge x z = true) (yz : G.edge y z = true)
    (edit : G.IsInsertion D x y) (C : Fin n → Bool) (offY : C y = false)
    (descendant : Ancestor G z d) (conditioned : C d = true)
    (route : Connected D C a b) : Connected G C a b := by
  rcases insertion_connection_split edit C route with existing | ⟨u, v, atU, atV, _, left, right⟩
  · exact existing
  have parent (t : Fin n) (atEnd : InsertionSegmentEnd G C x y t) : G.edge t z = true := by
    rcases atEnd with rfl | reaches
    · exact xz
    · have same : t = y := by simpa [offY] using reaches
      simpa [same] using yz
  exact connect_via_activated_child left right (parent u atU) (parent v atV)
    (activated_of_conditioned_descendant descendant conditioned)

end

end OpenCausalScience.Papers.Chickering2002
