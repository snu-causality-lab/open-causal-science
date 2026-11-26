module
public import OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge
public import OpenCausalScience.Papers.Zhang2008OrientationRules.UnshieldedPaths

/-! # Local orientation and descendant sets

Wang, Qin and Zhou (2023), Appendix B, Lemmas 4, 7, 9 and 10.
An agreeing graph with correctly specified local knowledge serves as an
arbitrary member of the restricted class.

Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.LocalTransformation

open LocalBackgroundKnowledge (PMG Mark)
open Zhang2008OrientationRules.Orientations (Directed AncestralMarks)
open Zhang2008OrientationRules.UnshieldedPaths
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

/-- The fixed endpoints and common skeleton of a PMG. -/
structure Agreement (P : PMG n) (G : MarkedGraph n) : Prop where
  adjacent : ∀ u v, P.Adjacent u v ↔ G.adjacent u v = true
  tail : ∀ {u v}, P.markAt u v = some .tail → G.arrowheadAt u v = false
  head : ∀ {u v}, P.markAt u v = some .arrow → G.arrowheadAt u v = true

/-- The correctly specified local knowledge at `x` fixes precisely which
circle endpoints at `x` are arrowheads. -/
structure LocalChoice (P : PMG n) (G : MarkedGraph n) (x : Fin n)
    (selected : Fin n → Prop) : Prop where
  is_circle : ∀ {v}, selected v → P.markAt x v = some .circle
  head_iff_selected : ∀ {v}, P.markAt x v = some .circle →
    (G.arrowheadAt x v = true ↔ selected v)

/-- The tail-witness direction of Complete in the previous equivalence
class. The witness may fail the new local knowledge. -/
def PreviousTailWitnesses (P : PMG n) (G : MarkedGraph n) : Prop :=
  ∀ {u v}, P.markAt u v = some .circle →
    ∃ H : MarkedGraph n, Agreement P H ∧ H.HasSeparators ∧
      H.SameSeparations G ∧ H.arrowheadAt u v = false

def NoSelection (G : MarkedGraph n) : Prop :=
  ∀ {u v}, G.marks u v ≠ some (false, false)

/-- `v` is possibly reachable from `x` without using selected vertices. -/
def PossibleDescendantAvoiding (P : PMG n) (selected : Fin n → Prop)
    (x v : Fin n) : Prop :=
  ∃ (vertices : Nat → Fin n) (length : Nat),
    P.PossiblePath vertices length ∧ vertices 0 = x ∧ vertices length = v ∧
      ∀ k, k ≤ length → ¬ selected (vertices k)

private theorem possible_adjacent {P : PMG n} {u v : Fin n}
    (edge : P.PossibleForward u v) : P.Adjacent u v := by
  rcases edge with e | e <;> simp [PMG.Adjacent, e]

private theorem not_adjacent {P : PMG n} {G : MarkedGraph n} (agree : Agreement P G)
    {u v : Fin n} (absent : ¬ P.Adjacent u v) : G.adjacent u v = false := by
  cases h : G.adjacent u v with
  | false => rfl
  | true => exact (absent ((agree.adjacent u v).mpr h)).elim

private theorem tail_leaves {G : MarkedGraph n} (noSelection : NoSelection G) {u v : Fin n}
    (adjacent : G.adjacent u v = true) (tail : G.arrowheadAt u v = false) : Directed G u v := by
  obtain ⟨⟨a, b⟩, marks⟩ := Option.isSome_iff_exists.mp adjacent
  cases a with
  | true => simp [MarkedGraph.arrowheadAt, marks] at tail
  | false =>
    cases b with
    | false => exact (noSelection marks).elim
    | true => exact marks

/-- R11. In the absence of selection, a definite tail requires an
arrowhead at the opposite endpoint. -/
theorem r11_sound {G : MarkedGraph n} (noSelection : NoSelection G) {u v : Fin n}
    (adjacent : G.adjacent u v = true) (tail : G.arrowheadAt u v = false) :
    Directed G u v :=
  tail_leaves noSelection adjacent tail

private theorem first_mark_is_tail {P : PMG n} {G : MarkedGraph n}
    {x next : Fin n} {selected : Fin n → Prop}
    (agree : Agreement P G) (knowledge : LocalChoice P G x selected)
    (edge : P.PossibleForward x next) (avoids : ¬ selected next) :
    G.arrowheadAt x next = false := by
  rcases edge with tail | circle
  · exact agree.tail tail
  · cases mark : G.arrowheadAt x next with
    | false => rfl
    | true => exact (avoids ((knowledge.head_iff_selected circle).mp mark)).elim

/-- Lemma 7, Step 1. A nonselected circle at the treatment is oriented
out of the treatment in every compatible MAG. -/
theorem step1_directs_unselected_edge {P : PMG n} {G : MarkedGraph n}
    (noSelection : NoSelection G) (agree : Agreement P G)
    {x v : Fin n} {selected : Fin n → Prop} (knowledge : LocalChoice P G x selected)
    (circle : P.markAt x v = some .circle) (outside : ¬ selected v) : Directed G x v :=
  tail_leaves noSelection ((agree.adjacent x v).mp (possible_adjacent (.inr circle)))
    (first_mark_is_tail agree knowledge (.inr circle) outside)

private theorem no_new_noncollider_head {P : PMG n} {G : MarkedGraph n}
    (agree : Agreement P G) (gMax : G.HasSeparators) (witness : PreviousTailWitnesses P G)
    {a b c : Fin n} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (first : P.Adjacent a b) (second : P.PossibleForward b c) (unshielded : ¬ P.Adjacent a c) :
    G.collider a b c = false := by
  rcases second with tail | circle
  · have noHead := agree.tail tail
    simp [MarkedGraph.collider, noHead]
  · obtain ⟨H, hAgree, hMax, same, noHead⟩ := witness circle
    exact unshielded_noncollider_invariant hMax gMax same ab ac bc
      ((hAgree.adjacent a b).mp first) ((hAgree.adjacent b c).mp (possible_adjacent (.inr circle)))
      (not_adjacent hAgree unshielded) (by simp [MarkedGraph.collider, noHead])

/-- Lemma 4, only-if direction. The input properties shorten the
possibly directed path to a chordless path. Correct local knowledge
directs its first edge, and noncollider invariance directs the rest. -/
theorem possible_descendant_is_descendant {P : PMG n} {G : MarkedGraph n}
    (conditions : P.PossiblePathConditions) (agree : Agreement P G)
    (gMax : G.HasSeparators) (ancestral : AncestralMarks G) (noSelection : NoSelection G)
    (witness : PreviousTailWitnesses P G) {x v : Fin n} {selected : Fin n → Prop}
    (knowledge : LocalChoice P G x selected)
    (possible : PossibleDescendantAvoiding P selected x v) : Reach (Directed G) x v := by
  obtain ⟨vertices, length, path, start, finish, avoided⟩ := possible
  obtain ⟨reduced, count, path, uncovered, reducedStart, reducedEnd, subset⟩ :=
    PMG.exists_uncovered_possible_path conditions path
  have start' : reduced 0 = x := reducedStart.trans start
  have finish' : reduced count = v := reducedEnd.trans finish
  cases count with
  | zero => rw [← start', ← finish']; exact .refl _
  | succ count =>
    have openPath : NoncolliderPath G reduced (count + 1) := by
      constructor
      · intro i bound
        exact (agree.adjacent _ _).mp (possible_adjacent (path.step i bound))
      · intro i bound
        have distinct : ∀ {j k}, j ≤ count + 1 → k ≤ count + 1 → j ≠ k → reduced j ≠ reduced k :=
          fun j k ne eq => ne (path.simple j k eq)
        exact no_new_noncollider_head agree gMax witness
          (distinct (by omega) (by omega) (by omega))
          (distinct (by omega) (by omega) (by omega))
          (distinct (by omega) (by omega) (by omega))
          (possible_adjacent (path.step i (by omega))) (path.step (i + 1) bound)
          (uncovered i (i + 2) (by omega) (by omega))
    have begins := path.step 0 (by omega)
    obtain ⟨pos, posBound, same⟩ := subset 1 (by omega)
    have nextOutside : ¬ selected (reduced 1) := fun h => avoided pos posBound (same ▸ h)
    have firstTail := first_mark_is_tail agree knowledge
      (show P.PossibleForward x (reduced 1) by simpa [start'] using begins) nextOutside
    have first := tail_leaves noSelection (openPath.adjacent 0 (by omega))
      (by simpa [start'] using firstTail)
    have reaches := reach_end_of_directed_path (direct_noncollider_path ancestral openPath first)
    simpa [start', finish'] using reaches

/-- Part of Lemma 7, Step 1. A selected endpoint points into the
treatment. An adjacency from such a vertex to a descendant therefore
has an arrowhead at the descendant. -/
theorem step1_head_at_descendant {P : PMG n} {G : MarkedGraph n}
    (ancestral : AncestralMarks G) (noSelection : NoSelection G)
    {x v t : Fin n} {selected : Fin n → Prop} (knowledge : LocalChoice P G x selected)
    (descendant : Reach (Directed G) x v) (chosen : selected t)
    (adjacent : G.adjacent v t = true) : G.arrowheadAt v t = true := by
  have intoX := (knowledge.head_iff_selected (knowledge.is_circle chosen)).mpr chosen
  cases head : G.arrowheadAt v t with
  | true => rfl
  | false =>
    have reaches := Reach.extend descendant (tail_leaves noSelection adjacent head)
    exact (ancestral.no_head_into_ancestor reaches intoX).elim

/-- Lemma 10. A descendant cannot be a parent of a selected vertex.
Combined with Lemma 4 this removes the intersection of possible
descendants with the definite parents of the selected vertices. -/
theorem descendant_cannot_be_parent_of_selected {P : PMG n} {G : MarkedGraph n}
    (ancestral : AncestralMarks G) {x v t : Fin n} {selected : Fin n → Prop}
    (knowledge : LocalChoice P G x selected)
    (descendant : Reach (Directed G) x v) (chosen : selected t) :
    ¬ Directed G v t :=
  fun edge => ancestral.no_head_into_ancestor (.extend descendant edge)
    ((knowledge.head_iff_selected (knowledge.is_circle chosen)).mpr chosen)

/-- Lemma 9. Distinct selected neighbours are adjacent, since otherwise
their two required heads would be a new unshielded collider. -/
theorem selected_vertices_are_adjacent {P : PMG n} {G : MarkedGraph n}
    (agree : Agreement P G) (gMax : G.HasSeparators) (witness : PreviousTailWitnesses P G)
    {x u v : Fin n} {selected : Fin n → Prop} (knowledge : LocalChoice P G x selected)
    (hu : selected u) (hv : selected v) (uv : u ≠ v) : P.Adjacent u v := by
  apply Classical.byContradiction
  intro absent
  have circleU := knowledge.is_circle hu
  have circleV := knowledge.is_circle hv
  have xu : x ≠ u := by
    intro same
    subst u
    simp [P.loop_free] at circleU
  have xv : x ≠ v := by
    intro same
    subst v
    simp [P.loop_free] at circleV
  have first : P.Adjacent u x := by
    unfold PMG.Adjacent
    rw [P.same_adjacencies u x]
    simp [circleU]
  have noncollider := no_new_noncollider_head agree gMax witness xu.symm uv xv first (.inr circleV) absent
  have headU := (knowledge.head_iff_selected circleU).mpr hu
  have headV := (knowledge.head_iff_selected circleV).mpr hv
  simp [MarkedGraph.collider, headU, headV] at noncollider

/-- Membership in the set `F_V` in Algorithm 1. -/
def InF (P : PMG n) (selected : Fin n → Prop) (x v t : Fin n) : Prop :=
  (t = x ∨ selected t) ∧ P.markAt v t = some .circle

private theorem reverse_adjacent {P : PMG n} {a b : Fin n} (h : P.Adjacent a b) :
    P.Adjacent b a := by
  unfold PMG.Adjacent at *
  rw [P.same_adjacencies b a]
  exact h

private theorem directed_adjacent {G : MarkedGraph n} {u v : Fin n} (edge : Directed G u v) :
    G.adjacent u v = true := by
  change G.marks u v = some (false, true) at edge
  simp [MarkedGraph.adjacent, edge]

private theorem no_head_at_ancestor {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {a b : Fin n} (ancestor : Reach (Directed G) a b) : G.arrowheadAt a b = false := by
  cases head : G.arrowheadAt a b with
  | false => rfl
  | true => exact (ancestral.no_head_into_ancestor ancestor head).elim

private theorem head_of_directed {G : MarkedGraph n} {u v : Fin n} (edge : Directed G u v) :
    G.arrowheadAt v u = true := by
  change G.marks u v = some (false, true) at edge
  simp [MarkedGraph.arrowheadAt, G.swap_marks u v, edge, Prod.swap]

private theorem indexed_directed_path {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {x v : Fin n} (descendant : Reach (Directed G) x v) :
    ∃ (path : Nat → Fin n) (length : Nat), path 0 = x ∧ path length = v ∧
      (∀ i, i < length → Directed G (path i) (path (i + 1))) ∧
      (∀ i j, i ≤ length → j ≤ length → path i = path j → i = j) := by
  induction descendant with
  | refl => exact ⟨fun _ => x, 0, rfl, rfl, fun _ bound => by omega,
      fun _ _ i j _ => by omega⟩
  | @extend u v prior edge ih =>
    obtain ⟨path, length, start, finish, directed, simple⟩ := ih
    let longer := fun k => if k ≤ length then path k else v
    have noRepeat : ∀ k, k ≤ length → path k ≠ v := by
      intro k bound same
      let subpath := fun i => path (k + i)
      have subDirected : ∀ i, i < length - k →
          Directed G (subpath i) (subpath (i + 1)) := fun i hi => directed (k + i) (by omega)
      have reaches := reach_end_of_directed_path subDirected
      have endIndex : k + (length - k) = length := by omega
      have reaches' : Reach (Directed G) v u := by
        simpa [subpath, endIndex, same, finish] using reaches
      exact ancestral.no_head_into_ancestor reaches' (head_of_directed edge)
    have past : ¬ length + 1 ≤ length := by omega
    refine ⟨longer, length + 1, by simp [longer, start], by simp [longer, past], ?_, ?_⟩
    · intro k bound
      by_cases before : k < length
      · have next : k + 1 ≤ length := by omega
        simpa [longer, Nat.le_of_lt before, next] using directed k before
      · have final : k = length := by omega
        subst k
        simpa [longer, finish, past] using edge
    · intro i j iBound jBound same
      by_cases left : i ≤ length <;> by_cases right : j ≤ length
      · exact simple i j left right (by simpa [longer, left, right] using same)
      · exact (noRepeat i left (by simpa [longer, left, right] using same)).elim
      · exact (noRepeat j right (by simpa [longer, left, right] using same.symm)).elim
      · omega

/-- Lemma 4, if direction. A directed path in a compatible graph is
possibly directed in the PMG and cannot visit any selected vertex. -/
theorem descendant_is_possible_descendant {P : PMG n} {G : MarkedGraph n}
    (agree : Agreement P G) (ancestral : AncestralMarks G)
    {x v : Fin n} {selected : Fin n → Prop} (knowledge : LocalChoice P G x selected)
    (descendant : Reach (Directed G) x v) : PossibleDescendantAvoiding P selected x v := by
  obtain ⟨path, length, start, finish, directed, simple⟩ := indexed_directed_path ancestral descendant
  refine ⟨path, length, ⟨?_, fun bounded bounded' eq => simple _ _ bounded bounded' eq⟩,
    start, finish, ?_⟩
  · intro k bound
    have edge := directed k bound
    have adjacent := (agree.adjacent _ _).mpr (directed_adjacent edge)
    obtain ⟨mark, marks⟩ := Option.isSome_iff_exists.mp adjacent
    cases mark with
    | tail => exact .inl marks
    | circle => exact .inr marks
    | arrow =>
      have head := agree.head marks
      have tail := no_head_at_ancestor ancestral (.extend (.refl _) edge)
      simp [tail] at head
  · intro k bound chosen
    have prefixDirected : ∀ i, i < k → Directed G (path i) (path (i + 1)) :=
      fun i hi => directed i (Nat.lt_of_lt_of_le hi bound)
    have reaches : Reach (Directed G) x (path k) := by
      simpa [start] using reach_end_of_directed_path prefixDirected
    exact ancestral.no_head_into_ancestor reaches
      ((knowledge.head_iff_selected (knowledge.is_circle chosen)).mpr chosen)

/-- Lemma 4. Possible descendants after removing the selected vertices
are exactly the descendants in each compatible graph. -/
theorem possible_descendants_eq_descendants {P : PMG n} {G : MarkedGraph n}
    (conditions : P.PossiblePathConditions) (agree : Agreement P G)
    (gMax : G.HasSeparators) (ancestral : AncestralMarks G) (noSelection : NoSelection G)
    (witness : PreviousTailWitnesses P G) {x v : Fin n} {selected : Fin n → Prop}
    (knowledge : LocalChoice P G x selected) :
    PossibleDescendantAvoiding P selected x v ↔ Reach (Directed G) x v :=
  ⟨possible_descendant_is_descendant conditions agree gMax ancestral noSelection witness knowledge,
    descendant_is_possible_descendant agree ancestral knowledge⟩

/-- Lemma 7, Step 2(i). A strict difference of the `F` sets forces the
stated direction in every compatible MAG. The difference witness cannot
be adjacent to the other endpoint, by Balanced or ancestrality. -/
theorem step2_from_different_f {P : PMG n} {G : MarkedGraph n}
    (balanced : P.BalancedArrowheads) (agree : Agreement P G)
    (gMax : G.HasSeparators) (ancestral : AncestralMarks G) (noSelection : NoSelection G)
    (witness : PreviousTailWitnesses P G) {x v w t : Fin n} {selected : Fin n → Prop}
    (knowledge : LocalChoice P G x selected)
    (vx : v ≠ x) (wx : w ≠ x) (vOutside : ¬ selected v) (wOutside : ¬ selected w)
    (descV : Reach (Directed G) x v) (descW : Reach (Directed G) x w)
    (circle : P.CircleEdge v w) (inF : InF P selected x v t)
    (notInF : ¬ InF P selected x w t) : Directed G v w := by
  have vt : v ≠ t := by
    intro same
    subst t
    rcases inF.1 with same | selected
    · exact vx same
    · exact vOutside selected
  have wt : w ≠ t := by
    intro same
    subst t
    rcases inF.1 with same | selected
    · exact wx same
    · exact wOutside selected
  have vw : v ≠ w := by
    intro same
    subst w
    have edge := circle.1
    simp [P.loop_free] at edge
  have absent : ¬ P.Adjacent t w := by
    intro adjacent
    have reversed := reverse_adjacent adjacent
    obtain ⟨mark, marks⟩ := Option.isSome_iff_exists.mp reversed
    cases mark with
    | circle => exact notInF ⟨inF.1, marks⟩
    | arrow =>
      have head := balanced wt.symm vw.symm vt.symm marks circle.2
      have circleToV := inF.2
      simp [PMG.ArrowInto, circleToV] at head
    | tail =>
      have directed := tail_leaves noSelection ((agree.adjacent w t).mp reversed) (agree.tail marks)
      rcases inF.1 with isX | chosen
      · subst t
        have reverse : G.marks x w = some (true, false) := by
          rw [G.swap_marks w x]
          change G.marks w x = some (false, true) at directed
          rw [directed]
          rfl
        have head : G.arrowheadAt x w = true := by simp [MarkedGraph.arrowheadAt, reverse]
        exact ancestral.no_head_into_ancestor descW head
      · exact descendant_cannot_be_parent_of_selected ancestral knowledge descW chosen directed
  have vtAdjacent : P.Adjacent v t := possible_adjacent (.inr inF.2)
  have head : G.arrowheadAt v t = true := by
    rcases inF.1 with isX | chosen
    · subst t
      have xDir := tail_leaves noSelection ((agree.adjacent x v).mp (reverse_adjacent vtAdjacent))
        (no_head_at_ancestor ancestral descV)
      have reverse : G.marks v x = some (true, false) := by
        rw [G.swap_marks x v]
        change G.marks x v = some (false, true) at xDir
        rw [xDir]
        rfl
      simp [MarkedGraph.arrowheadAt, reverse]
    · exact step1_head_at_descendant ancestral noSelection knowledge descV chosen
        ((agree.adjacent v t).mp vtAdjacent)
  have noncollider := no_new_noncollider_head agree gMax witness vt.symm wt.symm vw
    (reverse_adjacent vtAdjacent) (.inr circle.1) absent
  exact directed_after_noncollider ancestral noncollider head
    ((agree.adjacent v w).mp (possible_adjacent (.inr circle.1)))

/-- Lemma 7, Step 2(ii). A direction already established in the restricted
class propagates through an unshielded circle triple. The rule in
Algorithm 1 additionally requires equality of the two `F` sets. -/
theorem step2_propagates_direction {P : PMG n} {G : MarkedGraph n}
    (agree : Agreement P G) (gMax : G.HasSeparators) (witness : PreviousTailWitnesses P G)
    (ancestral : AncestralMarks G) {a v w : Fin n} (av : a ≠ v) (aw : a ≠ w) (vw : v ≠ w)
    (first : Directed G a v) (circle : P.CircleEdge v w) (absent : ¬ P.Adjacent a w) :
    Directed G v w := by
  have firstAdjacent := (agree.adjacent a v).mpr (directed_adjacent first)
  have noncollider := no_new_noncollider_head agree gMax witness av aw vw firstAdjacent
    (.inr circle.1) absent
  have head : G.arrowheadAt v a = true := by
    change G.marks a v = some (false, true) at first
    simp [MarkedGraph.arrowheadAt, G.swap_marks a v, first, Prod.swap]
  exact directed_after_noncollider ancestral noncollider head
    ((agree.adjacent v w).mp (possible_adjacent (.inr circle.1)))

/-- Lemma 11's no-conflict conclusion follows once both demands have
been shown to hold in one compatible MAG. -/
theorem no_opposing_demands {G : MarkedGraph n} {u v : Fin n}
    (forward : Directed G u v) (reverse : Directed G v u) : False := by
  change G.marks u v = some (false, true) at forward
  change G.marks v u = some (false, true) at reverse
  rw [G.swap_marks u v, forward] at reverse
  cases reverse

end
end OpenCausalScience.Papers.WangQinZhou2023.LocalTransformation
