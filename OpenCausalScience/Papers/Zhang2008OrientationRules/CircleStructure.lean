module
public import OpenCausalScience.Papers.WangQinZhou2023.CircleChordality

/-! The chordality argument for the circle component of augmented FCI
in Zhang (2008), Section 4. The closure properties and the structural
properties P1 and P3 are hypotheses on the partially marked graph.
Source: https://doi.org/10.1016/j.artint.2008.08.001
-/

namespace OpenCausalScience.Papers.Zhang2008OrientationRules.CircleStructure

open MixedGraph (Reach)
open WangQinZhou2023.LocalBackgroundKnowledge (PMG)
open WangQinZhou2023.CircleChordality (CircleChordal CircleCycle circle_distinct)

@[expose] public section

variable {n : Nat} {P : PMG n}

/-- The part of P3 that propagates a tail–circle edge past a circle edge. -/
def P3Circle (P : PMG n) : Prop :=
  ∀ {a b c : Fin n}, a ≠ b → b ≠ c → a ≠ c →
    P.markAt a b = some .tail → P.markAt b a = some .circle → P.CircleEdge b c →
      P.markAt a c = some .tail ∧ P.markAt c a = some .circle

/-- The R6 consequence for a remaining circle at an endpoint. -/
def R6Closed (P : PMG n) : Prop :=
  ∀ {u v w : Fin n}, P.markAt u v = some .tail → P.markAt v u = some .tail →
    P.markAt u w ≠ some .circle

/-- One of the endpoint conclusions of R5, sufficient to rule out a
remaining uncovered circle cycle. -/
def R5Closed (P : PMG n) : Prop :=
  ∀ {vertices : Nat → Fin n} {length : Nat}, 3 ≤ length →
    P.CircleEdge (vertices 0) (vertices length) →
    (∀ i, i < length → P.CircleEdge (vertices i) (vertices (i + 1))) →
    (∀ {i j}, i ≤ length → j ≤ length → vertices i = vertices j → i = j) →
    (∀ i, i + 1 < length → ¬ P.Adjacent (vertices i) (vertices (i + 2))) →
    (¬ P.Adjacent (vertices 0) (vertices (length - 1))) →
    (¬ P.Adjacent (vertices 1) (vertices length)) →
    P.markAt (vertices 0) (vertices length) = some .tail

private theorem reverse_circle {u v : Fin n} (edge : P.CircleEdge u v) : P.CircleEdge v u :=
  ⟨edge.2, edge.1⟩

private theorem reach_trans {u v w : Fin n} (left : Reach P.CircleEdge u v)
    (right : Reach P.CircleEdge v w) : Reach P.CircleEdge u w := by
  induction right with
  | refl => exact left
  | extend _ edge ih => exact .extend ih edge

private theorem reverse_reach {u v : Fin n} (reach : Reach P.CircleEdge u v) :
    Reach P.CircleEdge v u := by
  induction reach with
  | refl => exact .refl _
  | extend _ edge prior => exact reach_trans (.extend (.refl _) (reverse_circle edge)) prior

/-- The tail end of a tail–circle edge cannot lie in the same circle
component as its circle end. -/
theorem tail_circle_source_outside (p3 : P3Circle P) {a b : Fin n}
    (tail : P.markAt a b = some .tail) (circle : P.markAt b a = some .circle) :
    ¬ Reach P.CircleEdge b a := by
  intro path
  have propagated {c} (reach : Reach P.CircleEdge b c) :
      P.markAt a c = some .tail ∧ P.markAt c a = some .circle := by
    induction reach with
    | refl => exact ⟨tail, circle⟩
    | @extend u v prior edge ih =>
      have distinctU : a ≠ u := by
        intro same
        subst u
        have atLoop := ih.1
        simp [P.loop_free] at atLoop
      have distinctV : a ≠ v := by
        intro same
        subst v
        have first := edge.2
        simp [ih.1] at first
      exact p3 distinctU (circle_distinct edge) distinctV ih.1 ih.2 edge
  have atLoop := (propagated path).1
  simp [P.loop_free] at atLoop

/-- Under P1, P3 and R6 closure, any adjacency between vertices in a
circle component is a circle edge. This allows selection tails. -/
theorem adjacent_in_circle_component (p1 : P.BalancedArrowheads) (p3 : P3Circle P)
    (r6 : R6Closed P) {u v : Fin n} (path : Reach P.CircleEdge u v)
    (uIncident : ∃ w, P.CircleEdge u w) (vIncident : ∃ w, P.CircleEdge v w)
    (adjacent : P.Adjacent u v) : P.CircleEdge u v := by
  have circleMark {a b : Fin n} (path : Reach P.CircleEdge a b)
      (aIncident : ∃ w, P.CircleEdge a w) (adjacent : P.Adjacent a b) :
      P.markAt a b = some .circle := by
    obtain ⟨mark, actual⟩ := Option.isSome_iff_exists.mp adjacent
    cases mark with
    | circle => exact actual
    | arrow => exact (PMG.source_outside_circle_component p1 actual path).elim
    | tail =>
      have reverse : P.Adjacent b a := (P.same_adjacencies b a).trans adjacent
      obtain ⟨other, otherActual⟩ := Option.isSome_iff_exists.mp reverse
      cases other with
      | arrow => exact (PMG.source_outside_circle_component p1 otherActual (reverse_reach path)).elim
      | circle => exact (tail_circle_source_outside p3 actual otherActual (reverse_reach path)).elim
      | tail =>
        obtain ⟨w, edge⟩ := aIncident
        exact (r6 actual otherActual edge.1).elim
  exact ⟨circleMark path uIncident adjacent,
    circleMark (reverse_reach path) vIncident ((P.same_adjacencies v u).trans adjacent)⟩

/-- Circle chordality under the structural properties P1 and P3 and
closure under R5 and R6. A circle cycle with no circle chord would also
have no skeleton chord and would therefore trigger R5. -/
theorem chordal_of_r5_closed (p1 : P.BalancedArrowheads) (p3 : P3Circle P)
    (r6 : R6Closed P) (r5 : R5Closed P) : CircleChordal P := by
  intro vertices length cycle
  have large := cycle.large
  apply Classical.byContradiction
  intro noChord
  have reaches : ∀ i, i < length → Reach P.CircleEdge (vertices 0) (vertices i) := by
    intro i
    induction i with
    | zero => exact fun _ => .refl _
    | succ i ih => exact fun bound => .extend (ih (by omega)) (cycle.along i bound)
  have incident i (bound : i < length) : ∃ w, P.CircleEdge (vertices i) w := by
    by_cases next : i + 1 < length
    · exact ⟨vertices (i + 1), cycle.along i next⟩
    · have last : i = length - 1 := by omega
      exact ⟨vertices 0, last ▸ cycle.closing⟩
  have absent {i j : Nat} (apart : i + 1 < j) (bound : j < length)
      (notEnds : i ≠ 0 ∨ j + 1 < length) : ¬ P.Adjacent (vertices i) (vertices j) := by
    intro adjacent
    have earlier : i < length := by omega
    have path := reach_trans (reverse_reach (reaches i earlier)) (reaches j bound)
    have chord := adjacent_in_circle_component p1 p3 r6 path (incident i earlier) (incident j bound) adjacent
    exact noChord ⟨i, j, apart, bound, notEnds, chord⟩
  have closure : P.markAt (vertices 0) (vertices (length - 1)) = some .tail :=
    r5 (length := length - 1) (by omega) (reverse_circle cycle.closing)
      (fun i step => cycle.along i (by omega))
      (fun hi hj same => cycle.simple (by omega) (by omega) same)
      (fun i step => absent (by omega) (by omega) (by omega))
      (absent (by omega) (by omega) (Or.inr (by omega)))
      (absent (by omega) (by omega) (Or.inl (by omega)))
  simp [cycle.closing.2] at closure

end
end OpenCausalScience.Papers.Zhang2008OrientationRules.CircleStructure
