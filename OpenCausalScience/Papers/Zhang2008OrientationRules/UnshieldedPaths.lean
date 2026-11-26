module
public import OpenCausalScience.Papers.Zhang2008OrientationRules.Orientations

/-! # Orientation rules using unshielded triples and paths

Zhang (2008), R0, R3, R5–R7, R9 and R10. Once R0 has determined the
noncolliders, the path rules propagate a directed edge through successive
noncolliders. The proofs are over compatible fully marked graphs.

Source: https://doi.org/10.1016/j.artint.2008.08.001
-/

namespace OpenCausalScience.Papers.Zhang2008OrientationRules.UnshieldedPaths

open MarkedGraph
open MixedGraph (Reach)
open Orientations (AncestralMarks Directed r2_sound)

@[expose] public section

variable {n : Nat}

/-- R0. In an unshielded triple, the middle vertex is a collider exactly
when a separating set for the two endpoints does not contain it. -/
theorem r0_collider_iff_outside_separator {G : MarkedGraph n} {a b c : Fin n}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (first : G.adjacent a b = true)
    (second : G.adjacent b c = true) (absent : G.adjacent a c = false)
    {cond : BitVec n} (separates : G.MSeparated a c cond) :
    G.collider a b c = true ↔ conditioned cond b = false := by
  constructor
  · intro collider
    exact G.collider_excluded_from_separator ⟨ab, ac, bc, first, second, absent, collider⟩ separates
  · intro outside
    cases collider : G.collider a b c with
    | true => rfl
    | false =>
      have inside := G.noncollider_in_separator ab ac bc first second collider separates
      simp [outside] at inside

/-- The noncollider information supplied by R0 persists in every
Markov-equivalent maximal graph. -/
theorem unshielded_noncollider_invariant {G H : MarkedGraph n}
    (gMax : G.HasSeparators) (hMax : H.HasSeparators) (equivalent : G.SameSeparations H)
    {a b c : Fin n} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (first : G.adjacent a b = true) (second : G.adjacent b c = true)
    (absent : G.adjacent a c = false) (noncollider : G.collider a b c = false) :
    H.collider a b c = false := by
  have same := AliRichardsonSpirtes2009.equivalent_adjacencies gMax hMax equivalent
  cases collider : H.collider a b c with
  | false => rfl
  | true =>
    have transferred := (AliRichardsonSpirtes2009.equivalent_unshielded_colliders
      gMax hMax equivalent a b c).mpr
        ⟨ab, ac, bc, (same a b).symm.trans first, (same b c).symm.trans second,
          (same a c).symm.trans absent, collider⟩
    simp [MarkedGraph.UnshieldedCollider, noncollider] at transferred

private theorem edge_marks_reverse {G : MarkedGraph n} {u v : Fin n} {p q : Bool}
    (edge : G.marks u v = some (p, q)) : G.marks v u = some (q, p) := by
  rw [G.swap_marks u v, edge]
  rfl

private theorem directed_head {G : MarkedGraph n} {u v : Fin n}
    (edge : Directed G u v) : G.arrowheadAt v u = true :=
  by simp [MarkedGraph.arrowheadAt, edge_marks_reverse edge]

/-- A tail at a vertex with an incident arrowhead starts a directed edge. -/
theorem directed_of_tail_and_incident_head {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {u v w : Fin n} (edge : G.adjacent u v = true) (tail : G.arrowheadAt u v = false)
    (head : G.arrowheadAt u w = true) : Directed G u v := by
  obtain ⟨⟨near, far⟩, marks⟩ := Option.isSome_iff_exists.mp edge
  cases near with
  | true => simp [MarkedGraph.arrowheadAt, marks] at tail
  | false =>
    cases far with
    | false => have absent := ancestral.no_head_at_undirected marks (w := w); simp [head] at absent
    | true => exact marks

/-- The directed-edge propagation used in the proofs of R5, R9 and R10. -/
theorem directed_after_noncollider {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {a b c : Fin n} (noncollider : G.collider a b c = false)
    (head : G.arrowheadAt b a = true) (edge : G.adjacent b c = true) :
    Directed G b c := by
  have out : G.arrowheadAt b c = false := by
    simpa [MarkedGraph.collider, head] using noncollider
  exact directed_of_tail_and_incident_head ancestral edge out head

/-- R3. The outer triple's noncollider status is the R0 information for
the triple `A-D-C`. The head forced by R3 is at `B` on `BD`. -/
theorem r3_sound {G : MarkedGraph n} (ancestral : AncestralMarks G) {a b c d : Fin n}
    (ab : G.arrowheadAt b a = true) (cb : G.arrowheadAt b c = true)
    (ad : G.adjacent a d = true) (cd : G.adjacent c d = true)
    (bd : G.adjacent b d = true) (noncollider : G.collider a d c = false) :
    G.arrowheadAt b d = true := by
  cases mark : G.arrowheadAt b d with
  | true => rfl
  | false =>
    have bdDir := directed_of_tail_and_incident_head ancestral bd mark ab
    have aHead := r2_sound ancestral ad (Or.inr ⟨ab, bdDir⟩)
    have cHead := r2_sound ancestral cd (Or.inr ⟨cb, bdDir⟩)
    simp [MarkedGraph.collider, aHead, cHead] at noncollider

/-- R6. An undirected edge rules out a head at the shared endpoint. -/
theorem r6_sound {G : MarkedGraph n} (ancestral : AncestralMarks G) {a b c : Fin n}
    (undirected : G.marks a b = some (false, false)) : G.arrowheadAt b c = false :=
  ancestral.no_head_at_undirected (edge_marks_reverse undirected)

/-- R7. A tail at the first vertex of an unshielded noncollider forces a
tail at the middle vertex on its second edge. -/
theorem r7_sound {G : MarkedGraph n} (ancestral : AncestralMarks G) {a b c : Fin n} {other : Bool}
    (first : G.marks a b = some (false, other)) (noncollider : G.collider a b c = false) :
    G.arrowheadAt b c = false := by
  cases other with
  | false => exact r6_sound ancestral first
  | true =>
    have head := directed_head first
    simpa [MarkedGraph.collider, head] using noncollider

/-- All consecutive triples along the supplied path are unshielded
noncolliders after R0. This condition is carried across the class. -/
structure NoncolliderPath (G : MarkedGraph n) (vertices : Nat → Fin n) (length : Nat) : Prop where
  adjacent : ∀ i, i < length → G.adjacent (vertices i) (vertices (i + 1)) = true
  noncollider : ∀ i, i + 1 < length → G.collider (vertices i) (vertices (i + 1)) (vertices (i + 2)) = false

theorem direct_noncollider_path {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {vertices : Nat → Fin n} {length : Nat} (path : NoncolliderPath G vertices length)
    (first : Directed G (vertices 0) (vertices 1)) :
    ∀ k, k < length → Directed G (vertices k) (vertices (k + 1)) := by
  intro k
  induction k with
  | zero => exact fun _ => first
  | succ k ih =>
    intro bound
    have previous := directed_head (ih (by omega))
    exact directed_after_noncollider ancestral (path.noncollider k (by omega)) previous
      (path.adjacent (k + 1) bound)

theorem reach_end_of_directed_path {G : MarkedGraph n}
    {vertices : Nat → Fin n} {length : Nat}
    (directed : ∀ k, k < length → Directed G (vertices k) (vertices (k + 1))) :
    Reach (Directed G) (vertices 0) (vertices length) := by
  have reach : ∀ k, k ≤ length → Reach (Directed G) (vertices 0) (vertices k) := by
    intro k
    induction k with
    | zero => exact fun _ => .refl _
    | succ k ih => exact fun bound => .extend (ih (by omega)) (directed k (by omega))
  exact reach length (Nat.le_refl _)

/-- R5 in any traversal of its uncovered circle cycle. The index starts
with the edge under test and ends back at the first vertex. R0 provides
the noncollider status of the cycle triples. -/
theorem r5_no_head_in_cycle_traversal {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {vertices : Nat → Fin n} {length : Nat} (lengthGe : 1 < length)
    (path : NoncolliderPath G vertices length) (closed : vertices length = vertices 0) :
    G.arrowheadAt (vertices 1) (vertices 0) = false := by
  cases head : G.arrowheadAt (vertices 1) (vertices 0) with
  | false => rfl
  | true =>
    let tail := fun i => vertices (i + 1)
    have nonempty : 0 < length - 1 := by omega
    have tailPath : NoncolliderPath G tail (length - 1) := by
      refine ⟨?_, ?_⟩
      · intro i hi; exact path.adjacent (i + 1) (by omega)
      · intro i hi; exact path.noncollider (i + 1) (by omega)
    have first := directed_after_noncollider ancestral (path.noncollider 0 lengthGe)
      head (path.adjacent 1 lengthGe)
    have directed := direct_noncollider_path ancestral tailPath first
    have reaches := reach_end_of_directed_path directed
    change Reach (Directed G) (vertices 1) (vertices (length - 1 + 1)) at reaches
    have index : length - 1 + 1 = length := by omega
    rw [index, closed] at reaches
    exact (ancestral.no_head_into_ancestor reaches head).elim

private theorem adjacent_reverse {G : MarkedGraph n} {u v : Fin n}
    (forward : G.adjacent u v = true) : G.adjacent v u = true := by
  simpa [MarkedGraph.adjacent, G.swap_marks u v] using forward

/-- R5. Each edge on an uncovered cycle whose triples are noncolliders
must be undirected. Read the cycle in both directions starting with the
edge under test. -/
theorem r5_sound {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {vertices : Nat → Fin n} {length : Nat} (nontrivial : 1 < length)
    (periodic : ∀ i, vertices (i + length) = vertices i)
    (edge : ∀ i, G.adjacent (vertices i) (vertices (i + 1)) = true)
    (status : ∀ i, G.collider (vertices i) (vertices (i + 1)) (vertices (i + 2)) = false)
    (i : Nat) : G.marks (vertices i) (vertices (i + 1)) = some (false, false) := by
  let forward := fun k => vertices (i + k)
  let reverse := fun k => vertices (i + 1 + (length - k))
  have forwardPath : NoncolliderPath G forward length :=
    ⟨fun k _ => edge (i + k), fun k _ => status (i + k)⟩
  have reversePath : NoncolliderPath G reverse length := by
    constructor
    · intro k bound
      have index : i + 1 + (length - (k + 1)) + 1 = i + 1 + (length - k) := by omega
      exact adjacent_reverse (by simpa [index] using edge (i + 1 + (length - (k + 1))))
    · intro k bound
      have middle : i + 1 + (length - (k + 2)) + 1 = i + 1 + (length - (k + 1)) := by omega
      have last : i + 1 + (length - (k + 2)) + 2 = i + 1 + (length - k) := by omega
      simpa [reverse, middle, last, MarkedGraph.collider, Bool.and_comm] using
        status (i + 1 + (length - (k + 2)))
  have noFar := r5_no_head_in_cycle_traversal ancestral nontrivial forwardPath
    (show forward length = forward 0 from periodic i)
  have noNear := r5_no_head_in_cycle_traversal ancestral nontrivial reversePath
    (show reverse length = reverse 0 by simp [reverse, periodic])
  have oneBack : i + 1 + (length - 1) = i + length := by omega
  have far : G.arrowheadAt (vertices (i + 1)) (vertices i) = false := noFar
  have near : G.arrowheadAt (vertices i) (vertices (i + 1)) = false := by
    simpa [reverse, oneBack, periodic] using noNear
  obtain ⟨⟨nearMark, farMark⟩, marks⟩ := Option.isSome_iff_exists.mp (edge i)
  have nearTail : nearMark = false := by simpa [MarkedGraph.arrowheadAt, marks] using near
  have farTail : farMark = false := by
    simpa [MarkedGraph.arrowheadAt, edge_marks_reverse marks] using far
  simp [marks, nearTail, farTail]

/-- R9. The cross triple made by the proposed shortcut and first path
edge is an unshielded noncollider. A bidirected shortcut would make the
entire path directed, contrary to ancestrality. -/
theorem r9_sound {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {vertices : Nat → Fin n} {length : Nat} (nonempty : 0 < length)
    (path : NoncolliderPath G vertices length)
    (cross : G.collider (vertices length) (vertices 0) (vertices 1) = false)
    {near : Bool} (shortcut : G.marks (vertices 0) (vertices length) = some (near, true)) :
    Directed G (vertices 0) (vertices length) := by
  cases near with
  | false => exact shortcut
  | true =>
    have head : G.arrowheadAt (vertices 0) (vertices length) = true :=
      by simp [MarkedGraph.arrowheadAt, shortcut]
    have first := directed_after_noncollider ancestral cross head (path.adjacent 0 nonempty)
    have directed := direct_noncollider_path ancestral path first
    exact (ancestral.no_head_into_ancestor (reach_end_of_directed_path directed) head).elim

/-- R10. The two first neighbours and the common start form an unshielded
noncollider. At least one path must be directed if the shortcut were
bidirected, putting the start among the target's ancestors. -/
theorem r10_sound {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {left right : Nat → Fin n} {leftLength rightLength : Nat}
    (leftNonempty : 0 < leftLength) (rightNonempty : 0 < rightLength)
    (leftPath : NoncolliderPath G left leftLength) (rightPath : NoncolliderPath G right rightLength)
    {a c : Fin n} (leftStart : left 0 = a) (rightStart : right 0 = a)
    (leftParent : Directed G (left leftLength) c) (rightParent : Directed G (right rightLength) c)
    (cross : G.collider (left 1) a (right 1) = false)
    {near : Bool} (shortcut : G.marks a c = some (near, true)) : Directed G a c := by
  cases near with
  | false => exact shortcut
  | true =>
    have head : G.arrowheadAt a c = true := by simp [MarkedGraph.arrowheadAt, shortcut]
    have reaches : Reach (Directed G) a c := by
      cases leftMark : G.arrowheadAt a (left 1) with
      | false =>
        have first := directed_of_tail_and_incident_head ancestral (leftPath.adjacent 0 leftNonempty)
          (by simpa [leftStart] using leftMark) (by simpa [leftStart] using head)
        have path := reach_end_of_directed_path (direct_noncollider_path ancestral leftPath first)
        exact .extend (by simpa [leftStart] using path) leftParent
      | true =>
        have rightMark : G.arrowheadAt a (right 1) = false := by
          simpa [MarkedGraph.collider, leftMark] using cross
        have first := directed_of_tail_and_incident_head ancestral (rightPath.adjacent 0 rightNonempty)
          (by simpa [rightStart] using rightMark) (by simpa [rightStart] using head)
        have path := reach_end_of_directed_path (direct_noncollider_path ancestral rightPath first)
        exact .extend (by simpa [rightStart] using path) rightParent
    exact (ancestral.no_head_into_ancestor reaches head).elim

end
end OpenCausalScience.Papers.Zhang2008OrientationRules.UnshieldedPaths
