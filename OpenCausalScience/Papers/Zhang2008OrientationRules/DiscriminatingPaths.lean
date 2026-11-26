module
public import OpenCausalScience.Papers.Zhang2008OrientationRules.UnshieldedPaths

/-! # Discriminating paths and rule R4

A discriminating path makes the final triple distinguishable by an
m-separating set. Before the distinguished vertex, every interior
vertex is a collider and a parent of the endpoint. Truncating the path
at each such parent and adding its directed edge to the endpoint shows
that the parent belongs to the separating set.

Source: https://doi.org/10.1016/j.artint.2008.08.001
-/

namespace OpenCausalScience.Papers.Zhang2008OrientationRules.DiscriminatingPaths

open MarkedGraph
open MixedGraph (Reach)
open Orientations (AncestralMarks Directed)

@[expose] public section

variable {n : Nat}

/-- The prefix of a discriminating path, up to the vertex whose collider
status is tested. The last two vertices are separated from the earlier
vertices to make the last turn explicit. -/
inductive DiscriminatingPrefix (G : MarkedGraph n) (source target : Fin n) :
    List (Fin n) → Fin n → Fin n → Prop where
  | initial {v : Fin n} : G.adjacent source v = true → DiscriminatingPrefix G source target [] source v
  | extend {earlier : List (Fin n)} {u v w : Fin n} :
      DiscriminatingPrefix G source target earlier u v →
      G.collider u v w = true → Directed G v target → G.adjacent v w = true →
      DiscriminatingPrefix G source target (earlier ++ [u]) v w

private theorem DiscriminatingPrefix.starts {G : MarkedGraph n} {source target u v : Fin n}
    {earlier tail : List (Fin n)} (p : DiscriminatingPrefix G source target earlier u v) :
    (earlier ++ u :: v :: tail).head? = some source := by
  induction p with
  | initial => rfl
  | extend _ _ _ _ ih => simpa [List.append_assoc] using ih

private theorem DiscriminatingPrefix.last_edge {G : MarkedGraph n} {source target u v : Fin n}
    {earlier : List (Fin n)} (p : DiscriminatingPrefix G source target earlier u v) :
    G.adjacent u v = true := by
  cases p with
  | initial edge => exact edge
  | extend _ _ _ edge => exact edge

private theorem active_prefix_of_separator {G : MarkedGraph n} {source target u v : Fin n}
    {earlier : List (Fin n)} (p : DiscriminatingPrefix G source target earlier u v)
    (simple : (earlier ++ [u, v, target]).Nodup) {cond : BitVec n}
    (separates : G.MSeparated source target cond) :
    ∀ tail, G.activePath cond (u :: v :: tail) = true →
      G.activePath cond (earlier ++ u :: v :: tail) = true := by
  induction p with
  | initial => exact fun _ active => active
  | @extend earlier u v w prior collider parent adjacent ih =>
    have sublist : (earlier ++ [u, v, target]).Sublist
        ((earlier ++ [u]) ++ [v, w, target]) := by
      rw [List.append_assoc]
      exact (((List.Sublist.refl [target]).cons w).cons_cons v).cons_cons u |>.append_left earlier
    have activeBefore := ih (sublist.nodup simple)
    have vIn : conditioned cond v = true := by
      cases membership : conditioned cond v with
      | true => rfl
      | false =>
        change G.marks v target = some (false, true) at parent
        have tailMark : G.arrowheadAt v target = false := by
          simp [MarkedGraph.arrowheadAt, parent]
        have shortcut : G.adjacent v target = true := by simp [MarkedGraph.adjacent, parent]
        have openShortcut : G.activePath cond [u, v, target] = true := by
          simp [MarkedGraph.activePath, prior.last_edge, MarkedGraph.collider, tailMark, membership,
            shortcut]
        exact (separates ⟨earlier ++ [u, v, target], sublist.nodup simple,
          prior.starts (tail := [target]), by simp [List.getLast?_append],
          activeBefore [target] openShortcut⟩).elim
    intro tail active
    have openTurn : G.activePath cond (u :: v :: w :: tail) = true := by
      simp only [MarkedGraph.activePath, prior.last_edge, collider, ite_true,
        G.activated_of_conditioned cond v vIn, Bool.and_self, Bool.true_and]
      exact active
    simpa [List.append_assoc] using activeBefore (w :: tail) openTurn

/-- The separator test for the last triple of a discriminating path.
It is independent of the choice of separating set. -/
theorem collider_iff_outside_separator {G : MarkedGraph n} {source a b c : Fin n}
    {earlier : List (Fin n)} (path : DiscriminatingPrefix G source c earlier a b)
    (simple : (earlier ++ [a, b, c]).Nodup) (last : G.adjacent b c = true)
    {cond : BitVec n} (separates : G.MSeparated source c cond) :
    G.collider a b c = true ↔ conditioned cond b = false := by
  have previous := path.last_edge
  have impossible : G.activePath cond [a, b, c] = true → False := by
    intro active
    exact separates ⟨earlier ++ [a, b, c], simple, path.starts (tail := [c]),
      by simp [List.getLast?_append], active_prefix_of_separator path simple separates [c] active⟩
  constructor
  · intro collider
    cases membership : conditioned cond b with
    | false => rfl
    | true =>
      exact (impossible (by simp [MarkedGraph.activePath, previous, collider, last,
        G.activated_of_conditioned cond b membership])).elim
  · intro membership
    cases collider : G.collider a b c with
    | true => rfl
    | false =>
      exact (impossible (by simp [MarkedGraph.activePath, previous, collider, last, membership])).elim

private theorem endpoint_head {G : MarkedGraph n} {u v : Fin n}
    (edge : Directed G u v) : G.arrowheadAt v u = true := by
  change G.marks u v = some (false, true) at edge
  simp [MarkedGraph.arrowheadAt, G.swap_marks u v, edge, Prod.swap]

private theorem marks_with_two_heads {G : MarkedGraph n} {u v : Fin n}
    (near : G.arrowheadAt u v = true) (far : G.arrowheadAt v u = true) :
    G.marks u v = some (true, true) := by
  cases mark : G.marks u v with
  | none => simp [MarkedGraph.arrowheadAt, mark] at near
  | some pair =>
    obtain ⟨p, q⟩ := pair
    have pHead : p = true := by simpa [MarkedGraph.arrowheadAt, mark] using near
    have qHead : q = true := by
      simpa [MarkedGraph.arrowheadAt, G.swap_marks u v, mark, Prod.swap] using far
    simp [pHead, qHead]

/-- Both orientation branches of R4. The penultimate collider is a
parent of the endpoint, and its edge to the distinguished vertex has
an arrowhead at the penultimate collider. -/
theorem r4_sound {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {source a b c : Fin n} {earlier : List (Fin n)}
    (path : DiscriminatingPrefix G source c earlier a b)
    (simple : (earlier ++ [a, b, c]).Nodup) (last : G.adjacent b c = true)
    (parent : Directed G a c) (headAtA : G.arrowheadAt a b = true)
    {cond : BitVec n} (separates : G.MSeparated source c cond) :
    (conditioned cond b = true → Directed G b c) ∧
    (conditioned cond b = false → G.marks a b = some (true, true) ∧
      G.marks b c = some (true, true)) := by
  have status := collider_iff_outside_separator path simple last separates
  constructor
  · intro membership
    obtain ⟨⟨near, far⟩, mark⟩ := Option.isSome_iff_exists.mp last
    cases near with
    | false =>
      cases far with
      | true => exact mark
      | false =>
        have noHead : G.arrowheadAt c a = false :=
          UnshieldedPaths.r6_sound ancestral mark
        have head := endpoint_head parent
        simp [head] at noHead
    | true =>
      have bToCHead : G.arrowheadAt b c = true := by simp [MarkedGraph.arrowheadAt, mark]
      have bToATail : G.arrowheadAt b a = false := by
        cases bToA : G.arrowheadAt b a with
        | false => rfl
        | true =>
          have collider : G.collider a b c = true := by simp [MarkedGraph.collider, bToA, bToCHead]
          have outside := status.mp collider
          simp [membership] at outside
      have bToA : Directed G b a := by
        have aToB : G.marks a b = some (true, false) := by
          cases edge : G.marks a b with
          | none => simp [MarkedGraph.arrowheadAt, edge] at headAtA
          | some marks =>
            obtain ⟨p, q⟩ := marks
            have pHead : p = true := by simpa [MarkedGraph.arrowheadAt, edge] using headAtA
            have qTail : q = false := by
              simpa [MarkedGraph.arrowheadAt, G.swap_marks a b, edge, Prod.swap] using bToATail
            simp [pHead, qTail]
        change G.marks b a = some (false, true)
        rw [G.swap_marks a b, aToB]
        rfl
      exact (ancestral.no_head_into_ancestor
        (.extend (.extend (.refl b) bToA) parent) bToCHead).elim
  · intro membership
    have collider := status.mpr membership
    simp only [MarkedGraph.collider, Bool.and_eq_true] at collider
    obtain ⟨headBA, headBC⟩ := collider
    refine ⟨marks_with_two_heads headAtA headBA, marks_with_two_heads headBC ?_⟩
    cases headCA : G.arrowheadAt c b with
    | true => rfl
    | false =>
      have adjacentCB : G.adjacent c b = true := by
        simpa [MarkedGraph.adjacent, G.swap_marks b c] using last
      have cToB := UnshieldedPaths.directed_of_tail_and_incident_head ancestral adjacentCB
        headCA (endpoint_head parent)
      exact (ancestral.no_head_into_ancestor
        (.extend (.extend (.refl a) parent) cToB) headAtA).elim

end
end OpenCausalScience.Papers.Zhang2008OrientationRules.DiscriminatingPaths
