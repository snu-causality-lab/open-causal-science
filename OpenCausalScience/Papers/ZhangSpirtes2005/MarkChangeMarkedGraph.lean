module
public import OpenCausalScience.Papers.ZhangSpirtes2005.MarkChangeSeparation

/-! The matching-parent and matching-spouse criterion in terms of the
singly marked graph's singleton separation relation. -/

namespace OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange

open MixedGraph (Arrival ActiveWalk openTurn)
open MarkedGraph (conditioned)

@[expose] public section

variable {n : Nat} {G : MarkedGraph n} {noLines : NoLines G}

private theorem keeps_arrows_on_suffix {u : Fin n} (front rest : List (Fin n))
    (arrows : G.followsArrows (front ++ u :: rest) = true) : G.followsArrows (u :: rest) = true := by
  induction front with
  | nil => exact arrows
  | cons v front ih =>
    apply ih
    cases front with
    | nil =>
      change G.directed v u && G.followsArrows (u :: rest) = true at arrows
      exact ((Bool.and_eq_true _ _).mp arrows).2
    | cons w front =>
      change G.directed v w && G.followsArrows (w :: (front ++ u :: rest)) = true at arrows
      exact ((Bool.and_eq_true _ _).mp arrows).2

private theorem ancestor_of_arrows {C : BitVec n} (u : Fin n) (rest : List (Fin n))
    (arrows : G.followsArrows (u :: rest) = true)
    (lastInC : (u :: rest).getLast?.any (conditioned C) = true) :
    (asMixed G noLines).AncestorOf (conditioned C) u := by
  induction rest generalizing u with
  | nil => exact .conditioned (by simpa using lastInC)
  | cons v rest ih =>
    change G.directed u v && G.followsArrows (v :: rest) = true at arrows
    obtain ⟨edge, tail⟩ := (Bool.and_eq_true _ _).mp arrows
    have marked : G.marks u v = some (false, true) := by simpa [MarkedGraph.directed] using edge
    exact .parent (decide_eq_true marked)
      (ih v tail (by simpa only [List.getLast?_cons_cons] using lastInC))

private theorem marked_ancestry_iff {C : BitVec n} {v : Fin n} :
    G.activated C v = true ↔ (asMixed G noLines).AncestorOf (conditioned C) v := by
  rw [G.activated_iff]
  constructor
  · rintro ⟨path, _, first, last, arrows⟩
    cases path with
    | nil => simp at first
    | cons u rest =>
      simp only [List.head?_cons, Option.some.injEq] at first
      subst u
      exact ancestor_of_arrows v rest arrows last
  · intro active
    induction active with
    | @conditioned u mem => exact ⟨[u], by simp, rfl, mem, rfl⟩
    | @parent u v edge active ih =>
      obtain ⟨route, simple, first, last, arrows⟩ := ih
      by_cases visit : u ∈ route
      · obtain ⟨front, rest, rfl⟩ := List.mem_iff_append.mp visit
        refine ⟨u :: rest, (List.nodup_append.mp simple).2.1, rfl, ?_,
          keeps_arrows_on_suffix front rest arrows⟩
        have suf : (u :: rest).getLast? = (front ++ u :: rest).getLast? := by
          rw [List.getLast?_append, List.getLast?_cons]
          simp
        rwa [suf]
      · cases route with
        | nil => simp at first
        | cons w rest =>
          simp only [List.head?_cons, Option.some.injEq] at first
          subst w
          have marked : G.marks u v = some (false, true) := of_decide_eq_true edge
          refine ⟨u :: v :: rest, List.nodup_cons.mpr ⟨visit, simple⟩, rfl, ?_, ?_⟩
          · simpa only [List.getLast?_cons_cons] using last
          · simp [MarkedGraph.followsArrows, MarkedGraph.directed, marked, arrows]

private theorem turn_iff {C : BitVec n} {u v w : Fin n} {p i o q : Bool}
    (first : G.marks u v = some (p, i)) (second : G.marks v w = some (o, q)) :
    (if G.collider u v w then G.activated C v else !conditioned C v) = true ↔
    (asMixed G noLines).openTurn (conditioned C) (v, i) o := by
  have collider : G.collider u v w = (i && o) := by
    simp [MarkedGraph.collider, MarkedGraph.arrowheadAt, G.swap_marks u v, first, second, Prod.swap]
  rw [collider]
  cases i <;> cases o <;> simp [openTurn, marked_ancestry_iff (noLines := noLines)]

private theorem path_adjacent {u v : Fin n} {rest : List (Fin n)} {C : BitVec n}
    (active : G.activePath C (u :: v :: rest) = true) : G.adjacent u v = true := by
  cases rest with
  | nil => exact active
  | cons w rest => exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp active).1).1

private theorem path_iff_walk {C : BitVec n} {u v : Fin n} {p i : Bool} {rest : List (Fin n)}
    (first : G.marks u v = some (p, i)) :
    G.activePath C (u :: v :: rest) = true ↔
    ∃ final, (asMixed G noLines).ActiveWalk (conditioned C) (v, i) rest final ∧
      (v :: rest).getLast? = some final.1 := by
  induction rest generalizing u v p i with
  | nil =>
    constructor
    · intro _
      exact ⟨(v, i), .nil _, rfl⟩
    · intro _
      simp [MarkedGraph.activePath, MarkedGraph.adjacent, first]
  | cons w rest ih =>
    constructor
    · intro active
      change (G.adjacent u v && (if G.collider u v w then G.activated C v else !conditioned C v) &&
        G.activePath C (v :: w :: rest)) = true at active
      obtain ⟨front, tail⟩ := (Bool.and_eq_true _ _).mp active
      obtain ⟨_, turn⟩ := (Bool.and_eq_true _ _).mp front
      obtain ⟨⟨o, q⟩, second⟩ := Option.isSome_iff_exists.mp (path_adjacent tail)
      obtain ⟨final, walk, last⟩ := (ih second).mp tail
      have edge : (asMixed G noLines).edge v o w q = true := by
        exact decide_eq_true second
      exact ⟨final, .cons ⟨o, edge, (turn_iff first second).mp turn⟩ walk,
        by simpa only [List.getLast?_cons_cons] using last⟩
    · rintro ⟨final, walk, last⟩
      cases walk with
      | @cons _ next _ _ move suffix =>
        obtain ⟨o, edge, turn⟩ := move
        have second : G.marks v next.1 = some (o, next.2) := of_decide_eq_true edge
        have openTurn := (turn_iff first second).mpr turn
        have tail := (ih second).mpr ⟨final, suffix, by simpa only [List.getLast?_cons_cons] using last⟩
        simp only [MarkedGraph.activePath, MarkedGraph.adjacent, first, Option.isSome_some,
          Bool.true_and, openTurn, tail]

private theorem walk_last {C : BitVec n} {start final : Arrival n} {visited : List (Fin n)}
    (walk : (asMixed G noLines).ActiveWalk (conditioned C) start visited final) :
    (start.1 :: visited).getLast? = some final.1 := by
  induction walk with
  | nil => rfl
  | cons step _ ih => simpa only [List.getLast?_cons_cons] using ih

/-- The singleton queries of the two path definitions agree. -/
theorem marked_connected_iff_mixed_path {x y : Fin n} {C : BitVec n} (distinct : x ≠ y) :
    G.MConnected x y C ↔
      (asMixed G noLines).PathConnected (· == x) (· == y) (conditioned C) := by
  constructor
  · rintro ⟨path, simple, first, last, active⟩
    cases path with
    | nil => simp at first
    | cons u rest =>
      simp only [List.head?_cons, Option.some.injEq] at first
      subst u
      cases rest with
      | nil => exact (distinct (by simpa using last)).elim
      | cons v rest =>
        obtain ⟨⟨p, i⟩, initial⟩ := Option.isSome_iff_exists.mp (path_adjacent active)
        obtain ⟨final, walk, endVertex⟩ := (path_iff_walk initial).mp active
        have memRight : final.1 == y := by
          rw [List.getLast?_cons_cons, endVertex, Option.some.injEq] at last
          simpa using last
        exact ⟨x, p, (v, i), rest, final, by simp, decide_eq_true initial, walk, memRight, simple⟩
  · rintro ⟨source, outgoing, first, visited, final, memLeft, edge, walk, memRight, simple⟩
    rcases first with ⟨v, arrival⟩
    have sourceEq : source = x := beq_iff_eq.mp memLeft
    have finalEq : final.1 = y := beq_iff_eq.mp memRight
    subst source
    have initial : G.marks x v = some (outgoing, arrival) := of_decide_eq_true edge
    have endVertex := walk_last walk
    exact ⟨x :: v :: visited, simple, rfl, by simpa only [List.getLast?_cons_cons, finalEq] using endVertex,
      (path_iff_walk initial).mpr ⟨final, walk, endVertex⟩⟩

/-- Adding the head preserves the singly marked graph's separation relation
when the endpoints have matching external parents and spouses. -/
theorem same_separations_of_matching {H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (edit : AddedHead G H a b) (matching : MatchingParentsSpouses G a b) :
    G.SameSeparations H := by
  intro x y C legal
  obtain ⟨distinct, xOutside, _⟩ := legal
  have outside (v : Fin n) (left : (v == x) = true) : conditioned C v = false :=
    (beq_iff_eq.mp left).symm ▸ xOutside
  have disjoint (v : Fin n) (left : (v == x) = true) : (v == y) = false := by
    have same : v = x := beq_iff_eq.mp left
    simpa [same] using distinct
  have paths := path_connected_iff_of_matching noLines edit matching (· == x) (· == y)
    (conditioned C) outside disjoint
  exact not_congr ((marked_connected_iff_mixed_path (noLines := noLines) distinct).trans
    (paths.trans (marked_connected_iff_mixed_path (noLines := no_lines_after noLines edit) distinct).symm))

/-- Reversing through the common bidirected graph preserves the separation
relation under the same external parent and spouse conditions. -/
theorem same_separations_of_reversal {H K : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (noLines' : NoLines K)
    (forward : AddedHead G H a b) (backward : AddedHead K H b a)
    (matching : MatchingParentsSpouses G a b) : G.SameSeparations K := by
  intro x y C legal
  have matchedReverse := matching_of_reverse_edits forward backward matching
  exact (same_separations_of_matching noLines forward matching x y C legal).trans
    (same_separations_of_matching noLines' backward matchedReverse x y C legal).symm

end
end OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange
