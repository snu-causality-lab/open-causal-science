module
public import OpenCausalScience.Papers.AliRichardsonSpirtes2009.EquivalenceNecessary
public import OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge

/-! # Definite-status paths in MAG representatives

Perković et al. (2018), Lemma 10, the direction that transfers a witness of
non-blocking from the PAG to each MAG representative. The family of
representatives supplies completeness of circle marks through the existence
of a member with a tail at each circle endpoint. Maximality and shared
m-separations give invariance of unshielded colliders (Ali et al., 2009).

Source: https://jmlr.org/papers/v18/16-319.html.
-/

namespace OpenCausalScience.Papers.PerkovicEtAl2018.PAGBlocking

open OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge (PMG)

@[expose] public section

variable {n : Nat}

structure Represents (pag : PMG n) (members : MarkedGraph n → Prop) : Prop where
  adjacent : ∀ {m}, members m → ∀ u v, m.adjacent u v = (pag.markAt u v).isSome
  fixedTail : ∀ {m}, members m → ∀ {u v}, pag.markAt u v = some .tail → m.arrowheadAt u v = false
  fixedArrow : ∀ {m}, members m → ∀ {u v}, pag.markAt u v = some .arrow → m.arrowheadAt u v = true
  variableMark : ∀ {u v}, pag.markAt u v = some .circle →
    ∃ m, members m ∧ m.arrowheadAt u v = false
  maximal : ∀ {m}, members m → m.HasSeparators
  equivalent : ∀ {m other}, members m → members other → m.SameSeparations other

def DefiniteNoncollider (pag : PMG n) (u v w : Fin n) : Prop :=
  pag.markAt v u = some .tail ∨ pag.markAt v w = some .tail ∨
    (pag.markAt v u = some .circle ∧ pag.markAt v w = some .circle ∧ pag.markAt u w = none ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w)

theorem definite_noncollider_in_representative {pag : PMG n} {members : MarkedGraph n → Prop}
    (represents : Represents pag members) {m : MarkedGraph n} (member : members m)
    {u v w : Fin n} (definite : DefiniteNoncollider pag u v w) : m.collider u v w = false := by
  rcases definite with tail | tail | ⟨left, right, absent, uv, uw, vw⟩
  · simp [MarkedGraph.collider, represents.fixedTail member tail]
  · simp [MarkedGraph.collider, represents.fixedTail member tail]
  · obtain ⟨other, otherMember, leftTail⟩ := represents.variableMark left
    cases coll : m.collider u v w with
    | false => rfl
    | true =>
      have leftEdge : m.adjacent u v = true := by
        rw [represents.adjacent member, pag.same_adjacencies u v, left]
        rfl
      have rightEdge : m.adjacent v w = true := by simp [represents.adjacent member, right]
      have unshielded : m.adjacent u w = false := by simp [represents.adjacent member, absent]
      have triple : m.UnshieldedCollider u v w := ⟨uv, uw, vw, leftEdge, rightEdge, unshielded, coll⟩
      have otherTriple := (AliRichardsonSpirtes2009.equivalent_unshielded_colliders
        (represents.maximal member) (represents.maximal otherMember)
        (represents.equivalent member otherMember) u v w).mp triple
      obtain ⟨_, _, _, _, _, _, otherCollider⟩ := otherTriple
      simp [MarkedGraph.collider, leftTail] at otherCollider

def FollowsDirected (pag : PMG n) : List (Fin n) → Prop
  | u :: v :: rest => pag.Directed u v ∧ FollowsDirected pag (v :: rest)
  | _ => True

private theorem follows_directed_in_representative {pag : PMG n} {members : MarkedGraph n → Prop}
    (represents : Represents pag members) {m : MarkedGraph n} (member : members m) :
    ∀ vertices, FollowsDirected pag vertices → m.followsArrows vertices = true
  | u :: v :: rest, path => by
    obtain ⟨⟨tail, head⟩, suffix⟩ := path
    have left := represents.fixedTail member tail
    have right := represents.fixedArrow member head
    have edge : m.directed u v = true := by
      rw [MarkedGraph.arrowheadAt, m.swap_marks u v] at right
      cases edgeMarks : m.marks u v with
      | none => simp [edgeMarks] at right
      | some endpoints =>
        obtain ⟨a, b⟩ := endpoints
        simp [MarkedGraph.arrowheadAt, MarkedGraph.directed, edgeMarks, Prod.swap] at left right ⊢
        exact ⟨left, right⟩
    simp [MarkedGraph.followsArrows, edge,
      follows_directed_in_representative represents member (v :: rest) suffix]
  | [], _ => rfl
  | [_], _ => rfl

def ActivatedInPAG (pag : PMG n) (conditioning : BitVec n) (v : Fin n) : Prop :=
  ∃ p : List (Fin n), p.Nodup ∧ p.head? = some v ∧
    p.getLast?.any (MarkedGraph.conditioned conditioning) = true ∧ FollowsDirected pag p

def DefiniteOpenPath (pag : PMG n) (conditioning : BitVec n) : List (Fin n) → Prop
  | u :: v :: w :: rest => pag.Adjacent u v ∧
    ((pag.ArrowInto u v ∧ pag.ArrowInto w v ∧ ActivatedInPAG pag conditioning v) ∨
      (DefiniteNoncollider pag u v w ∧ MarkedGraph.conditioned conditioning v = false)) ∧
    DefiniteOpenPath pag conditioning (v :: w :: rest)
  | [u, v] => pag.Adjacent u v
  | _ => True

private theorem definite_open_in_representative {pag : PMG n} {members : MarkedGraph n → Prop}
    (represents : Represents pag members) {m : MarkedGraph n} (member : members m)
    (conditioning : BitVec n) :
    ∀ vertices, DefiniteOpenPath pag conditioning vertices → m.activePath conditioning vertices = true
  | u :: v :: w :: rest, path => by
    obtain ⟨edge, turn, suffix⟩ := path
    have firstEdge : m.adjacent u v = true := (represents.adjacent member u v).trans edge
    have restOpen := definite_open_in_representative represents member conditioning (v :: w :: rest) suffix
    rcases turn with ⟨left, right, activated⟩ | ⟨noncollider, outside⟩
    · obtain ⟨p, simple, starts, ends, directed⟩ := activated
      have active : m.activated conditioning v = true := (m.activated_iff _ _).mpr
        ⟨p, simple, starts, ends, follows_directed_in_representative represents member p directed⟩
      simp [MarkedGraph.activePath, MarkedGraph.collider, firstEdge,
        represents.fixedArrow member left, represents.fixedArrow member right, active, restOpen]
    · have coll := definite_noncollider_in_representative represents member noncollider
      simp [MarkedGraph.activePath, firstEdge, coll, outside, restOpen]
  | [u, v], path => (represents.adjacent member u v).trans path
  | [], _ => rfl
  | [_], _ => rfl

/-- A backward arrowhead makes the PAG path noncausal. -/
def HasBackwardArrow (pag : PMG n) : List (Fin n) → Prop
  | u :: v :: rest => pag.ArrowInto v u ∨ HasBackwardArrow pag (v :: rest)
  | _ => False

private theorem noncausal_in_representative {pag : PMG n} {members : MarkedGraph n → Prop}
    (represents : Represents pag members) {m : MarkedGraph n} (member : members m) :
    ∀ vertices, HasBackwardArrow pag vertices → m.followsArrows vertices = false
  | u :: v :: rest, path => by
    rcases path with backward | suffix
    · have arrow := represents.fixedArrow member backward
      have directed : m.directed u v = false := by
        cases h : m.directed u v with
        | false => rfl
        | true =>
          have marks : m.marks u v = some (false, true) := by simpa [MarkedGraph.directed] using h
          simp [MarkedGraph.arrowheadAt, marks] at arrow
      simp [MarkedGraph.followsArrows, directed]
    · simp [MarkedGraph.followsArrows, noncausal_in_representative represents member (v :: rest) suffix]
  | [], h => h.elim
  | [_], h => h.elim

/-- A proper noncausal definite-status active path in the PAG stays active
and noncausal in every MAG representative. It uses the same vertex list,
so any treatment-set properness property of that list is preserved. -/
theorem noncausal_path_in_representative {pag : PMG n} {members : MarkedGraph n → Prop}
    (represents : Represents pag members) {m : MarkedGraph n} (member : members m)
    {vertices : List (Fin n)} (conditioning : BitVec n)
    (openPath : DefiniteOpenPath pag conditioning vertices) (noncausal : HasBackwardArrow pag vertices) :
    m.activePath conditioning vertices = true ∧ m.followsArrows vertices = false :=
  ⟨definite_open_in_representative represents member conditioning vertices openPath,
    noncausal_in_representative represents member vertices noncausal⟩

end

end OpenCausalScience.Papers.PerkovicEtAl2018.PAGBlocking
