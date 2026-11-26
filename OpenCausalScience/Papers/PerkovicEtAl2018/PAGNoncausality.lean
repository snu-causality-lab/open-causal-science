module
public import OpenCausalScience.Papers.PerkovicEtAl2018.PAGBlocking

/-! # Noncausality in the MAG-to-PAG direction

Perković et al. (2018), Lemma 50(i). An active noncausal path in a
representative and a proper path in the PAG cannot share their first
edge if the PAG path is possibly directed. This covers the original
path and the internal shortcuts considered in the lemma. The first
arrow consequence of amenability is stated as a premise.

Source: https://jmlr.org/papers/v18/16-319.html.
-/

namespace OpenCausalScience.Papers.PerkovicEtAl2018.PAGNoncausality

open OpenCausalScience.Papers.PerkovicEtAl2018.PAGBlocking
open OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge (PMG Mark)

@[expose] public section

variable {n : Nat}

def FollowsAdjacencies (pag : PMG n) : List (Fin n) → Prop
  | u :: v :: rest => pag.Adjacent u v ∧ FollowsAdjacencies pag (v :: rest)
  | _ => True

def PossiblyDirected (pag : PMG n) : List (Fin n) → Prop
  | u :: v :: rest => pag.PossibleForward u v ∧ PossiblyDirected pag (v :: rest)
  | _ => True

/-- All nodes after the start are outside the treatment set. -/
def ProperTo (treatment outcome : Fin n → Bool) (x : Fin n) (rest : List (Fin n)) : Prop :=
  treatment x = true ∧ (∀ v ∈ rest, treatment v = false) ∧
    (x :: rest).Nodup ∧ (x :: rest).getLast?.any outcome = true

def Forbidden (pag : PMG n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ x tail w, ProperTo treatment outcome x tail ∧ PossiblyDirected pag (x :: tail) ∧
    w ∈ tail ∧ MixedGraph.Reach pag.PossibleForward w v

def FirstArrowCondition (pag : PMG n) (treatment outcome : Fin n → Bool) : Prop :=
  ∀ x a rest, ProperTo treatment outcome x (a :: rest) →
    PossiblyDirected pag (x :: a :: rest) → pag.Directed x a

private theorem may_prepend {pag : PMG n} {a b c : Fin n} (edge : pag.PossibleForward a b)
    (path : MixedGraph.Reach pag.PossibleForward b c) : MixedGraph.Reach pag.PossibleForward a c := by
  induction path with
  | refl => exact .extend (.refl _) edge
  | extend _ step ih => exact .extend ih step

private theorem may_append {pag : PMG n} {a b c : Fin n}
    (first : MixedGraph.Reach pag.PossibleForward a b)
    (second : MixedGraph.Reach pag.PossibleForward b c) :
    MixedGraph.Reach pag.PossibleForward a c := by
  induction second with
  | refl => exact first
  | extend _ step ih => exact .extend ih step

private theorem possible_of_directed {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    {a b : Fin n} (edge : m.directed a b = true) : pag.PossibleForward a b := by
  have actual : m.marks a b = some (false, true) := by simpa [MarkedGraph.directed] using edge
  cases mark : pag.markAt a b with
  | none =>
    have adj := rep.adjacent member a b
    simp [MarkedGraph.adjacent, actual, mark] at adj
  | some endpoint =>
    cases endpoint with
    | tail => exact .inl mark
    | circle => exact .inr mark
    | arrow =>
      have head := rep.fixedArrow member mark
      simp [MarkedGraph.arrowheadAt, actual] at head

private theorem directed_of_fixed {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    {a b : Fin n} (edge : pag.Directed a b) : m.directed a b = true := by
  have tail := rep.fixedTail member edge.1
  have head := rep.fixedArrow member edge.2
  rw [MarkedGraph.arrowheadAt, m.swap_marks a b] at head
  cases edgeMarks : m.marks a b with
  | none => simp [edgeMarks] at head
  | some endpoints =>
    obtain ⟨left, right⟩ := endpoints
    simp [MarkedGraph.arrowheadAt, MarkedGraph.directed, edgeMarks, Prod.swap] at tail head ⊢
    exact ⟨tail, head⟩

private theorem from_directed_list {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m) :
    ∀ (a : Fin n) (rest : List (Fin n)) {b : Fin n},
      (a :: rest).getLast? = some b → m.followsArrows (a :: rest) = true →
      MixedGraph.Reach pag.PossibleForward a b
  | a, [], b, last, _ => by
    have eq : a = b := by simpa using last
    subst b
    exact .refl a
  | a, c :: rest, b, last, follows => by
    have edges := Bool.and_eq_true_iff.mp follows
    exact may_prepend (possible_of_directed rep member edges.1)
      (from_directed_list rep member c rest (by simpa using last) edges.2)

private theorem forbidden_at_possible_descendant {pag : PMG n}
    {treatment outcome : Fin n → Bool} {a b : Fin n}
    (forbidden : Forbidden pag treatment outcome a)
    (reaches : MixedGraph.Reach pag.PossibleForward a b) :
    Forbidden pag treatment outcome b := by
  obtain ⟨x, tail, w, proper, possible, occurs, toA⟩ := forbidden
  exact ⟨x, tail, w, proper, possible, occurs, may_append toA reaches⟩

private theorem forbidden_cannot_be_active {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    {treatment outcome : Fin n → Bool} (z : BitVec n)
    (avoids : ∀ v, Forbidden pag treatment outcome v → MarkedGraph.conditioned z v = false)
    {v : Fin n} (forbidden : Forbidden pag treatment outcome v) : m.activated z v = false := by
  cases active : m.activated z v with
  | false => rfl
  | true =>
    obtain ⟨path, _, start, endpoint, follows⟩ := (m.activated_iff z v).mp active
    cases path with
    | nil => simp at start
    | cons a rest =>
      have same : a = v := by simpa using start
      subst a
      cases last : (v :: rest).getLast? with
      | none => simp [last] at endpoint
      | some w =>
        have reaches := from_directed_list rep member v rest last follows
        have blocked := avoids w (forbidden_at_possible_descendant forbidden reaches)
        simp [last, blocked] at endpoint

private theorem outgoing_after_head {m : MarkedGraph n}
    (noTailTail : ∀ u v, m.marks u v ≠ some (false, false)) {a b c : Fin n}
    (first : m.directed a b = true) (second : m.adjacent b c = true)
    (noncollider : m.collider a b c = false) : m.directed b c = true := by
  have actual : m.marks a b = some (false, true) := by simpa [MarkedGraph.directed] using first
  have arrival : m.arrowheadAt b a = true := by
    simp [MarkedGraph.arrowheadAt, m.swap_marks a b, actual, Prod.swap]
  have tail : m.arrowheadAt b c = false := by
    simpa [MarkedGraph.collider, arrival] using noncollider
  cases marks : m.marks b c with
  | none => simp [MarkedGraph.adjacent, marks] at second
  | some endpoints =>
    obtain ⟨u, v⟩ := endpoints
    have uTail : u = false := by simpa [MarkedGraph.arrowheadAt, marks] using tail
    subst u
    cases v with
    | false => exact (noTailTail _ _ marks).elim
    | true => simp [MarkedGraph.directed, marks]

private theorem directed_after_forbidden_first {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    (noTailTail : ∀ u v, m.marks u v ≠ some (false, false))
    (treatment outcome : Fin n → Bool) (z : BitVec n)
    (avoids : ∀ v, Forbidden pag treatment outcome v → MarkedGraph.conditioned z v = false) :
    ∀ (a b : Fin n) (rest : List (Fin n)),
      m.directed a b = true → Forbidden pag treatment outcome b →
      m.activePath z (a :: b :: rest) = true → m.followsArrows (a :: b :: rest) = true
  | a, b, [], first, _, _ => by simp [MarkedGraph.followsArrows, first]
  | a, b, c :: rest, first, forbidden, active => by
    have colliderFalse : m.collider a b c = false := by
      cases collider : m.collider a b c with
      | false => rfl
      | true =>
        have inactive := forbidden_cannot_be_active rep member z avoids forbidden
        simp [MarkedGraph.activePath, collider, inactive] at active
    have suffix : m.activePath z (b :: c :: rest) = true := by
      simp only [MarkedGraph.activePath, Bool.and_eq_true] at active
      exact active.2
    have adjacent : m.adjacent b c = true := by
      cases rest with
      | nil => exact suffix
      | cons d rest =>
        simp only [MarkedGraph.activePath, Bool.and_eq_true] at suffix
        exact suffix.1.1
    have next := outgoing_after_head noTailTail first adjacent colliderFalse
    have nextForbidden := forbidden_at_possible_descendant forbidden
      (.extend (.refl _) (possible_of_directed rep member next))
    have directions := directed_after_forbidden_first rep member noTailTail treatment outcome z avoids
      b c rest next nextForbidden suffix
    exact Bool.and_eq_true_iff.mpr ⟨first, directions⟩

private theorem may_follow_or_backward (pag : PMG n) :
    ∀ vertices, FollowsAdjacencies pag vertices →
      PossiblyDirected pag vertices ∨ HasBackwardArrow pag vertices
  | a :: b :: rest, path => by
    obtain ⟨adjacent, suffix⟩ := path
    cases mark : pag.markAt a b with
    | none => simp [PMG.Adjacent, mark] at adjacent
    | some endpoint =>
      have continuePath (first : pag.PossibleForward a b) :
          PossiblyDirected pag (a :: b :: rest) ∨ HasBackwardArrow pag (a :: b :: rest) :=
        (may_follow_or_backward pag (b :: rest) suffix).elim
          (fun tail => .inl ⟨first, tail⟩) (fun head => .inr (.inr head))
      cases endpoint with
      | tail => exact continuePath (.inl mark)
      | circle => exact continuePath (.inr mark)
      | arrow => exact .inr (.inl mark)
  | [], _ => .inl trivial
  | [_], _ => .inl trivial

/-- The noncausality conclusion of Lemma 50(i). The proper PAG path can
be the unchanged representative path or an internal shortcut, since
only its first edge must agree with the active representative path. -/
theorem noncausal_same_first_edge {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    (noTailTail : ∀ u v, m.marks u v ≠ some (false, false))
    (treatment outcome : Fin n → Bool) (z : BitVec n)
    (firstArrow : FirstArrowCondition pag treatment outcome)
    (avoids : ∀ v, Forbidden pag treatment outcome v → MarkedGraph.conditioned z v = false)
    {x first : Fin n} {original replacement : List (Fin n)}
    (active : m.activePath z (x :: first :: original) = true)
    (noncausal : m.followsArrows (x :: first :: original) = false)
    (proper : ProperTo treatment outcome x (first :: replacement))
    (path : FollowsAdjacencies pag (x :: first :: replacement)) :
    HasBackwardArrow pag (x :: first :: replacement) := by
  rcases may_follow_or_backward pag _ path with possible | backward
  · have firstForbidden : Forbidden pag treatment outcome first :=
      ⟨x, first :: replacement, first, proper, possible, List.mem_cons_self, .refl _⟩
    have directed := directed_of_fixed rep member (firstArrow _ _ _ proper possible)
    have follows := directed_after_forbidden_first rep member noTailTail treatment outcome z avoids
      _ _ _ directed firstForbidden active
    simp [noncausal] at follows
  · exact backward

private theorem representative_active_walk_is_pag_path {pag : PMG n}
    {members : MarkedGraph n → Prop} (rep : Represents pag members)
    {m : MarkedGraph n} (member : members m) (z : BitVec n) :
    ∀ vertices, m.activePath z vertices = true → FollowsAdjacencies pag vertices
  | a :: b :: c :: rest, active => by
    simp only [MarkedGraph.activePath, Bool.and_eq_true] at active
    exact ⟨(rep.adjacent member a b).symm.trans active.1.1,
      representative_active_walk_is_pag_path rep member z (b :: c :: rest) active.2⟩
  | [a, b], active => ⟨(rep.adjacent member a b).symm.trans active, trivial⟩
  | [], _ | [_], _ => trivial

/-- Any open proper noncausal path in a representative has a backward
arrow on its image in the PAG under the first-arrow and forbidden-set
conditions. Definite status and activation in the PAG are separate. -/
theorem noncausal_path_in_pag {pag : PMG n} {members : MarkedGraph n → Prop}
    (rep : Represents pag members) {m : MarkedGraph n} (member : members m)
    (noTailTail : ∀ u v, m.marks u v ≠ some (false, false))
    (treatment outcome : Fin n → Bool) (z : BitVec n)
    (firstArrow : FirstArrowCondition pag treatment outcome)
    (avoids : ∀ v, Forbidden pag treatment outcome v → MarkedGraph.conditioned z v = false)
    {x first : Fin n} {rest : List (Fin n)}
    (active : m.activePath z (x :: first :: rest) = true)
    (noncausal : m.followsArrows (x :: first :: rest) = false)
    (proper : ProperTo treatment outcome x (first :: rest)) :
    HasBackwardArrow pag (x :: first :: rest) :=
  noncausal_same_first_edge rep member noTailTail treatment outcome z firstArrow avoids
    active noncausal proper (representative_active_walk_is_pag_path rep member z _ active)

/-- R1 closure forces any ambiguous triple to be shielded. In particular
the first ambiguous interior vertex of Lemma 50(ii) can be skipped by
an adjacency; noncausality of that first-edge-changing shortcut is a
separate assertion of the lemma. -/
theorem unshielded_triple_definite_of_r1 {pag : PMG n}
    (r1 : ∀ {a b c}, pag.ArrowInto a b → pag.markAt b c = some .circle →
      ¬ pag.Adjacent a c → pag.Directed b c)
    {a b c : Fin n} (ab : pag.Adjacent b a) (bc : pag.Adjacent b c)
    (ac : pag.markAt a c = none) (distinctAB : a ≠ b) (distinctAC : a ≠ c) (distinctBC : b ≠ c) :
    (pag.ArrowInto a b ∧ pag.ArrowInto c b) ∨ DefiniteNoncollider pag a b c := by
  have ca : pag.markAt c a = none := by
    have same := pag.same_adjacencies a c
    cases h : pag.markAt c a <;> simp_all
  cases left : pag.markAt b a with
  | none => simp [PMG.Adjacent, left] at ab
  | some leftMark =>
    cases right : pag.markAt b c with
    | none => simp [PMG.Adjacent, right] at bc
    | some rightMark =>
      cases leftMark with
      | tail => exact .inr (.inl left)
      | arrow =>
        cases rightMark with
        | tail => exact .inr (.inr (.inl right))
        | arrow => exact .inl ⟨left, right⟩
        | circle =>
          have tail := (r1 left right (by simp [PMG.Adjacent, ac])).1
          simp [right] at tail
      | circle =>
        cases rightMark with
        | tail => exact .inr (.inr (.inl right))
        | arrow =>
          have tail := (r1 right left (by simp [PMG.Adjacent, ca])).1
          simp [left] at tail
        | circle => exact .inr (.inr (.inr ⟨left, right, ac, distinctAB, distinctAC, distinctBC⟩))

end

end OpenCausalScience.Papers.PerkovicEtAl2018.PAGNoncausality
