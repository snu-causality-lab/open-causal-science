module
public import OpenCausalScience.Graph.MixedGraph

/-! # Arrowheads and paths in partially marked graphs

Wang, Qin and Zhou, *Sound and complete causal identification with latent
variables given local background knowledge*, Artificial Intelligence 322
(2023), 103964, Theorem 1 and Appendix B, Lemmas 2–3.

Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge

open MixedGraph (Reach)

@[expose] public section

inductive Mark where
  | tail
  | arrow
  | circle
  deriving DecidableEq

/-- One endpoint mark in each direction for every adjacency. -/
structure PMG (n : Nat) where
  markAt : Fin n → Fin n → Option Mark
  loop_free : ∀ v, markAt v v = none
  same_adjacencies : ∀ u v, (markAt u v).isSome = (markAt v u).isSome

namespace PMG

variable {n : Nat}

/-- An edge from `u` with an arrowhead at `v`. -/
def ArrowInto (G : PMG n) (u v : Fin n) : Prop :=
  G.markAt v u = some .arrow

def CircleEdge (G : PMG n) (u v : Fin n) : Prop :=
  G.markAt u v = some .circle ∧ G.markAt v u = some .circle

/-- The first clause of Balanced in Theorem 1, on distinct vertices:
`A *→ B o-* C` implies `A *→ C`. -/
def BalancedArrowheads (G : PMG n) : Prop :=
  ∀ {a b c}, a ≠ b → b ≠ c → a ≠ c →
    G.ArrowInto a b → G.markAt b c = some .circle → G.ArrowInto a c

/-- Lemma 3, first assertion: an arrowhead into one vertex of a circle
component forces an arrowhead into every vertex of that component. -/
theorem arrowhead_into_circle_component {G : PMG n} (balanced : G.BalancedArrowheads)
    {a b c : Fin n} (arrow : G.ArrowInto a b) (component : Reach G.CircleEdge b c) :
    G.ArrowInto a c := by
  induction component with
  | refl => exact arrow
  | @extend b' c' _ step ih =>
    have notLoop : a ≠ b' := by
      intro eq
      subst b'
      simp [ArrowInto, G.loop_free] at ih
    have notRepeated : b' ≠ c' := by
      intro eq
      subst c'
      have circ := step.1
      simp [G.loop_free] at circ
    have notSource : a ≠ c' := by
      intro eq
      subst c'
      have mark := step.1
      simp [ArrowInto, mark] at ih
    exact balanced notLoop notRepeated notSource ih step.1

/-- Lemma 3, second assertion: the source is outside that circle component. -/
theorem source_outside_circle_component {G : PMG n} (balanced : G.BalancedArrowheads)
    {a b : Fin n} (arrow : G.ArrowInto a b) :
    ¬ Reach G.CircleEdge b a := by
  intro component
  have ends := arrowhead_into_circle_component balanced arrow component
  simp [ArrowInto, G.loop_free] at ends

def Adjacent (G : PMG n) (u v : Fin n) : Prop := (G.markAt u v).isSome = true

def Directed (G : PMG n) (u v : Fin n) : Prop :=
  G.markAt u v = some .tail ∧ G.ArrowInto u v

def PossibleForward (G : PMG n) (u v : Fin n) : Prop :=
  G.markAt u v = some .tail ∨ G.markAt u v = some .circle

/-- The properties used to rule out an arrowhead at the beginning of an
isolated chord. The tail condition is the no-selection endpoint constraint
after R11 closure. The last field is necessary whenever a compatible
ancestral graph exists. -/
structure PossiblePathConditions (G : PMG n) : Prop where
  balanced : G.BalancedArrowheads
  tail_into_head : ∀ {a b}, G.markAt a b = some .tail → G.ArrowInto a b
  r1_closed : ∀ {a b c}, G.ArrowInto a b → G.markAt b c = some .circle →
    ¬ G.Adjacent a c → G.Directed b c
  r2_closed : ∀ {a b c}, G.ArrowInto a b → G.Directed b c →
    G.markAt c a = some .circle → G.ArrowInto a c
  no_arrowhead_into_ancestor : ∀ {a b}, Reach G.Directed a b → G.ArrowInto b a → False

/-- The directed edges and definite arrowheads of the PMG survive in a
compatible MAG. These are the only parts of agreement needed here. -/
structure AgreesWith (G : PMG n) (M : MixedGraph n) : Prop where
  directed : ∀ {a b}, G.Directed a b → M.edge a false b true = true
  arrowhead : ∀ {a b}, G.ArrowInto a b → ∃ mark, M.edge a mark b true = true

/-- One agreeing ancestral graph suffices to rule out a fixed arrowhead
at the start of any definite directed path between its endpoints. -/
theorem no_arrowhead_into_ancestor_of_agreeing_graph {G : PMG n} {M : MixedGraph n}
    (agree : G.AgreesWith M)
    (ancestral : ∀ {a b mark}, Reach (fun u v => M.edge u false v true = true) a b →
      M.edge b mark a true = true → False)
    {a b : Fin n} (path : Reach G.Directed a b) : G.ArrowInto b a → False := by
  have directedPath : Reach (fun u v => M.edge u false v true = true) a b := by
    induction path with
    | refl => exact .refl _
    | extend _ step ih => exact .extend ih (agree.directed step)
  intro head
  obtain ⟨_, mark⟩ := agree.arrowhead head
  exact ancestral directedPath mark

/-- A simple, possibly directed path with `length` edges. The index
function is inspected only at positions at most `length`. -/
structure PossiblePath (G : PMG n) (vertices : Nat → Fin n) (length : Nat) : Prop where
  step : ∀ i, i < length → G.PossibleForward (vertices i) (vertices (i + 1))
  simple : ∀ {i j}, i ≤ length → j ≤ length → vertices i = vertices j → i = j

def Uncovered (G : PMG n) (vertices : Nat → Fin n) (length : Nat) : Prop :=
  ∀ i j, i + 1 < j → j ≤ length → ¬ G.Adjacent (vertices i) (vertices j)

private theorem forward_without_head {G : PMG n} {u v : Fin n}
    (adjacent : G.Adjacent u v) (noHead : ¬ G.ArrowInto v u) : G.PossibleForward u v := by
  obtain ⟨mark, marked⟩ := Option.isSome_iff_exists.mp adjacent
  cases mark with
  | tail => exact Or.inl marked
  | circle => exact Or.inr marked
  | arrow => exact (noHead marked).elim

private theorem forward_precludes_head {G : PMG n} {u v : Fin n}
    (forward : G.PossibleForward u v) : ¬ G.ArrowInto v u := by
  intro head
  rcases forward with tail | circle
  · simp [ArrowInto, tail] at head
  · simp [ArrowInto, circle] at head

private theorem directed_from_unshielded {G : PMG n} (conditions : G.PossiblePathConditions)
    {a b c : Fin n} (head : G.ArrowInto a b) (forward : G.PossibleForward b c)
    (unshielded : ¬ G.Adjacent a c) : G.Directed b c := by
  rcases forward with tail | circle
  · exact ⟨tail, conditions.tail_into_head tail⟩
  · exact conditions.r1_closed head circle unshielded

/-- The shortcut used in the proof of Lemma 2. Choose a chord whose
spanned segment has no shorter chord. Its initial mark cannot be an
arrowhead. -/
theorem isolated_chord_points_possibly_forward {G : PMG n}
    (conditions : G.PossiblePathConditions) {vertices : Nat → Fin n} {length i j : Nat}
    (path : G.PossiblePath vertices length) (gap : i + 1 < j) (bound : j ≤ length)
    (chord : G.Adjacent (vertices i) (vertices j))
    (noShorter : ∀ k l, k + 1 < l → l ≤ length → l - k < j - i →
      ¬ G.Adjacent (vertices k) (vertices l)) :
    G.PossibleForward (vertices i) (vertices j) := by
  apply forward_without_head chord
  intro back
  by_cases triangle : j = i + 2
  · subst j
    have first := path.step i (by omega)
    have second := path.step (i + 1) (by omega)
    apply forward_precludes_head second
    rcases first with firstTail | firstCircle
    · have firstDir : G.Directed (vertices i) (vertices (i + 1)) :=
        ⟨firstTail, conditions.tail_into_head firstTail⟩
      rcases second with secondTail | secondCircle
      · have secondDir : G.Directed (vertices (i + 1)) (vertices (i + 2)) :=
          ⟨secondTail, conditions.tail_into_head secondTail⟩
        exact (conditions.no_arrowhead_into_ancestor
          (.extend (.extend (.refl _) firstDir) secondDir) back).elim
      · exact conditions.r2_closed back firstDir secondCircle
    · have distinct : ∀ {k l}, k ≤ length → l ≤ length → k ≠ l → vertices k ≠ vertices l :=
        fun hk hl ne eq => ne (path.simple hk hl eq)
      exact conditions.balanced
        (distinct bound (by omega) (by omega))
        (distinct (by omega) (by omega) (by omega))
        (distinct bound (by omega) (by omega)) back firstCircle
  · have firstUnshielded : ¬ G.Adjacent (vertices j) (vertices (i + 1)) := by
      intro reverse
      apply noShorter (i + 1) j (by omega) bound (by omega)
      unfold Adjacent at reverse ⊢
      rw [G.same_adjacencies]
      exact reverse
    have step : ∀ k, i + k < j → G.Directed (vertices (i + k)) (vertices (i + k + 1)) := by
      intro k
      induction k with
      | zero =>
        intro _
        simpa using directed_from_unshielded conditions back
          (path.step i (by omega)) firstUnshielded
      | succ k ih =>
        intro before
        have previous := ih (by omega)
        have unshielded := noShorter (i + k) (i + k + 2) (by omega) (by omega) (by omega)
        have edge := directed_from_unshielded conditions previous.2
          (path.step (i + k + 1) (by omega)) unshielded
        exact edge
    have reach : ∀ k, i + k ≤ j → Reach G.Directed (vertices i) (vertices (i + k)) := by
      intro k
      induction k with
      | zero => intro _; exact .refl _
      | succ k ih =>
        intro bound
        exact .extend (ih (by omega)) (step k (by omega))
    have endIndex : i + (j - i) = j := by omega
    have reaches := reach (j - i) (by omega)
    rw [endIndex] at reaches
    exact conditions.no_arrowhead_into_ancestor reaches back

private theorem least_witness {P : Nat → Prop} {m : Nat} (atM : P m) :
    ∃ k, P k ∧ ∀ t, t < k → ¬ P t := by
  classical
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases smaller : ∃ t, t < m ∧ P t
    · obtain ⟨t, lt, proof⟩ := smaller
      exact ih t lt proof
    · exact ⟨m, atM, fun t lt proof => smaller ⟨t, lt, proof⟩⟩

private def shortcutIndex (i skipped k : Nat) : Nat :=
  if k ≤ i then k else k + skipped

private theorem shortcut_injective {i skipped x y : Nat}
    (same : shortcutIndex i skipped x = shortcutIndex i skipped y) : x = y := by
  by_cases left : x ≤ i <;> by_cases right : y ≤ i <;>
    simp [shortcutIndex, left, right] at same <;> omega

/-- Lemma 2. Remove the interior of a shortest chord, then repeat on the
shorter path. The resulting path has no chord, the same endpoints, and
only vertices of the original path. -/
theorem exists_uncovered_possible_path {G : PMG n} (conditions : G.PossiblePathConditions)
    {vertices : Nat → Fin n} {length : Nat} (path : G.PossiblePath vertices length) :
    ∃ (reduced : Nat → Fin n) (count : Nat),
      G.PossiblePath reduced count ∧ G.Uncovered reduced count ∧
      reduced 0 = vertices 0 ∧ reduced count = vertices length ∧
      ∀ k, k ≤ count → ∃ pos, pos ≤ length ∧ reduced k = vertices pos := by
  classical
  induction length using Nat.strongRecOn generalizing vertices with
  | ind length ih =>
    by_cases uncovered : G.Uncovered vertices length
    · exact ⟨vertices, length, path, uncovered, rfl, rfl, fun k bound => ⟨k, bound, rfl⟩⟩
    have hasChord : ∃ i j, i + 1 < j ∧ j ≤ length ∧ G.Adjacent (vertices i) (vertices j) := by
      apply Classical.byContradiction
      intro absent
      exact uncovered (fun i j gap bound adj => absent ⟨i, j, gap, bound, adj⟩)
    obtain ⟨p, q, gap0, bound0, adjacent0⟩ := hasChord
    let ChordSpan := fun span =>
      ∃ i j, i + 1 < j ∧ j ≤ length ∧ G.Adjacent (vertices i) (vertices j) ∧ j - i = span
    obtain ⟨span, ⟨i, j, gap, bound, adjacent, spanEq⟩, minimal⟩ :=
      least_witness (P := ChordSpan) (m := q - p) ⟨p, q, gap0, bound0, adjacent0, rfl⟩
    have noShorter : ∀ k l, k + 1 < l → l ≤ length → l - k < j - i →
        ¬ G.Adjacent (vertices k) (vertices l) := by
      intro k l distance within less adj
      exact minimal (l - k) (by omega) ⟨k, l, distance, within, adj, rfl⟩
    have chord := isolated_chord_points_possibly_forward conditions path gap bound adjacent noShorter
    let skipped := j - i - 1
    let shorter := length - skipped
    have shorterLt : shorter < length := by dsimp [shorter, skipped]; omega
    have afterCut : ¬ shorter ≤ i := by dsimp [shorter, skipped]; omega
    let newVertices := fun k => vertices (shortcutIndex i skipped k)
    have indexBound : ∀ k, k ≤ shorter → shortcutIndex i skipped k ≤ length := by
      intro k within
      by_cases first : k ≤ i
      · simpa [shortcutIndex, first] using (show k ≤ length by omega)
      · simp [shortcutIndex, first]
        dsimp [shorter, skipped] at within ⊢
        omega
    have newPath : G.PossiblePath newVertices shorter := by
      constructor
      · intro k inside
        change G.PossibleForward (vertices (shortcutIndex i skipped k))
          (vertices (shortcutIndex i skipped (k + 1)))
        by_cases cut : k = i
        · subst k
          have past : ¬ i + 1 ≤ i := by omega
          have skips : i + 1 + skipped = j := by dsimp [skipped]; omega
          simpa [shortcutIndex, past, skips] using chord
        by_cases before : k < i
        · have beforeNext : k + 1 ≤ i := by omega
          simpa [shortcutIndex, beforeNext, Nat.le_of_lt before] using
            (path.step k (by omega))
        · have after : ¬ k ≤ i := by omega
          have afterNext : ¬ k + 1 ≤ i := by omega
          have next : shortcutIndex i skipped (k + 1) = shortcutIndex i skipped k + 1 := by
            simp [shortcutIndex, after, afterNext]
            omega
          rw [next]
          exact path.step _ (by have := indexBound (k + 1) (by omega); omega)
      · intro a b ha hb same
        exact shortcut_injective (path.simple (indexBound a ha) (indexBound b hb) same)
    have startSame : newVertices 0 = vertices 0 := by simp [newVertices, shortcutIndex]
    have endpointSame : newVertices shorter = vertices length := by
      have last : shorter + skipped = length := by dsimp [shorter, skipped]; omega
      simp [newVertices, shortcutIndex, afterCut, last]
    obtain ⟨reduced, count, reducedPath, uncoveredPath, first, last, within⟩ :=
      ih shorter shorterLt newPath
    refine ⟨reduced, count, reducedPath, uncoveredPath, first.trans startSame,
      last.trans endpointSame, ?_⟩
    intro k hk
    obtain ⟨pos, hp, eq⟩ := within k hk
    exact ⟨shortcutIndex i skipped pos, indexBound pos hp, eq⟩
end PMG
end
end OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge
