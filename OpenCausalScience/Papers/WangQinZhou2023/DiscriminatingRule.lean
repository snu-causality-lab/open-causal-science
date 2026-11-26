module
public import OpenCausalScience.Papers.WangQinZhou2023.LocalBackgroundKnowledge
public import OpenCausalScience.Papers.Zhang2008OrientationRules.DiscriminatingPaths

/-! # The modified discriminating-path rule

Wang, Qin and Zhou (2023), Proposition 1. A collider path formed by
violating R′4 has a minimal collider subsequence. Its last interior
vertex must be the discriminated vertex, because every earlier
interior vertex is a parent of the endpoint.

Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.DiscriminatingRule

open LocalBackgroundKnowledge (PMG)
open Zhang2008OrientationRules.Orientations (AncestralMarks Directed r2_sound)
open Zhang2008OrientationRules.DiscriminatingPaths (DiscriminatingPrefix)
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

inductive ColliderChain (G : MarkedGraph n) : List (Fin n) → Fin n → Fin n → Prop where
  | edge {u v} : G.adjacent u v = true → ColliderChain G [] u v
  | extend {earlier : List (Fin n)} {u v w} :
      ColliderChain G earlier u v → G.collider u v w = true → G.adjacent v w = true →
      ColliderChain G (earlier ++ [u]) v w

def ColliderPath (G : MarkedGraph n) (source target : Fin n) (path : List (Fin n)) : Prop :=
  ∃ earlier previous, path = earlier ++ [previous, target] ∧ path.head? = some source ∧
    path.Nodup ∧ ColliderChain G earlier previous target

def MinimalColliderPath (G : MarkedGraph n) (source target : Fin n) (path : List (Fin n)) : Prop :=
  ColliderPath G source target path ∧
    ∀ q, q.Sublist path → q.length < path.length → ¬ ColliderPath G source target q

/-- Every collider path has a minimal collider subsequence with the
same endpoints. -/
theorem exists_minimal_collider_subpath {G : MarkedGraph n} {s t : Fin n} {p : List (Fin n)}
    (path : ColliderPath G s t p) : ∃ q, q.Sublist p ∧ MinimalColliderPath G s t q := by
  classical
  induction size : p.length using Nat.strongRecOn generalizing p with
  | ind length ih =>
    by_cases shorter : ∃ q, q.Sublist p ∧ q.length < p.length ∧ ColliderPath G s t q
    · obtain ⟨q, sublist, small, candidate⟩ := shorter
      obtain ⟨result, sub, minimal⟩ := ih q.length (size ▸ small) candidate rfl
      exact ⟨result, sub.trans sublist, minimal⟩
    · exact ⟨p, List.Sublist.refl _, path, fun q sub small other => shorter ⟨q, sub, small, other⟩⟩

/-- The result used from minimal-collider-path invariance and initial
PAG completeness. Every interior endpoint mark of a minimal collider
path is a definite arrowhead in the initial PAG. -/
def DisplaysMinimalColliders (P : PMG n) (G : MarkedGraph n) : Prop :=
  ∀ {s t path}, MinimalColliderPath G s t path →
    ∀ {earlier later : List (Fin n)} {u v w}, path = earlier ++ u :: v :: w :: later →
      P.markAt v u = some .arrow ∧ P.markAt v w = some .arrow

private theorem DiscriminatingPrefix.is_collider_chain {G : MarkedGraph n}
    {s t u v : Fin n} {earlier : List (Fin n)} (path : DiscriminatingPrefix G s t earlier u v) :
    ColliderChain G earlier u v := by
  induction path with
  | initial edge => exact .edge edge
  | extend _ col _ adjacent ih => exact .extend ih col adjacent

private theorem DiscriminatingPrefix.head_eq {G : MarkedGraph n} {s t u v : Fin n}
    {earlier tail : List (Fin n)} (path : DiscriminatingPrefix G s t earlier u v) :
    (earlier ++ u :: v :: tail).head? = some s := by
  induction path with
  | initial => rfl
  | extend _ _ _ _ ih => simpa [List.append_assoc] using ih

private theorem DiscriminatingPrefix.parent_until_last {G : MarkedGraph n} {s t u v : Fin n}
    {earlier : List (Fin n)} (path : DiscriminatingPrefix G s t earlier u v) :
    ∀ k, k ∈ earlier ++ [u] → k ≠ s → Directed G k t := by
  induction path with
  | initial =>
    intro k inEarlier distinct
    simp at inEarlier
    exact (distinct inEarlier).elim
  | @extend earlier u v w prior col parent adjacent ih =>
    intro k inEarlier distinct
    rcases List.mem_append.mp inEarlier with inPrefix | isV
    · exact ih k inPrefix distinct
    · simp at isV
      rwa [isV]

private theorem ColliderChain.end_shape {G : MarkedGraph n} {u v : Fin n}
    {earlier : List (Fin n)} (path : ColliderChain G earlier u v) :
    G.adjacent u v = true ∧
      (earlier = [] ∨ ∃ before predecessor, earlier = before ++ [predecessor] ∧
        G.arrowheadAt u v = true) := by
  cases path with
  | edge adjacent => exact ⟨adjacent, .inl rfl⟩
  | extend _ collider adjacent =>
    simp only [MarkedGraph.collider, Bool.and_eq_true] at collider
    exact ⟨adjacent, .inr ⟨_, _, rfl, collider.2⟩⟩

private theorem shortcut_collider_has_head {G : MarkedGraph n} (ancestral : AncestralMarks G)
    {a b c : Fin n} (parent : Directed G a c) (headAtA : G.arrowheadAt a b = true)
    (headAtB : G.arrowheadAt b c = true) : G.collider a b c = true := by
  cases head : G.arrowheadAt b a with
  | true => simp [MarkedGraph.collider, head, headAtB]
  | false =>
    obtain ⟨p, edge⟩ : ∃ p, G.marks a b = some p := by
      cases marks : G.marks a b with
      | none => simp [MarkedGraph.arrowheadAt, marks] at headAtA
      | some p => exact ⟨p, rfl⟩
    obtain ⟨near, far⟩ := p
    have nearTrue : near = true := by simpa [MarkedGraph.arrowheadAt, edge] using headAtA
    have farFalse : far = false := by
      simpa [MarkedGraph.arrowheadAt, G.swap_marks a b, edge, Prod.swap] using head
    have intoA : Directed G b a := by
      change G.marks b a = some (false, true)
      simp [G.swap_marks a b, edge, nearTrue, farFalse, Prod.swap]
    exact (ancestral.no_head_into_ancestor
      (.extend (.extend (.refl b) intoA) parent) headAtB).elim

/-- Proposition 1, R′4. The initial PAG displays the definite heads of
minimal collider paths, and the current PMG retains those heads. A
circle on the final edge of a discriminating path must be a tail. -/
theorem r4_prime_sound {G : MarkedGraph n} {initial current : PMG n}
    (ancestral : AncestralMarks G) (initialDisplays : DisplaysMinimalColliders initial G)
    (retained : ∀ {u v}, initial.markAt u v = some .arrow → current.markAt u v = some .arrow)
    {s a b c : Fin n} {earlier : List (Fin n)}
    (path : DiscriminatingPrefix G s c earlier a b)
    (simple : (earlier ++ [a, b, c]).Nodup) (nonadjacent : G.adjacent s c = false)
    (last : G.adjacent b c = true) (parent : Directed G a c)
    (headAtA : G.arrowheadAt a b = true) (circle : current.markAt b c = some .circle) :
    Directed G b c := by
  have headAtC := r2_sound ancestral last (.inr ⟨headAtA, parent⟩)
  obtain ⟨⟨near, far⟩, marks⟩ := Option.isSome_iff_exists.mp last
  have farTrue : far = true := by
    simpa [MarkedGraph.arrowheadAt, G.swap_marks b c, marks, Prod.swap] using headAtC
  subst far
  cases near with
  | false => exact marks
  | true =>
    have headAtB : G.arrowheadAt b c = true := by simp [MarkedGraph.arrowheadAt, marks]
    have collider := shortcut_collider_has_head ancestral parent headAtA headAtB
    have colliderPath : ColliderPath G s c (earlier ++ [a, b, c]) :=
      ⟨earlier ++ [a], b, by simp [List.append_assoc],
        DiscriminatingPrefix.head_eq (tail := [c]) path,
        simple, .extend (DiscriminatingPrefix.is_collider_chain path) collider last⟩
    obtain ⟨q, subsequence, minimal⟩ := exists_minimal_collider_subpath colliderPath
    have qPath := minimal.1
    obtain ⟨before, previous, shape, start, _, chain⟩ := qPath
    have ending := chain.end_shape
    rcases ending.2 with tooShort | ⟨front, predecessor, beforeShape, finalHead⟩
    · have first : previous = s := by simpa [shape, tooShort] using start
      have edge : G.adjacent s c = true := first ▸ ending.1
      simp [nonadjacent] at edge
    · have distinctTarget : previous ≠ c := by
        intro eq
        subst previous
        have loop := ending.1
        simp [MarkedGraph.adjacent, G.loop_free] at loop
      have previousIn : previous ∈ earlier ++ [a, b, c] :=
        subsequence.subset (by simp [shape])
      have previousNotStart : previous ≠ s := by
        intro eq
        subst previous
        simp [nonadjacent] at ending
      have previousIsB : previous = b := by
        by_cases same : previous = b
        · exact same
        · have inParents : previous ∈ earlier ++ [a] := by
            simpa [List.mem_append, same, distinctTarget] using previousIn
          have ahead := DiscriminatingPrefix.parent_until_last path previous inParents previousNotStart
          change G.marks previous c = some (false, true) at ahead
          simp [MarkedGraph.arrowheadAt, ahead] at finalHead
      have finalShape : q = front ++ predecessor :: previous :: c :: [] := by
        simp [shape, beforeShape, List.append_assoc]
      have definite := retained (initialDisplays minimal finalShape).2
      simp [previousIsB, circle] at definite

end
end OpenCausalScience.Papers.WangQinZhou2023.DiscriminatingRule
