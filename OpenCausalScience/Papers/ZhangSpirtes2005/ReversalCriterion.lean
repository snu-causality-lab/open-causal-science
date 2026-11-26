module
public import OpenCausalScience.Papers.ZhangSpirtes2005.MarkChangeMarkedGraph

/-! The parent and spouse conditions for a legitimate reversal in Zhang and
Spirtes (2005), Lemma 2.
Source: https://www.cmu.edu/dietrich/philosophy/docs/spirtes/uai05.pdf
-/

namespace OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange

open MarkedGraph (adjacent arrowheadAt collider)
open MixedGraph (Reach)
open Zhang2008OrientationRules.Orientations (AncestralMarks Directed)

@[expose] public section

variable {n : Nat}

private theorem distinct_of_directed {G : MarkedGraph n} {a b : Fin n}
    (edge : Directed G a b) : a ≠ b := by
  rintro rfl
  simp [Directed, G.loop_free] at edge

private theorem reverse_of_directed {G : MarkedGraph n} {a b : Fin n}
    (edge : Directed G a b) : G.marks b a = some (true, false) := by
  change G.marks a b = some (false, true) at edge
  simp [G.swap_marks a b, edge, Prod.swap]

private theorem adjacency_of_edit {G H : MarkedGraph n} {a b : Fin n}
    (edit : AddedHead G H a b) (u v : Fin n) : G.adjacent u v = H.adjacent u v := by
  by_cases forward : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := forward
    simp [adjacent, show G.marks _ _ = _ from edit.original, show H.marks _ _ = _ from edit.changed]
  by_cases backward : u = b ∧ v = a
  · obtain ⟨rfl, rfl⟩ := backward
    have original := reverse_of_directed edit.original
    have changed := edit.changed
    change H.marks _ _ = some (true, true) at changed
    unfold adjacent
    rw [original, H.swap_marks _ _, changed]
    rfl
  have first : u ≠ a ∨ v ≠ b := by
    by_cases h : u = a
    · exact .inr fun same => forward ⟨h, same⟩
    · exact .inl h
  have second : u ≠ b ∨ v ≠ a := by
    by_cases h : u = b
    · exact .inr fun same => backward ⟨h, same⟩
    · exact .inl h
  simp [adjacent, edit.other u v first second]

private theorem maximality_after_edit {G H : MarkedGraph n} {a b : Fin n}
    (edit : AddedHead G H a b) (maximal : G.HasSeparators)
    (equivalent : G.SameSeparations H) : H.HasSeparators := by
  intro u v distinct absent
  obtain ⟨C, legal, separated⟩ := maximal u v distinct ((adjacency_of_edit edit u v).trans absent)
  exact ⟨C, legal, (equivalent u v C legal).mp separated⟩

private theorem incoming_is_adjacent {G H : MarkedGraph n} {a b c : Fin n}
    (edit : AddedHead G H a b) (maximum : G.HasSeparators) (equivalent : G.SameSeparations H)
    (ca : c ≠ a) (cb : c ≠ b) (head : G.arrowheadAt a c = true) : G.adjacent c b = true := by
  cases adjacentCB : G.adjacent c b with
  | true => rfl
  | false =>
    have preservedHead : H.arrowheadAt a c = true := by
      unfold arrowheadAt at *
      rwa [edit.other a c (.inr cb) (.inr ca)]
    have adjacentCA : G.adjacent c a = true := by
      rcases h : G.marks c a with _ | ⟨p, q⟩
      · simp [arrowheadAt, G.swap_marks c a, h] at head
      · simp [adjacent, h]
    have adjacentAB : H.adjacent a b = true := by
      simp [adjacent, show H.marks a b = _ from edit.changed]
    have inH : H.UnshieldedCollider c a b :=
      ⟨ca, cb, distinct_of_directed edit.original, (adjacency_of_edit edit c a).symm.trans adjacentCA,
        adjacentAB, (adjacency_of_edit edit c b).symm.trans adjacentCB,
        by
          have headAB : H.arrowheadAt a b = true := by
            simp [arrowheadAt, show H.marks a b = _ from edit.changed]
          simp [collider, preservedHead, headAB]⟩
    have inG := (AliRichardsonSpirtes2009.equivalent_unshielded_colliders maximum
      (maximality_after_edit edit maximum equivalent) equivalent c a b).mpr inH
    have noncollider := inG.2.2.2.2.2.2
    simp [collider, arrowheadAt, show G.marks a b = _ from edit.original] at noncollider

private theorem parent_of_legitimate_addition {G H : MarkedGraph n} {a b c : Fin n}
    (edit : AddedHead G H a b) (noLines : NoLines G) (ancestral : AncestralMarks G)
    (maximum : G.HasSeparators) (equivalent : G.SameSeparations H)
    (ca : c ≠ a) (cb : c ≠ b) (parent : Directed G c a) : Directed G c b := by
  have head : G.arrowheadAt a c = true := by simp [arrowheadAt, reverse_of_directed parent]
  obtain ⟨⟨p, q⟩, marked⟩ := Option.isSome_iff_exists.mp
    (incoming_is_adjacent edit maximum equivalent ca cb head)
  cases p with
  | false =>
    cases q with
    | false => exact (noLines c b marked).elim
    | true => exact marked
  | true =>
    have route : Reach (Directed G) c b := .extend (.extend (.refl _) parent) edit.original
    exact (ancestral.no_head_into_ancestor route (by simp [arrowheadAt, marked])).elim

private theorem spouse_of_legitimate_addition {G H : MarkedGraph n} {a b c : Fin n}
    (edit : AddedHead G H a b) (noLines : NoLines G) (ancestral : AncestralMarks G)
    (maximum : G.HasSeparators) (equivalent : G.SameSeparations H)
    (ca : c ≠ a) (cb : c ≠ b) (parentBack : Directed G c b → Directed G c a)
    (spouse : Spouse G c a) : Spouse G c b := by
  have spouseMarks : G.marks c a = some (true, true) := spouse
  have head : G.arrowheadAt a c = true := by simp [arrowheadAt, G.swap_marks c a, spouseMarks, Prod.swap]
  obtain ⟨⟨p, q⟩, marked⟩ := Option.isSome_iff_exists.mp
    (incoming_is_adjacent edit maximum equivalent ca cb head)
  cases p with
  | false =>
    cases q with
    | false => exact (noLines c b marked).elim
    | true =>
      have conflict : G.marks c a = some (false, true) := parentBack marked
      rw [spouseMarks] at conflict
      contradiction
  | true =>
    cases q with
    | false =>
      have fromB : Directed G b c := by
        change G.marks b c = some (false, true)
        simp [G.swap_marks c b, marked, Prod.swap]
      have route : Reach (Directed G) a c := .extend (.extend (.refl _) edit.original) fromB
      exact (ancestral.no_head_into_ancestor route head).elim
    | true => exact marked

/-- Matching is necessary when both directions into the same bidirected
intermediate preserve the separation relation of the respective DMAG. -/
theorem matching_of_legitimate_edits {G H K : MarkedGraph n} {a b : Fin n}
    (forward : AddedHead G H a b) (backward : AddedHead K H b a)
    (noLinesG : NoLines G) (ancestralG : AncestralMarks G) (maximumG : G.HasSeparators)
    (noLinesK : NoLines K) (ancestralK : AncestralMarks K) (maximumK : K.HasSeparators)
    (equivalentGH : G.SameSeparations H) (equivalentKH : K.SameSeparations H) :
    MatchingParentsSpouses G a b := by
  intro c ca cb
  have sameA : K.marks c a = G.marks c a :=
    (backward.other c a (.inl cb) (.inl ca)).symm.trans (forward.other c a (.inl ca) (.inl cb))
  have sameB : K.marks c b = G.marks c b :=
    (backward.other c b (.inl cb) (.inl ca)).symm.trans (forward.other c b (.inl ca) (.inl cb))
  have parentForward := parent_of_legitimate_addition forward noLinesG ancestralG maximumG equivalentGH ca cb
  have parentReverse := parent_of_legitimate_addition backward noLinesK ancestralK maximumK equivalentKH cb ca
  have parentBack : Directed G c b → Directed G c a := by
    simpa only [Directed, sameA, sameB] using parentReverse
  have parentK : Directed K c a → Directed K c b := by
    simpa only [Directed, sameA, sameB] using parentForward
  have spouseForward := spouse_of_legitimate_addition forward noLinesG ancestralG maximumG equivalentGH ca cb parentBack
  have spouseReverse := spouse_of_legitimate_addition backward noLinesK ancestralK maximumK equivalentKH cb ca parentK
  refine ⟨⟨parentForward, parentBack⟩, spouseForward, ?_⟩
  simpa only [Spouse, sameA, sameB] using spouseReverse

private theorem no_lines_before_edit {K H : MarkedGraph n} {a b : Fin n}
    (edit : AddedHead K H a b) (lineFree : NoLines H) : NoLines K := by
  intro u v line
  have first : u ≠ a ∨ v ≠ b := by
    by_cases ua : u = a
    · right
      intro vb
      subst u
      subst v
      rw [show K.marks a b = _ from edit.original] at line
      contradiction
    · exact .inl ua
  have second : u ≠ b ∨ v ≠ a := by
    by_cases ub : u = b
    · right
      intro va
      subst u
      subst v
      rw [reverse_of_directed edit.original] at line
      contradiction
    · exact .inl ub
  exact lineFree u v ((edit.other u v first second).trans line)

private theorem maximality_before_edit {K H : MarkedGraph n} {a b : Fin n}
    (edit : AddedHead K H a b) (maximal : H.HasSeparators)
    (equivalent : K.SameSeparations H) : K.HasSeparators := by
  intro u v distinct absent
  obtain ⟨C, legal, separated⟩ := maximal u v distinct ((adjacency_of_edit edit u v).symm.trans absent)
  exact ⟨C, legal, (equivalent u v C legal).mpr separated⟩

/-- For a directed edge, matching external vertices is exactly the equality
of the parent and spouse sets stated in Lemma 2. -/
theorem matching_iff_parent_and_spouse_sets {G : MarkedGraph n} {a b : Fin n}
    (edge : Directed G a b) : MatchingParentsSpouses G a b ↔
      (∀ c, Directed G c b ↔ Directed G c a ∨ c = a) ∧
      (∀ c, Spouse G c b ↔ Spouse G c a) := by
  constructor
  · intro matching
    have marked : G.marks a b = some (false, true) := edge
    have reverse := reverse_of_directed edge
    constructor <;> intro c
    · by_cases ca : c = a
      · subst c
        simp [Directed, marked]
      by_cases cb : c = b
      · subst c
        simp [Directed, G.loop_free, reverse, ca]
      simpa only [ca, or_false] using (matching c ca cb).1.symm
    · by_cases ca : c = a
      · subst c
        simp [Spouse, marked, G.loop_free]
      by_cases cb : c = b
      · subst c
        simp [Spouse, reverse, G.loop_free]
      exact (matching c ca cb).2.symm
  · rintro ⟨parents, spouses⟩ c ca _
    exact ⟨by simpa only [ca, or_false] using (parents c).symm, (spouses c).symm⟩

/-- A directed maximal ancestral graph has no undirected edges. -/
structure DMAG (G : MarkedGraph n) : Prop where
  lineFree : NoLines G
  ancestral : AncestralMarks G
  maximal : G.HasSeparators

private theorem ancestor_of_directed_reach {G : MarkedGraph n} {noLines : NoLines G}
    {C : Fin n → Bool} {u v : Fin n} (route : Reach (Directed G) u v)
    (active : (asMixed G noLines).AncestorOf C v) : (asMixed G noLines).AncestorOf C u := by
  induction route with
  | refl => exact active
  | extend _ edge ih => exact ih (.parent (decide_eq_true edge) active)

private theorem directed_reach_prepend {G : MarkedGraph n} {u v w : Fin n}
    (edge : Directed G u v) (route : Reach (Directed G) v w) : Reach (Directed G) u w := by
  induction route with
  | refl => exact .extend (.refl _) edge
  | extend _ step ih => exact .extend ih step

private theorem directed_reach_of_singleton_ancestor {G : MarkedGraph n} {noLines : NoLines G}
    {u v : Fin n} (active : (asMixed G noLines).AncestorOf (· == v) u) :
    Reach (Directed G) u v := by
  induction active with
  | conditioned inside =>
    obtain rfl := beq_iff_eq.mp inside
    exact .refl _
  | @parent u w edge _ ih =>
    have marked : G.marks u w = some (false, true) := of_decide_eq_true edge
    exact directed_reach_prepend marked ih

/-- Removing the head at `a` from `a ↔ b` gives an ancestral graph if the
resulting graph has matching external parents and spouses at the endpoints. -/
theorem ancestral_before_of_matching {G H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (edit : AddedHead G H a b) (matching : MatchingParentsSpouses G a b)
    (ancestral : AncestralMarks H) : AncestralMarks G := by
  constructor
  · intro u v w line
    exact (noLines u v line).elim
  · intro u v route head
    have active : (asMixed G noLines).AncestorOf (· == v) u :=
      ancestor_of_directed_reach route (.conditioned (by simp))
    rcases ancestor_after_change (noLines' := no_lines_after noLines edit) edit matching active with
      kept | ⟨same, displaced⟩
    · exact ancestral.no_head_into_ancestor (directed_reach_of_singleton_ancestor kept)
        ((arrowhead_iff_after_addition edit u v).mpr (.inl head))
    · subst u
      have va : v ≠ a := by
        intro equal
        subst v
        simp [MarkedGraph.arrowheadAt, G.loop_free] at head
      have vb : v ≠ b := by
        intro equal
        subst v
        simp [MarkedGraph.arrowheadAt, show G.marks a b = some (false, true) from edit.original] at head
      cases incident : G.marks a v with
      | none => simp [MarkedGraph.arrowheadAt, incident] at head
      | some marks =>
        obtain ⟨near, far⟩ := marks
        have nearHead : near = true := by simpa [MarkedGraph.arrowheadAt, incident] using head
        subst near
        have incoming : G.marks v a = some (far, true) := by
          simp [G.swap_marks a v, incident, Prod.swap]
        have matchingAtB : G.marks v b = some (far, true) := by
          cases far with
          | false => exact (matching v va vb).1.mp incoming
          | true => exact (matching v va vb).2.mp incoming
        have keptAtB := (edit.other v b (.inl va) (.inl vb)).trans matchingAtB
        apply ancestral.no_head_into_ancestor (directed_reach_of_singleton_ancestor displaced)
        simp [MarkedGraph.arrowheadAt, H.swap_marks v b, keptAtB, Prod.swap]

/-- These two edits make up a legitimate reversal when the intermediate and
reversed graphs are DMAGs and each edit preserves the separation relation. -/
structure LegitimateReversal (G H K : MarkedGraph n) : Prop where
  intermediate : DMAG H
  reversed : DMAG K
  firstEquivalent : G.SameSeparations H
  secondEquivalent : K.SameSeparations H

/-- The two edits of a reversal are legitimate exactly when the external
parents and spouses match. Only the starting graph is assumed to be a DMAG. -/
theorem legitimate_reversal_iff_of_edits {G H K : MarkedGraph n} {a b : Fin n}
    (original : DMAG G) (forward : AddedHead G H a b) (backward : AddedHead K H b a) :
    LegitimateReversal G H K ↔ MatchingParentsSpouses G a b := by
  constructor
  · intro legitimate
    exact matching_of_legitimate_edits forward backward original.lineFree original.ancestral original.maximal
      legitimate.reversed.lineFree legitimate.reversed.ancestral legitimate.reversed.maximal
      legitimate.firstEquivalent legitimate.secondEquivalent
  · intro matching
    have hNoLines := no_lines_after original.lineFree forward
    have hAncestral := (ancestral_iff_no_alternate_path original.lineFree original.ancestral forward).mpr
      (no_alternate_of_matching original.ancestral forward.original matching)
    have firstEquivalent := same_separations_of_matching original.lineFree forward matching
    have hMaximal := maximality_after_edit forward original.maximal firstEquivalent
    have kNoLines := no_lines_before_edit backward hNoLines
    have matchingK := matching_of_reverse_edits forward backward matching
    have kAncestral := ancestral_before_of_matching kNoLines backward matchingK hAncestral
    have secondEquivalent := same_separations_of_matching kNoLines backward matchingK
    have kMaximal := maximality_before_edit backward hMaximal secondEquivalent
    exact ⟨⟨hNoLines, hAncestral, hMaximal⟩, ⟨kNoLines, kAncestral, kMaximal⟩,
      firstEquivalent, secondEquivalent⟩

/-- Zhang and Spirtes (2005), Lemma 2. The fixed directed-to-bidirected and
bidirected-to-directed edits form a legitimate reversal exactly when the
target's parents are the source's parents plus the source, and the spouse
sets agree. -/
theorem legitimate_reversal_iff_parent_and_spouse_sets {G H K : MarkedGraph n} {a b : Fin n}
    (original : DMAG G) (forward : AddedHead G H a b) (backward : AddedHead K H b a) :
    LegitimateReversal G H K ↔
      (∀ c, Directed G c b ↔ Directed G c a ∨ c = a) ∧
      (∀ c, Spouse G c b ↔ Spouse G c a) :=
  (legitimate_reversal_iff_of_edits original forward backward).trans
    (matching_iff_parent_and_spouse_sets forward.original)

end
end OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange
