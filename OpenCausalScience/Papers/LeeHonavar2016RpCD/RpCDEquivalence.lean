module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDLearning

@[expose] public section

namespace RpCD

open Ground Completion RelationalFiniteSearch
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

variable {A P S : Type} [DecidableEq A] [DecidableEq P]

def SameRelCI (B : Schema A P S) (M N : Model A P) : Prop :=
  ∀ q selected, RelCI B M q selected ↔ RelCI B N q selected

omit [DecidableEq A] [DecidableEq P] in
theorem sameRelCI_of_ground {B : Schema A P S} {M N : Model A P}
    (ground : ∀ s, SameDConnections (graph B M s) (graph B N s)) :
    SameRelCI B M N := by
  intro q selected
  constructor
  · intro separates s x z hit connected
    exact separates s x z hit ((ground s _ x z).mpr connected)
  · intro separates s x z hit connected
    exact separates s x z hit ((ground s _ x z).mp connected)

omit [DecidableEq P] in
/-- A relational CI statement obtained by the classifier also determines the
collider status in a second model with the same ground adjacencies. -/
private theorem classifies_in_equivalent_model
    {B : Schema A P S} {M N : Model A P} (O : Oracle B M)
    {skeleton : List (Dependency A P)} {cuts : List (OrderedCUT B M)}
    {r : Status A} (member : r ∈ cutResults O skeleton cuts)
    (same : SameRelCI B M N)
    (adjSame : ∀ s x y, Adjacent (graph B M s) x y ↔ Adjacent (graph B N s) x y)
    (neighbors : ∀ p ∈ skeleton, ∀ s x z, B.realizes s p x z = true →
       Adjacent (graph B M s) x z) :
    ∃ c ∈ cuts, r.triple = c.witness.triple ∧
      (r.collider = true ↔ HeadToHead (graph B N c.witness.skeleton)
        c.witness.base c.witness.middle c.witness.other) := by
  obtain ⟨c, listed, record⟩ := List.mem_filterMap.mp member
  let w := c.witness
  let wN : CUT B N c.query :=
    { skeleton := w.skeleton
      base := w.base
      middle := w.middle
      other := w.other
      query := w.query
      distinct := w.distinct
      first := (adjSame _ _ _).mp w.first
      second := (adjSame _ _ _).mp w.second
      unshielded := fun hit => w.unshielded ((adjSame _ _ _).mpr hit) }
  unfold classify at record
  cases hit : (conditioningLists (fromPerspective skeleton c.query.target)).find? (O.answer c.query) with
  | none => simp [hit] at record
  | some selected =>
    have h : selected.Sublist (fromPerspective skeleton c.query.target) :=
      mem_conditioningLists.mp (List.mem_of_find?_eq_some hit)
    have ciM := (O.exact _ _).mp (List.find?_some hit)
    have ciN := (same _ _).mp ciM
    have checked := cut_collider_by_neighbors B N wN
      (fun p use x realizes => (adjSame _ _ _).mp
        (neighbors p (List.mem_filter.mp (h.subset use)).1 _ _ _ realizes)) ciN
    simp [hit] at record
    subst r
    exact ⟨c, listed, rfl, by simpa [wN, w] using checked⟩

theorem classified_extensions_relCI_iff {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (skeleton : List (Dependency A P))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (different : ∀ q ∈ skeleton, q.source ≠ q.target)
    {cuts : List (OrderedCUT B M)} (coverage : CUTCoverage cuts) (live order : List A)
    (attrLive : ∀ s v, B.attributeOf s v ∈ live) :
    Consistent (classifyConstraints (classAdjacent skeleton) (cutResults O skeleton cuts)) live order ↔
      order.Nodup ∧ (∀ v, v ∈ order ↔ v ∈ live) ∧ SameRelCI B M (reorient skeleton order) := by
  constructor
  · intro valid
    obtain ⟨unique, mem, same⟩ := (classified_extensions_ground_iff L O skeleton
      included closed sound different coverage live order attrLive).mp valid
    exact ⟨unique, mem, sameRelCI_of_ground same⟩
  · rintro ⟨unique, mem, same⟩
    have adj := reorient_skeleton_iff L O skeleton included closed sound different live order attrLive mem
    have neighbors (p : Dependency A P) (pIn : p ∈ skeleton) (s : S) (x z : Fin (B.size s))
        (hit : B.realizes s p x z = true) : Adjacent (graph B M s) x z :=
      adjacent_of_surviving L O (sound p pIn) hit
    have covered (r : Status A) (member : r ∈ cutResults O skeleton cuts) :
        r.triple.left ∈ live ∧ r.triple.middle ∈ live ∧ r.triple.right ∈ live := by
      obtain ⟨c, _, equal, _⟩ := classified_sound L O skeleton sound member
      rw [equal]
      exact ⟨attrLive .., attrLive .., attrLive ..⟩
    apply (classified_extensions_iff _ _ live order covered).mpr
    refine ⟨unique, mem, fun r member => ?_⟩
    obtain ⟨c, _, equal, agrees⟩ := classifies_in_equivalent_model O member same adj neighbors
    let w := c.witness
    have xy := class_adjacent_of_ground w.first skeleton included L closed
    have zy := class_adjacent_of_ground w.second skeleton included L closed
    unfold Matches HeadToHead at *
    rw [reorient_edge_iff L O skeleton included closed sound] at agrees
    rw [reorient_edge_iff L O skeleton included closed sound] at agrees
    simp [equal, CUT.triple, arrow, w, xy, zy, w.first, w.second] at agrees ⊢
    exact agrees

theorem revisedRpCD_relational_correct {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (initial : List (Dependency A P))
    (initialContains : ∀ q ∈ M.dependencies, q ∈ initial)
    (initialClosed : PairClosed (phaseQuery L O) initial)
    (initialValid : ∀ q ∈ initial, q.source ≠ q.target)
    (initialLegal : ∀ q ∈ initial, L.valid q)
    {cuts : List (OrderedCUT B M)} (coverage : CUTCoverage cuts)
    (attributes : List A) (unique : attributes.Nodup)
    (attrLive : ∀ s v, B.attributeOf s v ∈ attributes) :
    let learned := revisedRpCD L O initial cuts attributes
    (∀ d, d ∈ learned.1 ↔ d ∈ M.dependencies ∨ L.reverse d ∈ M.dependencies) ∧
    (∀ u ∈ attributes, ∀ v ∈ attributes, classAdjacent learned.1 u v = true →
      (learned.2 u v = true ↔ ∀ order, order.Nodup →
        (∀ a, a ∈ order ↔ a ∈ attributes) →
        SameRelCI B M (reorient learned.1 order) →
        order.idxOf v < order.idxOf u)) := by
  let learned := revisedRpCD L O initial cuts attributes
  let skeleton := learned.1
  have ground := revisedRpCD_sound_complete L O initial initialContains initialClosed initialValid initialLegal
    coverage attributes unique attrLive
  have recovered := phaseOne_ground_exact L O initial initialContains initialClosed initialValid initialLegal
  have included (q : Dependency A P) (member : q ∈ M.dependencies) :
      q ∈ skeleton := (recovered q).mpr ⟨initialContains q member, .inl (decide_eq_true member)⟩
  have sound (q : Dependency A P) (member : q ∈ skeleton) :
      pairPresent (phaseQuery L O) (trueDependency M) q := ((recovered q).mp member).2
  have different (q : Dependency A P) (member : q ∈ skeleton) :
      q.source ≠ q.target := initialValid q ((recovered q).mp member).1
  have closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton :=
    search_closed (phaseQuery L O) L.involution initial initialClosed (initial.length + 1)
  refine ⟨ground.1, fun u hu v hv adj => ?_⟩
  rw [ground.2 u hu v hv adj]
  constructor
  · intro compelled order nodup mem same
    have consistent := (classified_extensions_relCI_iff L O skeleton included closed
      sound different coverage _ order attrLive).mpr ⟨nodup, mem, same⟩
    exact compelled order nodup mem
      ((classified_extensions_ground_iff L O skeleton included closed sound different
        coverage _ order attrLive).mp consistent).2.2
  · intro compelled order nodup mem same
    exact compelled order nodup mem (sameRelCI_of_ground same)

end RpCD

end
