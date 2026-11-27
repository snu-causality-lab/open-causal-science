module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDPhaseOne
public import OpenCausalScience.Papers.VermaPearl1990.Equivalence

@[expose] public section

namespace RpCD

open Ground Completion RelationalFiniteSearch
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.VermaPearl1990.Equivalence
open OpenCausalScience.Papers.Chickering1995.Transformation

variable {A P S : Type} [DecidableEq A] [DecidableEq P]

def classAdjacent (skeleton : List (Dependency A P)) (u v : A) : Bool :=
  skeleton.any fun p => p.source == u && p.target == v

def fromPerspective (skeleton : List (Dependency A P)) (v : A) : List (Dependency A P) :=
  skeleton.filter fun p => p.target == v

def learnedSkeleton {B : Schema A P S} {M : Model A P} (L : PathSemantics B)
    (O : Oracle B M) (initial : List (Dependency A P)) : List (Dependency A P) :=
  phaseOne (phaseQuery L O) initial

def reorient (skeleton : List (Dependency A P)) (order : List A) : Model A P where
  dependencies := skeleton.filter fun p => decide (order.idxOf p.target < order.idxOf p.source)
  rank := fun v => order.length - order.idxOf v
  acyclic := by
    intro p member
    have direction : order.idxOf p.target < order.idxOf p.source :=
      of_decide_eq_true (List.mem_filter.mp member).2
    have inBounds : order.idxOf p.source ≤ order.length := List.idxOf_le_length
    omega

omit [DecidableEq A] [DecidableEq P] in
private theorem edge_iff_rank {B : Schema A P S} {M : Model A P} {s : S}
    {u v : Fin (B.size s)} :
    (graph B M s).edge u v = true ↔
      Adjacent (graph B M s) u v ∧ M.rank (B.attributeOf s u) < M.rank (B.attributeOf s v) := by
  constructor
  · intro edge
    exact ⟨.inl edge, (graph B M s).edge_increases _ _ edge⟩
  · rintro ⟨adj, order⟩
    rcases adj with forward | backward
    · exact forward
    · exact (Nat.lt_asymm order ((graph B M s).edge_increases _ _ backward)).elim

omit [DecidableEq A] [DecidableEq P] in
theorem headToHead_iff_ranks {B : Schema A P S} {M : Model A P} {s : S}
    {x y z : Fin (B.size s)} (xy : Adjacent (graph B M s) x y)
    (zy : Adjacent (graph B M s) z y) :
    HeadToHead (graph B M s) x y z ↔
      M.rank (B.attributeOf s x) < M.rank (B.attributeOf s y) ∧
      M.rank (B.attributeOf s z) < M.rank (B.attributeOf s y) := by
  simp [HeadToHead, edge_iff_rank, xy, zy]

omit [DecidableEq A] [DecidableEq P] in
theorem lift_ground_adjacent {B : Schema A P S} {M : Model A P}
    {s : S} {x y : Fin (B.size s)}
    (adj : Adjacent (graph B M s) x y)
    (skeleton : List (Dependency A P)) (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (L : PathSemantics B) (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton) :
    ∃ q ∈ skeleton, B.realizes s q y x = true := by
  rcases adj with forward | backward
  · obtain ⟨q, member, hit⟩ := List.any_eq_true.mp forward
    exact ⟨q, included q member, hit⟩
  · obtain ⟨q, member, hit⟩ := List.any_eq_true.mp backward
    exact ⟨L.reverse q, closed _ (included q member), by rw [L.reverse_realizes, hit]⟩

omit [DecidableEq P] in
theorem class_adjacent_of_ground {B : Schema A P S} {M : Model A P}
    {s : S} {x y : Fin (B.size s)}
    (adj : Adjacent (graph B M s) x y)
    (skeleton : List (Dependency A P)) (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (L : PathSemantics B) (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton) :
    classAdjacent skeleton (B.attributeOf s x) (B.attributeOf s y) = true := by
  obtain ⟨q, member, hit⟩ := lift_ground_adjacent adj skeleton included L closed
  have ⟨target, source⟩ := B.types s q y x hit
  exact List.any_eq_true.mpr ⟨q, member, by simp [target, source]⟩

theorem reorient_edge_iff {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (skeleton : List (Dependency A P))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (order : List A) (s : S) (x y : Fin (B.size s)) :
    (graph B (reorient skeleton order) s).edge x y = true ↔
      Adjacent (graph B M s) x y ∧ order.idxOf (B.attributeOf s y) < order.idxOf (B.attributeOf s x) := by
  constructor
  · intro forward
    obtain ⟨p, member, hit⟩ := List.any_eq_true.mp forward
    obtain ⟨original, direction⟩ := List.mem_filter.mp member
    have ⟨target, source⟩ := B.types s p y x hit
    refine ⟨Or.symm (adjacent_of_surviving L O (sound p original) hit), ?_⟩
    simpa [source, target] using (of_decide_eq_true direction :
      order.idxOf p.target < order.idxOf p.source)
  · rintro ⟨adj, direction⟩
    obtain ⟨q, member, hit⟩ := lift_ground_adjacent adj skeleton included L closed
    have ⟨target, source⟩ := B.types s q y x hit
    exact List.any_eq_true.mpr ⟨q, List.mem_filter.mpr ⟨member,
      decide_eq_true (by simpa [source, target] using direction)⟩, hit⟩

def classTriple (B : Schema A P S) (s : S) (x y z : Fin (B.size s)) : Triple A :=
  ⟨B.attributeOf s x, B.attributeOf s y, B.attributeOf s z⟩

def Triple.reverse (t : Triple A) : Triple A := ⟨t.right, t.middle, t.left⟩

/-- The exact CUT search supplies both orders of each realizable class triple.
Its finite representatives can come from different skeletons. -/
structure CUTCoverage {B : Schema A P S} {M : Model A P} (cuts : List (OrderedCUT B M)) : Prop where
  distinct : ∀ c ∈ cuts, ∀ s x z, B.realizes s c.query x z = true → x ≠ z
  forward : ∀ s x y z, x ≠ z →
    Adjacent (graph B M s) x y → Adjacent (graph B M s) z y →
    ¬ Adjacent (graph B M s) x z →
    ∃ c ∈ cuts, c.witness.triple = classTriple B s x y z

def cutResults {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (skeleton : List (Dependency A P)) (cuts : List (OrderedCUT B M)) : List (Status A) :=
  cuts.filterMap (classify O (fromPerspective skeleton))

theorem classified_sound {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (skeleton : List (Dependency A P))
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    {cuts : List (OrderedCUT B M)} {result : Status A}
    (member : result ∈ cutResults O skeleton cuts) :
    ∃ c ∈ cuts, result.triple = c.witness.triple ∧
      (result.collider = true ↔ HeadToHead (graph B M c.witness.skeleton)
        c.witness.base c.witness.middle c.witness.other) := by
  obtain ⟨c, listed, checked⟩ := List.mem_filterMap.mp member
  exact ⟨c, listed, classify_sound O _ c
    (fun p mem _ hit => adjacent_of_surviving L O (sound p (List.mem_filter.mp mem).1) hit) checked⟩

theorem classified_covers {B : Schema A P S} {M : Model A P} (O : Oracle B M)
    (skeleton : List (Dependency A P)) (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    {cuts : List (OrderedCUT B M)} (coverage : CUTCoverage cuts)
    (s : S) (x y z : Fin (B.size s)) (distinct : x ≠ z)
    (xy : Adjacent (graph B M s) x y) (zy : Adjacent (graph B M s) z y)
    (xz : ¬ Adjacent (graph B M s) x z) :
    ∃ result ∈ cutResults O skeleton cuts,
      result.triple = classTriple B s x y z ∨ result.triple = classTriple B s z y x := by
  obtain ⟨f, fIn, fType⟩ := coverage.forward s x y z distinct xy zy xz
  obtain ⟨r, rIn, rType⟩ := coverage.forward s z y x distinct.symm zy xy (fun adj => xz (Or.symm adj))
  have hf := B.types _ _ _ _ f.witness.query
  have hr := B.types _ _ _ _ r.witness.query
  have source : f.query.source = r.query.target := by
    have same := congrArg Triple.right fType
    have other := congrArg Triple.left rType
    exact hf.2.symm.trans (same.trans (other.symm.trans hr.1))
  have target : f.query.target = r.query.source := by
    have same := congrArg Triple.left fType
    have other := congrArg Triple.right rType
    exact hf.1.symm.trans (same.trans (other.symm.trans hr.2))
  have available : ∀ x p, p ∈ parents M x → p ∈ fromPerspective skeleton x := by
    intro atClass p mem
    obtain ⟨trueP, same⟩ := List.mem_filter.mp mem
    exact List.mem_filter.mpr ⟨included p trueP, same⟩
  have seen (c : OrderedCUT B M) (listed : c ∈ cuts)
      (found : ∃ result, classify O (fromPerspective skeleton) c = some result) :
      ∃ result ∈ cutResults O skeleton cuts, result.triple = c.witness.triple := by
    obtain ⟨result, record⟩ := found
    refine ⟨result, List.mem_filterMap.mpr ⟨c, listed, record⟩, ?_⟩
    unfold classify at record
    cases next : (RelationalFiniteSearch.conditioningLists
      (fromPerspective skeleton c.query.target)).find? (O.answer c.query) with
    | none => simp [next] at record
    | some selected =>
      simp [next] at record
      exact congrArg Status.triple record.symm
  rcases classify_one_of_two O (fromPerspective skeleton) f r source target available
    (coverage.distinct f fIn) (coverage.distinct r rIn) with fFound | rFound
  · obtain ⟨result, member, same⟩ := seen f fIn fFound
    exact ⟨result, member, Or.inl (same.trans fType)⟩
  · obtain ⟨result, member, same⟩ := seen r rIn rFound
    exact ⟨result, member, Or.inr (same.trans rType)⟩


omit [DecidableEq P] in
private theorem classAdj_symm {B : Schema A P S} (L : PathSemantics B)
    {skeleton : List (Dependency A P)}
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton) (x y : A) :
    classAdjacent skeleton x y = classAdjacent skeleton y x := by
  apply Bool.eq_iff_iff.mpr
  have flip (u v : A) (adj : classAdjacent skeleton u v = true) :
      classAdjacent skeleton v u = true := by
    obtain ⟨p, member, hit⟩ := List.any_eq_true.mp adj
    have ⟨source, target⟩ := L.endpoints p
    obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp hit
    exact List.any_eq_true.mpr ⟨L.reverse p, closed p member, by
      simp [source, target, eq_of_beq left, eq_of_beq right]⟩
  exact ⟨flip x y, flip y x⟩

omit [DecidableEq P] in
private theorem classAdj_loopless {skeleton : List (Dependency A P)}
    (different : ∀ q ∈ skeleton, q.source ≠ q.target) (v : A) :
    classAdjacent skeleton v v = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨p, member, h⟩ := List.any_eq_true.mp hit
  obtain ⟨src, dst⟩ := Bool.and_eq_true_iff.mp h
  exact different p member ((eq_of_beq src).trans (eq_of_beq dst).symm)

omit [DecidableEq A] [DecidableEq P] in
private theorem compare_ground_triples {B : Schema A P S} {M : Model A P}
    {s t : S} {x y z : Fin (B.size s)} {a b c : Fin (B.size t)}
    (xy : Adjacent (graph B M s) x y) (zy : Adjacent (graph B M s) z y)
    (ab : Adjacent (graph B M t) a b) (cb : Adjacent (graph B M t) c b)
    (classes : classTriple B s x y z = classTriple B t a b c) :
    HeadToHead (graph B M s) x y z ↔ HeadToHead (graph B M t) a b c := by
  rw [headToHead_iff_ranks xy zy, headToHead_iff_ranks ab cb]
  have left := congrArg Triple.left classes
  have middle := congrArg Triple.middle classes
  have right := congrArg Triple.right classes
  simp only [classTriple] at left middle right
  rw [left, middle, right]

theorem reorient_skeleton_iff {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (skeleton : List (Dependency A P))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (different : ∀ q ∈ skeleton, q.source ≠ q.target)
    (live order : List A) (attrLive : ∀ s v, B.attributeOf s v ∈ live)
    (mem : ∀ v, v ∈ order ↔ v ∈ live) (s : S) (x y : Fin (B.size s)) :
    Adjacent (graph B M s) x y ↔ Adjacent (graph B (reorient skeleton order) s) x y := by
  let C : Constraints A := ⟨classAdjacent skeleton, fun _ _ => false, fun _ _ _ => false⟩
  have input : ValidInput C := ⟨classAdj_symm L closed, classAdj_loopless different, by simp [C]⟩
  constructor
  · intro found
    have classAdj := class_adjacent_of_ground found skeleton included L closed
    rcases arrow_direction input ((mem _).mpr (attrLive s x)) ((mem _).mpr (attrLive s y))
      classAdj with forward | backward
    · exact .inl ((reorient_edge_iff L O skeleton included closed sound order s x y).mpr ⟨found, forward.2⟩)
    · exact .inr ((reorient_edge_iff L O skeleton included closed sound order s y x).mpr ⟨Or.symm found, backward.2⟩)
  · rintro (forward | backward)
    · exact ((reorient_edge_iff L O skeleton included closed sound order _ _ _).mp forward).1
    · exact Or.symm ((reorient_edge_iff L O skeleton included closed sound order _ _ _).mp backward).1

theorem classified_extensions_ground_iff {B : Schema A P S} {M : Model A P}
    (L : PathSemantics B) (O : Oracle B M) (skeleton : List (Dependency A P))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (different : ∀ q ∈ skeleton, q.source ≠ q.target)
    {cuts : List (OrderedCUT B M)} (coverage : CUTCoverage cuts) (live order : List A)
    (attrLive : ∀ s v, B.attributeOf s v ∈ live) :
    Consistent (classifyConstraints (classAdjacent skeleton) (cutResults O skeleton cuts)) live order ↔
      order.Nodup ∧ (∀ v, v ∈ order ↔ v ∈ live) ∧
        ∀ s, SameDConnections (graph B M s) (graph B (reorient skeleton order) s) := by
  let adj := classAdjacent skeleton
  let results := cutResults O skeleton cuts
  let C : Constraints A := ⟨adj, fun _ _ => false, fun _ _ _ => false⟩
  have covered (r : Status A) (member : r ∈ results) :
      r.triple.left ∈ live ∧ r.triple.middle ∈ live ∧ r.triple.right ∈ live := by
    obtain ⟨c, _, equal, _⟩ := classified_sound L O skeleton sound member
    rw [equal]
    exact ⟨attrLive .., attrLive .., attrLive ..⟩
  rw [classified_extensions_iff _ _ live order covered]
  have edgeFor {s : S} {x y : Fin (B.size s)} (found : Adjacent (graph B M s) x y) :
      (graph B (reorient skeleton order) s).edge x y = true ↔
        arrow C order (B.attributeOf s x) (B.attributeOf s y) := by
    rw [reorient_edge_iff L O skeleton included closed sound order s x y]
    simp [arrow, C, adj, found, class_adjacent_of_ground found skeleton included L closed]
  have skeletonFor (mem : ∀ v, v ∈ order ↔ v ∈ live) (s : S) (x y : Fin (B.size s)) :=
    reorient_skeleton_iff L O skeleton included closed sound different live order attrLive mem s x y
  have matchesFor (s : S) (x y z : Fin (B.size s)) (xy : Adjacent (graph B M s) x y)
      (zy : Adjacent (graph B M s) z y) (r : Status A) (classes : r.triple = classTriple B s x y z) :
      Matches adj order r ↔ (r.collider = true ↔ HeadToHead (graph B (reorient skeleton order) s) x y z) := by
    simp only [Matches, classes, classTriple, HeadToHead]
    rw [edgeFor xy, edgeFor zy]
  have statusFor (s : S) (x y z : Fin (B.size s)) (xy : Adjacent (graph B M s) x y)
      (zy : Adjacent (graph B M s) z y) (r : Status A)
      (member : r ∈ results) (classes : r.triple = classTriple B s x y z) :
      r.collider = true ↔ HeadToHead (graph B M s) x y z := by
    obtain ⟨c, _, names, verified⟩ := classified_sound L O skeleton sound member
    exact verified.trans (compare_ground_triples c.witness.first c.witness.second xy zy
      (names.symm.trans classes))
  constructor
  · rintro ⟨unique, mem, agrees⟩
    refine ⟨unique, mem, fun s => same_dConnections_iff_same_signature.mpr ⟨skeletonFor mem s, ?_⟩⟩
    intro x y z
    have classifyGround (xy : Adjacent (graph B M s) x y) (zy : Adjacent (graph B M s) z y)
        (distinct : x ≠ z) (xz : ¬ Adjacent (graph B M s) x z) :
        HeadToHead (graph B M s) x y z ↔ HeadToHead (graph B (reorient skeleton order) s) x y z := by
      obtain ⟨r, member, classes | classes⟩ := classified_covers O skeleton included coverage s x y z distinct xy zy xz
      · exact (statusFor s x y z xy zy r member classes).symm.trans
          ((matchesFor s x y z xy zy r classes).mp (agrees r member))
      · have swapped := (statusFor s z y x zy xy r member classes).symm.trans
          ((matchesFor s z y x zy xy r classes).mp (agrees r member))
        exact ⟨fun arrows => And.symm (swapped.mp arrows.symm),
          fun arrows => And.symm (swapped.mpr arrows.symm)⟩
    constructor
    · rintro ⟨distinct, noEdge, arrows⟩
      have compatible := classifyGround (.inl arrows.1) (.inl arrows.2) distinct noEdge
      exact ⟨distinct, fun joined => noEdge ((skeletonFor mem s x z).mpr joined), compatible.mp arrows⟩
    · rintro ⟨distinct, noEdge, arrows⟩
      have xy := (skeletonFor mem s x y).mpr (.inl arrows.1)
      have zy := (skeletonFor mem s z y).mpr (.inl arrows.2)
      have xz := fun joined => noEdge ((skeletonFor mem s x z).mp joined)
      exact ⟨distinct, xz, (classifyGround xy zy distinct xz).mpr arrows⟩
  · rintro ⟨unique, mem, sameQueries⟩
    refine ⟨unique, mem, fun r member => ?_⟩
    obtain ⟨c, _, names, verified⟩ := classified_sound L O skeleton sound member
    let w := c.witness
    have ground := (same_dConnections_iff_same_signature.mp (sameQueries w.skeleton)).2
      w.base w.middle w.other
    have noEdge : ¬ Adjacent (graph B (reorient skeleton order) w.skeleton) w.base w.other :=
      fun joined => w.unshielded ((skeletonFor mem _ _ _).mpr joined)
    have sameHead :
        HeadToHead (graph B M w.skeleton) w.base w.middle w.other ↔
        HeadToHead (graph B (reorient skeleton order) w.skeleton) w.base w.middle w.other :=
      ⟨fun h => (ground.mp ⟨w.distinct, w.unshielded, h⟩).2.2,
        fun h => (ground.mpr ⟨w.distinct, noEdge, h⟩).2.2⟩
    exact (matchesFor _ _ _ _ w.first w.second r names).mpr (verified.trans sameHead)


/-- The delayed-orientation revision of Algorithm 2. Local propagation can
be omitted because the two extension tests recover the compelled arrows. -/
def revisedRpCD {B : Schema A P S} {M : Model A P} (L : PathSemantics B)
    (O : Oracle B M) (initial : List (Dependency A P)) (cuts : List (OrderedCUT B M))
    (attributes : List A) : List (Dependency A P) × (A → A → Bool) :=
  let skeleton := learnedSkeleton L O initial
  let C := classifyConstraints (classAdjacent skeleton) (cutResults O skeleton cuts)
  (skeleton, compelled C attributes)

theorem revisedRpCD_sound_complete {B : Schema A P S} {M : Model A P}
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
        (∀ s, SameDConnections (graph B M s) (graph B (reorient learned.1 order) s)) →
        order.idxOf v < order.idxOf u)) := by
  let skeleton := learnedSkeleton L O initial
  have skeletonClosed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton :=
    search_closed (phaseQuery L O) L.involution initial initialClosed (initial.length + 1)
  have recovered (d : Dependency A P) := phaseOne_ground_exact L O initial initialContains initialClosed initialValid initialLegal d
  have included (q : Dependency A P) (member : q ∈ M.dependencies) :
      q ∈ skeleton := (recovered q).mpr ⟨initialContains q member, .inl (decide_eq_true member)⟩
  have sound (q : Dependency A P) (member : q ∈ skeleton) :
      pairPresent (phaseQuery L O) (trueDependency M) q := ((recovered q).mp member).2
  have different (q : Dependency A P) (member : q ∈ skeleton) :
      q.source ≠ q.target := initialValid q ((recovered q).mp member).1
  refine ⟨fun d => ?_, fun u hu v hv uv => ?_⟩
  · constructor
    · intro mem
      rcases sound d mem with forward | backward
      · exact .inl (of_decide_eq_true forward)
      · exact .inr (of_decide_eq_true backward)
    · rintro (forward | backward)
      · exact included d forward
      · change d ∈ skeleton
        simpa [L.involution] using skeletonClosed (L.reverse d) (included _ backward)
  · let results := cutResults O skeleton cuts
    let C := classifyConstraints (classAdjacent skeleton) results
    have input : ValidInput C := classifyConstraints_valid _ _
      (classAdj_symm L skeletonClosed) (classAdj_loopless different) (by
        intro r member
        obtain ⟨c, _, type, _⟩ := classified_sound L O skeleton sound member
        rw [type]
        exact ⟨class_adjacent_of_ground c.witness.first skeleton included L skeletonClosed,
          class_adjacent_of_ground c.witness.second skeleton included L skeletonClosed⟩)
    change compelled C attributes u v = true ↔ _
    rw [compelled_iff input unique hu hv uv]
    constructor
    · intro forced order sorted members sameQueries
      have consistent := (classified_extensions_ground_iff L O skeleton included skeletonClosed
        sound different coverage attributes order attrLive).mpr ⟨sorted, members, sameQueries⟩
      exact (forced order consistent).2
    · intro forced order consistent
      obtain ⟨sorted, members, sameQueries⟩ :=
        (classified_extensions_ground_iff L O skeleton included skeletonClosed
          sound different coverage attributes order attrLive).mp consistent
      exact ⟨uv, forced order sorted members sameQueries⟩

end RpCD

end
