module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDItemSchema
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDConcretePaths
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDAllModels

@[expose] public section

namespace RpCD.CutSchedule

open Ground CutComplete RelationalPaths

variable {A C V : Type}

private theorem paths_of_length {edge : V → V → Prop} {classOf : V → C}
    {x y : V} {m : Nat} {word : Fin (m+1) → C}
    (realizes : ExactCUT.Realizes edge classOf x y (List.ofFn word)) :
    ∃ positions : Fin (m+1) → V,
      Path edge x y (List.ofFn positions) ∧
      positions 0 = x ∧ positions (Fin.last m) = y ∧
      ∀ i, classOf (positions i) = word i := by
  obtain ⟨items, path, labels⟩ := realizes
  have size : items.length = m+1 := by
    simpa using congrArg List.length labels
  let positions (i : Fin (m+1)) : V := items[i.val]'(by simp [size])
  have itemsEq : List.ofFn positions = items := by
    conv => rhs; rw [← List.ofFn_getElem (xs := items)]
    apply List.ext_getElem
    · simp [size]
    · intro i h k
      simp only [List.getElem_ofFn]
      rfl
  have first : positions 0 = x := by
    have first := (List.getElem?_eq_some_iff.mp (List.head?_eq_getElem? ▸ path.1)).2
    exact first
  have last : positions (Fin.last m) = y := by
    have last := path.2.1
    rw [List.getLast?_eq_getElem?, size] at last
    exact (List.getElem?_eq_some_iff.mp (by simpa using last)).2
  refine ⟨positions, itemsEq ▸ path, first, last, ?_⟩
  intro i
  have h : i.val < (items.map classOf).length := by simp [size]
  simpa only [List.getElem_map, List.getElem_ofFn, positions] using (List.getElem_of_eq labels h)

/-- The two instantiated generating paths supply the constructor's position
maps. The same ground middle is identified before checking shielding. -/
theorem construct_from_realizations [DecidableEq V] [DecidableEq A] [DecidableEq C]
    {schema : CutComplete.Schema C} {m n : Nat} {input : Inputs C A m n}
    {classOf : V → C} {edge : V → V → Prop} {x y z : V}
    (legal : SkeletonLegal schema classOf edge)
    (p : ExactCUT.Realizes edge classOf x y (List.ofFn input.pClass))
    (q : ExactCUT.Realizes edge classOf y z (List.ofFn input.qClass))
    (distinct : distinctVariables x y z input.x input.y input.z)
    (unshielded : ∀ label ∈ input.shields, ¬ ExactCUT.Realizes edge classOf x z label) :
    ∃ out, out ∈ construct schema input := by
  obtain ⟨pItems, pPath, px, py, typedP⟩ := paths_of_length p
  obtain ⟨qItems, qPath, qy, qz, typedQ⟩ := paths_of_length q
  let ground : GroundWitness input classOf edge pItems qItems := {
    pPath := by simpa [px, py] using pPath
    qPath := by simpa [qy, qz] using qPath
    typedP := typedP
    typedQ := typedQ
    sameMiddle := py.trans qy.symm
    distinct := by simpa [px, py, qz] using distinct
    notShielded := by simpa [px, qz] using unshielded }
  obtain ⟨out, member, _⟩ := construct_of_groundWitness legal ground
  exact ⟨out, member⟩


open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open RelationalFiniteSearch

variable [DecidableEq A] [DecidableEq C] {schema : CutComplete.Schema C}

abbrev Dep (A C : Type) := Dependency A (List C)

def shields [DecidableEq A] (skeleton : List (Dep A C)) (x z : A) : List (List C) :=
  ((skeleton.filter fun p => p.target == x && p.source == z).map Dependency.path)

structure Seed (skeleton : List (Dep A C)) where
  p : Dep A C
  q : Dep A C
  pMem : p ∈ skeleton
  qMem : q ∈ skeleton
  pValid : p.path ≠ []
  qValid : q.path ≠ []
  joined : p.source = q.target

def seeds (skeleton : List (Dep A C)) : List (Seed skeleton) :=
  skeleton.attach.flatMap fun p =>
    skeleton.attach.filterMap fun q =>
      if good : p.val.path ≠ [] ∧ q.val.path ≠ [] ∧ p.val.source = q.val.target then
        some ⟨p.val, q.val, p.property, q.property, good.1, good.2.1, good.2.2⟩
      else none

omit [DecidableEq C] in
theorem mem_seeds {skeleton : List (Dep A C)} (s : Seed skeleton) : s ∈ seeds skeleton := by
  apply List.mem_flatMap.mpr
  refine ⟨⟨s.p, s.pMem⟩, List.mem_attach .., List.mem_filterMap.mpr ⟨⟨s.q, s.qMem⟩,
    List.mem_attach .., ?_⟩⟩
  simp [s.pValid, s.qValid, s.joined]

def Seed.m {skeleton : List (Dep A C)} (s : Seed skeleton) := s.p.path.length - 1
def Seed.n {skeleton : List (Dep A C)} (s : Seed skeleton) := s.q.path.length - 1

omit [DecidableEq A] [DecidableEq C] in
private theorem length_first {skeleton : List (Dep A C)} (s : Seed skeleton) :
    s.p.path.length = s.m + 1 := by
  have := List.length_pos_iff.mpr s.pValid
  unfold Seed.m
  omega

omit [DecidableEq A] [DecidableEq C] in
private theorem length_second {skeleton : List (Dep A C)} (s : Seed skeleton) :
    s.q.path.length = s.n + 1 := by
  have := List.length_pos_iff.mpr s.qValid
  unfold Seed.n
  omega

def input {skeleton : List (Dep A C)} (s : Seed skeleton) : Inputs C A s.m s.n where
  pClass i := s.p.path[i.val]'(by rw [length_first s]; exact i.isLt)
  qClass i := s.q.path[i.val]'(by rw [length_second s]; exact i.isLt)
  x := s.p.target
  y := s.p.source
  z := s.q.source
  shields := shields skeleton s.p.target s.q.source

omit [DecidableEq C] in
theorem first_word {skeleton : List (Dep A C)} (s : Seed skeleton) :
    List.ofFn (input s).pClass = s.p.path := by
  conv => rhs; rw [← List.ofFn_getElem (xs := s.p.path)]
  apply List.ext_getElem
  · simpa using (length_first s).symm
  · intro idx h k
    simp only [List.getElem_ofFn]
    rfl

omit [DecidableEq C] in
theorem second_word {skeleton : List (Dep A C)} (s : Seed skeleton) :
    List.ofFn (input s).qClass = s.q.path := by
  conv => rhs; rw [← List.ofFn_getElem (xs := s.q.path)]
  apply List.ext_getElem
  · simpa using (length_second s).symm
  · intro idx h k
    simp only [List.getElem_ofFn]
    rfl

omit [DecidableEq C] in
theorem label_endpoint_classes {V : Type} {edge : V → V → Prop} {cls : V → C}
    {a b : V} {label : List C} (r : ExactCUT.Realizes edge cls a b label) :
    label.head? = some (cls a) ∧ label.getLast? = some (cls b) := by
  obtain ⟨items, path, rfl⟩ := r
  exact ⟨by simp [path.1], by simp [path.2.1]⟩

def Typed (vocab : AttributeSchema C A) (p : Dep A C) : Prop :=
  p.path.head? = some (vocab.attributeClass p.target) ∧
  p.path.getLast? = some (vocab.attributeClass p.source)

theorem typed_of_ground {vocab : AttributeSchema C A} {s : ItemSkeleton schema}
    {p : Dep A C} {x z : Fin (variables vocab s).length} (r : groundRealizes vocab s p x z = true) :
    Typed vocab p := by
  obtain ⟨a, b, path⟩ := groundRealizes_spec.mp r
  obtain ⟨start, finish⟩ := label_endpoint_classes path
  rw [← variableAt_type vocab s x, a] at start
  rw [← variableAt_type vocab s z, b] at finish
  exact ⟨start, finish⟩


omit [DecidableEq C] in
theorem wholeWord {edge : V → V → Prop} {classOf : V → C} {n : Nat}
    {positions : Fin (n+1) → V} {word : Fin (n+1) → C}
    (path : Path edge (positions 0) (positions (Fin.last n)) (List.ofFn positions))
    (typed : ∀ i, classOf (positions i) = word i) :
    ExactCUT.Realizes edge classOf (positions 0) (positions (Fin.last n)) (List.ofFn word) := by
  refine ⟨_, path, ?_⟩
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext typed)

omit [DecidableEq C] in
theorem singleton_endpoints {edge : V → V → Prop} {classOf : V → C} {x z : V}
    {c : C} (r : ExactCUT.Realizes edge classOf x z [c]) : x = z := by
  obtain ⟨items, path, labels⟩ := r
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp path.1
  cases rest with
  | nil => exact Option.some.inj path.2.1
  | cons => simp at labels

/-- Each result of the exact CUT constructor, paired with the two input
dependencies, is reindexed as a ground witness in the learner's graph. -/
def compileCut (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (L : PathSemantics (groundSchema schema vocab)) (skeleton : List (Dep A C))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (typed : ∀ q ∈ skeleton, Typed vocab q)
    (s : Seed skeleton) (out : Result C s.m) (found : out ∈ construct schema (input s)) :
    {c : OrderedCUT (groundSchema schema vocab) M //
      c.witness.triple = ⟨s.p.target, s.p.source, s.q.source⟩ ∧
      ∀ g x z, (groundSchema schema vocab).realizes g c.query x z = true → x ≠ z} := by
  let I := input s
  let cls := coreClass I.pClass I.qClass (code := out.code) (n := s.n+1)
  let oldEdge := coreEdge out.code (s.n+1)
  let V := Completed schema cls oldEdge
  let edge := completionEdge schema cls oldEdge
  let classes := completionClass schema cls oldEdge
  let rawX : V := .inl (pSlot out.code 0)
  let rawY : V := .inl (pSlot out.code (Fin.last s.m))
  let rawZ : V := .inl (qSlot out.code (Fin.last s.n))
  have proof := construct_sound found
  let legal : SkeletonLegal schema classes edge := proof.1
  let w := proof.2.1
  let items := completionItems schema cls oldEdge (coreItems out.code (s.n+1)) mem_coreItems
  let covers : ∀ v : V, v ∈ items := mem_completionItems mem_coreItems
  let g := pack items covers classes edge legal
  let idx (v : V) : Fin g.size := packedIndex items covers v
  have idxSpec (v : V) : packItem items (idx v) = v := packItem_index items covers v
  have pLabel : ExactCUT.Realizes edge classes rawX rawY s.p.path := by
    rw [← first_word s]
    exact wholeWord w.pPath w.typedP
  have qLabel : ExactCUT.Realizes edge classes rawY rawZ s.q.path := by
    rw [← second_word s]
    have qReal := wholeWord w.qPath w.typedQ
    rw [← w.sameMiddle] at qReal
    exact qReal
  have rLabel : ExactCUT.Realizes edge classes rawX rawZ out.endpoint := proof.2.2.2
  have xTyped : vocab.attributeClass s.p.target = classes rawX :=
    Option.some.inj ((typed s.p s.pMem).1.symm.trans (label_endpoint_classes pLabel).1)
  have yTyped : vocab.attributeClass s.p.source = classes rawY :=
    Option.some.inj ((typed s.p s.pMem).2.symm.trans (label_endpoint_classes pLabel).2)
  have zTyped : vocab.attributeClass s.q.source = classes rawZ :=
    Option.some.inj ((typed s.q s.qMem).2.symm.trans (label_endpoint_classes qLabel).2)
  let vertex (v : V) (a : A) (typed : vocab.attributeClass a = classes v) :
      Fin (variables vocab g).length :=
    variableIndex vocab g (idx v) a (by change vocab.attributeClass a = classes (packItem items (idx v)); rw [idxSpec]; exact typed)
  have vertexSpec (v : V) (a : A) (typed : vocab.attributeClass a = classes v) :
      variableAt vocab g (vertex v a typed) = (idx v, a) := variableAt_index ..
  let x := vertex rawX s.p.target xTyped
  let y := vertex rawY s.p.source yTyped
  let z := vertex rawZ s.q.source zTyped
  have xs : variableAt vocab g x = (idx rawX, s.p.target) := vertexSpec rawX s.p.target xTyped
  have ys : variableAt vocab g y = (idx rawY, s.p.source) := vertexSpec rawY s.p.source yTyped
  have zs : variableAt vocab g z = (idx rawZ, s.q.source) := vertexSpec rawZ s.q.source zTyped
  let r : Dep A C := ⟨s.q.source, s.p.target, out.endpoint⟩
  have pHit : groundRealizes vocab g s.p x y = true := by
    apply groundRealizes_spec.mpr
    rw [xs, ys]
    exact ⟨rfl, rfl, pack_realizes_iff.mpr (by simpa [idxSpec] using pLabel)⟩
  have qHit : groundRealizes vocab g s.q y z = true := by
    apply groundRealizes_spec.mpr
    rw [ys, zs]
    exact ⟨s.joined, rfl, pack_realizes_iff.mpr (by simpa [idxSpec] using qLabel)⟩
  have rHit : groundRealizes vocab g r x z = true := by
    apply groundRealizes_spec.mpr
    rw [xs, zs]
    exact ⟨rfl, rfl, pack_realizes_iff.mpr (by simpa [idxSpec] using rLabel)⟩
  have distinct : x ≠ z := by
    intro same
    have endpoints := congrArg (variableAt vocab g) same
    rw [xs, zs] at endpoints
    have raw := congrArg (fun p : Fin g.size × A => (packItem items p.1, p.2)) endpoints
    apply w.distinct.2.2
    change (rawX, s.p.target) = (rawZ, s.q.source)
    simpa only [Prod.mk.injEq, idxSpec] using raw
  have unshielded : ¬ Adjacent (graph (groundSchema schema vocab) M g) x z := by
    intro shielded
    obtain ⟨q, member, hit⟩ := lift_ground_adjacent (Or.symm shielded) skeleton included L closed
    obtain ⟨hX, hZ, label⟩ := groundRealizes_spec.mp hit
    rw [xs] at hX
    rw [zs] at hZ
    rw [xs, zs] at label
    have allowed : q.path ∈ I.shields := by
      change q.path ∈ shields skeleton s.p.target s.q.source
      have first : s.p.target = q.target := hX
      have last : s.q.source = q.source := hZ
      exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨member, by simp [← first, ← last]⟩, rfl⟩
    exact w.notShielded q.path allowed (by simpa [idxSpec] using pack_realizes_iff.mp label)
  let c : OrderedCUT (groundSchema schema vocab) M :=
    ⟨r, ⟨g, x, y, z, rHit, distinct,
      adjacent_of_surviving L O (sound s.p s.pMem) pHit,
      Or.symm (adjacent_of_surviving L O (sound s.q s.qMem) qHit), unshielded⟩⟩
  refine ⟨c, ?_, ?_⟩
  · change Triple.mk (variableAt vocab g x).2 (variableAt vocab g y).2 (variableAt vocab g z).2 = _
    rw [xs, ys, zs]
  · intro other u v hit same
    subst v
    obtain ⟨atTarget, atSource, sameItem⟩ := groundRealizes_spec.mp hit
    have endpoints : s.p.target = s.q.source := atTarget.symm.trans atSource
    have singleton := sameItem_realizes_iff.mp sameItem
    change out.endpoint = _ at singleton
    rw [singleton] at rLabel
    have only := singleton_endpoints rLabel
    apply w.distinct.2.2
    change (rawX, s.p.target) = (rawZ, s.q.source)
    exact Prod.ext only endpoints


def enumerateCuts (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (L : PathSemantics (groundSchema schema vocab)) (skeleton : List (Dep A C))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (typed : ∀ q ∈ skeleton, Typed vocab q) :
    List (OrderedCUT (groundSchema schema vocab) M) :=
  (seeds skeleton).flatMap fun s => (construct schema (input s)).attach.map fun out =>
    (compileCut vocab O L skeleton included closed sound typed s out.val out.property).val

theorem exact_cut_coverage (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (L : PathSemantics (groundSchema schema vocab)) (skeleton : List (Dep A C))
    (included : ∀ q ∈ M.dependencies, q ∈ skeleton)
    (closed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton)
    (sound : ∀ q ∈ skeleton, pairPresent (phaseQuery L O) (trueDependency M) q)
    (typed : ∀ q ∈ skeleton, Typed vocab q) :
    CUTCoverage (enumerateCuts vocab O L skeleton included closed sound typed) where
  distinct := by
    intro c member
    obtain ⟨s, _, mem⟩ := List.mem_flatMap.mp member
    obtain ⟨out, _, equal⟩ := List.mem_map.mp mem
    rw [← equal]
    exact (compileCut vocab O L skeleton included closed sound typed s out.val out.property).property.2
  forward := by
    intro g x y z xz xy zy unshielded
    obtain ⟨p, pMem, pHit⟩ := lift_ground_adjacent (Or.symm xy) skeleton included L closed
    obtain ⟨q, qMem, qHit⟩ := lift_ground_adjacent zy skeleton included L closed
    obtain ⟨atX, atY, pPath⟩ := groundRealizes_spec.mp pHit
    obtain ⟨atY', atZ, qPath⟩ := groundRealizes_spec.mp qHit
    have pValid : p.path ≠ [] := by
      have present := (typed p pMem).1
      rintro empty
      simp [empty] at present
    have qValid : q.path ≠ [] := by
      have present := (typed q qMem).1
      rintro empty
      simp [empty] at present
    let s : Seed skeleton := ⟨p, q, pMem, qMem, pValid, qValid, atY.symm.trans atY'⟩
    have different {a b : Fin (variables vocab g).length}
        (join : Adjacent (graph (groundSchema schema vocab) M g) a b) : a ≠ b := by
      rintro rfl
      rcases join with self | self
      all_goals exact (graph (groundSchema schema vocab) M g).no_directed_cycle _ (.single self)
    have distinct :
        distinctVariables (variableAt vocab g x).1 (variableAt vocab g y).1 (variableAt vocab g z).1
          (input s).x (input s).y (input s).z := by
      change distinctVariables (variableAt vocab g x).1 (variableAt vocab g y).1 (variableAt vocab g z).1
        p.target p.source q.source
      rw [← atX, ← atY, ← atZ]
      exact ⟨fun same => different xy (variableAt_injective same),
        fun same => (different zy).symm (variableAt_injective same),
        fun same => xz (variableAt_injective same)⟩
    have noShields : ∀ label ∈ (input s).shields, ¬ ExactCUT.Realizes g.edge g.itemClass
        (variableAt vocab g x).1 (variableAt vocab g z).1 label := by
      intro label labeled realized
      change label ∈ shields skeleton p.target q.source at labeled
      obtain ⟨d, listed, hd⟩ := List.mem_map.mp labeled
      obtain ⟨member, test⟩ := List.mem_filter.mp listed
      obtain ⟨src, dst⟩ := Bool.and_eq_true_iff.mp test
      have also : groundRealizes vocab g d x z = true := groundRealizes_spec.mpr
        ⟨atX.trans (eq_of_beq src).symm, atZ.trans (eq_of_beq dst).symm, hd.symm ▸ realized⟩
      exact unshielded (adjacent_of_surviving L O (sound d member) also)
    obtain ⟨out, found⟩ := construct_from_realizations (input := input s) g.legal (by rwa [first_word])
      (by rwa [second_word]) distinct noShields
    let verified := compileCut vocab O L skeleton included closed sound typed s out found
    refine ⟨verified.val, List.mem_flatMap.mpr ⟨s, mem_seeds s, ?_⟩, ?_⟩
    · exact List.mem_map.mpr ⟨⟨out, found⟩, List.mem_attach .., rfl⟩
    · rw [verified.property.1]
      change Triple.mk p.target p.source q.source =
        Triple.mk (variableAt vocab g x).2 (variableAt vocab g y).2 (variableAt vocab g z).2
      rw [atX, atY, atZ]


/-- The search takes the dependency candidates at the supplied hop bound.
    Coverage is proved for the CUTs it actually computes from Phase I. -/
def verifiedCuts (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (initial : List (Dep A C))
    (contains : ∀ q ∈ M.dependencies, q ∈ initial)
    (closed : PairClosed (phaseQuery (concretePathSemantics schema vocab) O) initial)
    (proper : ∀ q ∈ initial, q.source ≠ q.target)
    (legal : ∀ q ∈ initial, dependencyValid schema vocab q) :
    {cuts : List (OrderedCUT (groundSchema schema vocab) M) // CUTCoverage cuts} := by
  let L := concretePathSemantics schema vocab
  let skeleton := learnedSkeleton L O initial
  have exactSkeleton (q : Dep A C) := phaseOne_ground_exact L O initial contains closed proper legal q
  have included (q : Dep A C) (member : q ∈ M.dependencies) :
      q ∈ skeleton := (exactSkeleton q).mpr ⟨contains q member, Or.inl (decide_eq_true member)⟩
  have revClosed : ∀ q ∈ skeleton, L.reverse q ∈ skeleton :=
    search_closed (phaseQuery L O) L.involution initial closed (initial.length + 1)
  have sound (q : Dep A C) (member : q ∈ skeleton) :=
    ((exactSkeleton q).mp member).2
  have typed (q : Dep A C) (member : q ∈ skeleton) : Typed vocab q := by
    obtain ⟨s, x, z, hit⟩ := legal q ((exactSkeleton q).mp member).1
    exact typed_of_ground hit
  exact ⟨enumerateCuts vocab O L skeleton included revClosed sound typed,
    exact_cut_coverage vocab O L skeleton included revClosed sound typed⟩

def correctedRpCD (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (initial : List (Dep A C))
    (contains : ∀ q ∈ M.dependencies, q ∈ initial)
    (closed : PairClosed (phaseQuery (concretePathSemantics schema vocab) O) initial)
    (proper : ∀ q ∈ initial, q.source ≠ q.target)
    (legal : ∀ q ∈ initial, dependencyValid schema vocab q) :
    List (Dep A C) × (A → A → Bool) :=
  let cuts := verifiedCuts vocab O initial contains closed proper legal
  revisedRpCD (concretePathSemantics schema vocab) O initial cuts.val vocab.attributes

theorem correctedRpCD_correct (vocab : AttributeSchema C A)
    {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (initial : List (Dep A C))
    (contains : ∀ q ∈ M.dependencies, q ∈ initial)
    (closed : PairClosed (phaseQuery (concretePathSemantics schema vocab) O) initial)
    (proper : ∀ q ∈ initial, q.source ≠ q.target)
    (legal : ∀ q ∈ initial, dependencyValid schema vocab q)
    (nodup : vocab.attributes.Nodup) :
    let result := correctedRpCD vocab O initial contains closed proper legal
    (∀ d, d ∈ result.1 ↔ d ∈ M.dependencies ∨ reverseDependency d ∈ M.dependencies) ∧
    (∀ u v, classAdjacent result.1 u v = true →
      (result.2 u v = true ↔ ∀ N : Model A (List C), (∀ q ∈ N.dependencies, q ∈ initial) →
        SameRelCI (groundSchema schema vocab) M N → N.classArrow u v)) := by
  let L := concretePathSemantics schema vocab
  let cuts := verifiedCuts vocab O initial contains closed proper legal
  have correctness := revisedRpCD_allModels_correct L O initial contains closed proper legal
    cuts.property vocab.attributes nodup (fun _ _ => vocab.covers _)
  exact ⟨correctness.1, fun u v edge => correctness.2 u (vocab.covers u) v (vocab.covers v) edge⟩

end RpCD.CutSchedule

end
