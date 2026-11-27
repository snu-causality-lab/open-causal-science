module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDLight
public import OpenCausalScience.Discovery.RelationalFiniteSearch

/-! Lee–Honavar (AAAI 2016), Algorithm 1. The statements below distinguish
the finite learner from the assumptions relating its oracle to ground graphs. -/

@[expose] public section

namespace RCDLight.Learning

abbrev Variable (K A : Type) := List K × A

structure Dependency (K A : Type) where
  path : List K
  cause : A
  effect : A
  deriving DecidableEq

variable {K A : Type} [DecidableEq K] [DecidableEq A]

def Dependency.reverse (d : Dependency K A) : Dependency K A :=
  ⟨d.path.reverse, d.effect, d.cause⟩

omit [DecidableEq K] [DecidableEq A] in
theorem Dependency.reverse_reverse (d : Dependency K A) : d.reverse.reverse = d := by
  cases d
  simp [Dependency.reverse]

def Dependency.source (d : Dependency K A) : Variable K A :=
  (d.path, d.cause)

def canonical (itemClass : A → K) (a : A) : Variable K A :=
  ([itemClass a], a)

structure Model (K A : Type) where
  itemClass : A → K
  validPath : List K → Prop
  trueDependency : Dependency K A → Bool
  independent : Variable K A → Variable K A → List (Variable K A) → Bool

def Model.query (m : Model K A) :
    RelationalFiniteSearch.Query (Dependency K A) (Variable K A) where
  source := Dependency.source
  target := fun d => canonical m.itemClass d.effect
  reverse := Dependency.reverse
  independent := fun d => m.independent d.source (canonical m.itemClass d.effect)

def Model.classArrow (m : Model K A) (a b : A) : Prop :=
  ∃ path, m.trueDependency ⟨path, a, b⟩ = true

/-- Nonempty directed reachability in the attribute-class graph. -/
inductive Reach (edge : A → A → Prop) : A → A → Prop
  | single {a b} : edge a b → Reach edge a b
  | extend {a b c} : Reach edge a b → edge b c → Reach edge a c

omit [DecidableEq A] in
theorem Reach.trans {edge : A → A → Prop} {a b c : A}
    (left : Reach edge a b) (right : Reach edge b c) : Reach edge a c := by
  induction right with
  | single bc => exact .extend left bc
  | extend _ cd ih => exact .extend ih cd

omit [DecidableEq A] in
theorem Reach.mono {e f : A → A → Prop} {a b : A}
    (le : ∀ x y, e x y → f x y) (path : Reach e a b) : Reach f a b := by
  induction path with
  | single h => exact .single (le _ _ h)
  | extend _ edge ih => exact .extend ih (le _ _ edge)

def Model.acyclic (m : Model K A) : Prop :=
  ∀ a, ¬ Reach m.classArrow a a

def Model.classAdjacent (m : Model K A) (a b : A) : Prop :=
  m.classArrow a b ∨ m.classArrow b a

def Model.unrolled (m : Model K A) (u v : Variable K A) : Prop :=
  m.validPath u.1 ∧ ∃ path : List K, m.trueDependency ⟨path, u.2, v.2⟩ = true ∧
    ∃ pivot, Pivot v.1.reverse path pivot ∧ joinAt v.1 path pivot = u.1

def Model.unrolledAdjacent (m : Model K A) (u v : Variable K A) : Prop :=
  m.unrolled u v ∨ m.unrolled v u

omit [DecidableEq K] [DecidableEq A] in
theorem Model.unrolled_has_class_arrow (m : Model K A) {u v : Variable K A}
    (h : m.unrolled u v) : m.classArrow u.2 v.2 := by
  obtain ⟨_, path, trueD, _⟩ := h
  exact ⟨path, trueD⟩

section Adjacency

open RelationalFiniteSearch

def Model.trueParents (m : Model K A) (initial : List (Dependency K A)) (target : A) :
    List (Variable K A) :=
  (initial.filter fun d => decide (d.effect = target) && m.trueDependency d).map
    Dependency.source

/-- Lemma 1 specialized to both canonical queries of an undirected dependency. -/
def AdjacencyFaithful (m : Model K A) : Prop :=
  ∀ d, pairPresent m.query m.trueDependency d → ∀ C,
    d.source ∉ C → canonical m.itemClass d.effect ∉ C →
    m.independent d.source (canonical m.itemClass d.effect) C = false

/-- The separating direction of Proposition 1 for ground-graph CI with a
canonical endpoint. Initial enumeration determines the list of true parents. -/
def CanonicalParentSeparation (m : Model K A) (initial : List (Dependency K A)) : Prop :=
  ∀ d : Dependency K A,
    d.source ≠ canonical m.itemClass d.effect →
    ¬ pairPresent m.query m.trueDependency d →
    ¬ Reach m.classArrow d.effect d.cause →
    m.independent d.source (canonical m.itemClass d.effect) (m.trueParents initial d.effect) = true

private theorem trueParents_eq (m : Model K A) (initial : List (Dependency K A))
    {d : Dependency K A} (missing : ¬ pairPresent m.query m.trueDependency d) :
    (trueParentCandidates m.query m.trueDependency initial d).map m.query.source =
      m.trueParents initial d.effect := by
  unfold trueParentCandidates Model.trueParents
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c _
  have noSelf : c.effect = d.effect → c.source = d.source → m.trueDependency c = false := by
    intro sameEffect sameSource
    have same : c = d := by
      cases c
      cases d
      simp_all [Dependency.source]
    subst c
    exact Bool.eq_false_iff.mpr (fun trueD => missing (.inl trueD))
  cases ht : m.trueDependency c with
  | false => simp
  | true =>
    by_cases sameEffect : c.effect = d.effect
    · have differentSource : c.source ≠ d.source := by
        intro sameSource
        rw [ht] at noSelf
        exact Bool.noConfusion (noSelf sameEffect sameSource)
      simp [eligible, Model.query, canonical, sameEffect, differentSource]
    · simp [eligible, Model.query, canonical, sameEffect]

theorem both_perspectives_parent_separator (m : Model K A) (initial : List (Dependency K A))
    (acyclic : m.acyclic) (parentSeparation : CanonicalParentSeparation m initial)
    {d : Dependency K A} (forwardDistinct : d.source ≠ canonical m.itemClass d.effect)
    (backwardDistinct : d.reverse.source ≠ canonical m.itemClass d.reverse.effect)
    (missing : ¬ pairPresent m.query m.trueDependency d) :
    m.query.independent d
        ((trueParentCandidates m.query m.trueDependency initial d).map m.query.source) = true ∨
      m.query.independent d.reverse
        ((trueParentCandidates m.query m.trueDependency initial d.reverse).map
          m.query.source) = true := by
  have noReverse : ¬ pairPresent m.query m.trueDependency d.reverse := by
    intro present
    exact missing (present.elim (fun trueR => .inr trueR)
      (fun trueD => .inl (by simpa [Model.query, Dependency.reverse_reverse] using trueD)))
  rw [trueParents_eq m initial missing, trueParents_eq m initial noReverse]
  by_cases targetAnc : Reach m.classArrow d.effect d.cause
  · have sourceNotAnc : ¬ Reach m.classArrow d.reverse.effect d.reverse.cause :=
      fun path => acyclic d.effect (targetAnc.trans path)
    exact .inr (parentSeparation _ backwardDistinct noReverse sourceNotAnc)
  · exact .inl (parentSeparation _ forwardDistinct missing targetAnc)

def adjacencyPhase (m : Model K A) (initial : List (Dependency K A)) :
    List (Dependency K A) :=
  phaseOne m.query initial

/-- Algorithm 1 lines 1–8 recover exactly both orientations of each
enumerated true undirected dependency. -/
theorem adjacency_phase_exact (m : Model K A) (initial : List (Dependency K A))
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (faithful : AdjacencyFaithful m) (parentSeparation : CanonicalParentSeparation m initial)
    (d : Dependency K A) :
    d ∈ adjacencyPhase m initial ↔ d ∈ initial ∧ pairPresent m.query m.trueDependency d :=
  phaseOne_exact m.query m.trueDependency initial Dependency.reverse_reverse reverseClosed proper
    faithful (fun c mem => both_perspectives_parent_separator m initial acyclic parentSeparation
      (proper c mem) (proper c.reverse (reverseClosed c mem))) d

end Adjacency

section Orientation

open RelationalFiniteSearch

structure Triple (K A : Type) where
  leftAttribute : A
  middle : Variable K A
  right : Variable K A
  deriving DecidableEq

def Triple.left (m : Model K A) (t : Triple K A) : Variable K A :=
  canonical m.itemClass t.leftAttribute

def Triple.endpointDependency (t : Triple K A) : Dependency K A :=
  ⟨t.right.1, t.right.2, t.leftAttribute⟩

/-- A representative triple has a canonical left variable. Its endpoints
are different variables even in the repeated-attribute RBO case. -/
structure Representative (m : Model K A) (t : Triple K A) : Prop where
  leftRightDistinct : t.left m ≠ t.right
  leftArm : m.unrolledAdjacent (t.left m) t.middle
  rightArm : m.unrolledAdjacent t.middle t.right
  unshielded : ¬ m.unrolledAdjacent (t.left m) t.right
  rightValid : m.validPath t.right.1
  rightBase : t.right.1.head? = some (m.itemClass t.leftAttribute)
  middleValid : m.validPath t.middle.1
  canonicalValid : m.validPath (t.left m).1

def Triple.collider (m : Model K A) (t : Triple K A) : Prop :=
  m.unrolled (t.left m) t.middle ∧ m.unrolled t.right t.middle

def Triple.classCollider (m : Model K A) (t : Triple K A) : Prop :=
  m.classArrow t.leftAttribute t.middle.2 ∧ m.classArrow t.right.2 t.middle.2

/-- Lemma 2 restricted to representative triples. The canonical endpoint
makes the two distinct flanking relational variables nonintersectable. -/
def OrientationFaithful (m : Model K A) : Prop :=
  ∀ t, Representative m t → ∀ conditions, t.left m ∉ conditions → t.right ∉ conditions →
    ((t.collider m ∧ t.middle ∈ conditions) ∨
      (¬ t.collider m ∧ t.middle ∉ conditions)) →
    m.independent (t.left m) t.right conditions = false

def SymmetricOracle (m : Model K A) : Prop :=
  ∀ u v conditions, u ≠ v → u ∉ conditions → v ∉ conditions →
    m.independent u v conditions = m.independent v u conditions

omit [DecidableEq K] [DecidableEq A] in
private theorem Representative.classes_adjacent {m : Model K A} {t : Triple K A}
    (rep : Representative m t) :
    m.classAdjacent t.leftAttribute t.middle.2 ∧ m.classAdjacent t.middle.2 t.right.2 := by
  exact ⟨rep.leftArm.imp (m.unrolled_has_class_arrow) (m.unrolled_has_class_arrow),
    rep.rightArm.imp (m.unrolled_has_class_arrow) (m.unrolled_has_class_arrow)⟩

omit [DecidableEq K] [DecidableEq A] in
private theorem Representative.class_collider_iff {m : Model K A} {t : Triple K A}
    (rep : Representative m t) (acyclic : m.acyclic) : t.classCollider m ↔ t.collider m := by
  constructor
  · rintro ⟨left, right⟩
    have orient {u v : Variable K A} (adj : m.unrolledAdjacent u v)
        (forward : m.classArrow u.2 v.2) : m.unrolled u v :=
      adj.elim id (fun back => (acyclic u.2
        (.extend (.single forward) (m.unrolled_has_class_arrow back))).elim)
    exact ⟨orient rep.leftArm left, orient rep.rightArm.symm right⟩
  · rintro ⟨left, right⟩
    exact ⟨m.unrolled_has_class_arrow left, m.unrolled_has_class_arrow right⟩

omit [DecidableEq K] [DecidableEq A] in
private theorem Representative.endpoint_pair_absent {m : Model K A} {t : Triple K A}
    (rep : Representative m t) :
    ¬ pairPresent m.query m.trueDependency t.endpointDependency := by
  intro paired
  have head := rep.rightBase
  obtain ⟨tail, rightWord⟩ := List.head?_eq_some_iff.mp head
  rcases paired with direct | reverse
  · apply rep.unshielded
    exact .inr ⟨rep.rightValid, t.right.1, direct, 1,
      by simp [Triple.left, canonical, rightWord, Pivot],
      by simp [Triple.left, canonical, joinAt]⟩
  · apply rep.unshielded
    refine .inl ⟨rep.canonicalValid, t.right.1.reverse, reverse, t.right.1.length, ?_, ?_⟩
    · simp [Pivot, rightWord]
    · simp [joinAt, rightWord, Triple.left, canonical]

structure ClassFacts (A : Type) where
  directed : A → A → Prop
  ancestor : A → A → Prop
  noncollider : A → A → A → Prop

def ClassFacts.sound (m : Model K A) (facts : ClassFacts A) : Prop :=
  (∀ a b, facts.directed a b → m.classArrow a b) ∧
  (∀ a b, facts.ancestor a b → Reach m.classArrow a b) ∧
  (∀ a b c, facts.noncollider a b c → ¬ (m.classArrow a b ∧ m.classArrow c b))

def ClassFacts.addArrow (facts : ClassFacts A) (a b : A) : ClassFacts A :=
  { facts with directed := fun x y => facts.directed x y ∨ x = a ∧ y = b }

omit [DecidableEq K] [DecidableEq A] in
private theorem ClassFacts.addArrow_sound {m : Model K A} {facts : ClassFacts A} {a b : A}
    (prior : facts.sound m) (edge : m.classArrow a b) : (facts.addArrow a b).sound m := by
  refine ⟨?_, prior.2⟩
  rintro x y (known | ⟨rfl, rfl⟩)
  · exact prior.1 x y known
  · exact edge

def ClassFacts.addAncestor (facts : ClassFacts A) (a b : A) : ClassFacts A :=
  { facts with ancestor := fun x y => facts.ancestor x y ∨ x = a ∧ y = b }

omit [DecidableEq K] [DecidableEq A] in
private theorem ClassFacts.addAncestor_sound {m : Model K A} {facts : ClassFacts A} {a b : A}
    (prior : facts.sound m) (path : Reach m.classArrow a b) :
    (facts.addAncestor a b).sound m := by
  refine ⟨prior.1, ?_, prior.2.2⟩
  rintro x y (known | ⟨rfl, rfl⟩)
  · exact prior.2.1 x y known
  · exact path

def ClassFacts.addNoncollider (facts : ClassFacts A) (a b c : A) : ClassFacts A :=
  { facts with noncollider := fun x y z => facts.noncollider x y z ∨
      x = a ∧ y = b ∧ z = c ∨ x = c ∧ y = b ∧ z = a }

omit [DecidableEq K] [DecidableEq A] in
private theorem ClassFacts.addNoncollider_sound {m : Model K A} {facts : ClassFacts A} {a b c : A}
    (prior : facts.sound m) (noncollider : ¬ (m.classArrow a b ∧ m.classArrow c b)) :
    (facts.addNoncollider a b c).sound m := by
  refine ⟨prior.1, prior.2.1, ?_⟩
  rintro x y z (known | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
  · exact prior.2.2 x y z known
  · exact noncollider
  · exact noncollider ∘ And.symm

def ClassFacts.oriented (facts : ClassFacts A) (a b : A) : Prop :=
  facts.directed a b ∨ facts.directed b a

def ClassFacts.skipTriple (facts : ClassFacts A) (t : Triple K A) : Prop :=
  let x := t.leftAttribute
  let y := t.middle.2
  let z := t.right.2
  Reach (fun a b => facts.directed a b ∨ facts.ancestor a b) x z ∨
    (facts.oriented x y ∧ facts.oriented y z) ∨
    facts.noncollider x y z ∨ facts.directed y x ∨ facts.directed y z

/-- An available parent is a retained candidate approaching the canonical
endpoint. An already directed class arrow away from it excludes that
candidate. The endpoints themselves cannot be conditioned on. -/
noncomputable def availableParents (m : Model K A) (candidates : List (Dependency K A))
    (facts : ClassFacts A) (t : Triple K A) : List (Dependency K A) :=
  open Classical in
  candidates.filter fun d => decide (d.effect = t.leftAttribute ∧ d.source ≠ t.left m ∧
    d.source ≠ t.right ∧ ¬ facts.directed t.leftAttribute d.cause)

noncomputable def firstSeparator (m : Model K A) (candidates : List (Dependency K A))
    (facts : ClassFacts A) (t : Triple K A) : Option (List (Dependency K A)) :=
  (conditioningLists (availableParents m candidates facts t)).find?
    fun ds => m.independent (t.left m) t.right (ds.map Dependency.source)

/-- Algorithm 1 lines 12–19. A failed parent-set search records ancestry.
Only the collider and RBO branches insert direct class orientations. -/
noncomputable def orientTriple (m : Model K A) (candidates : List (Dependency K A))
    (facts : ClassFacts A) (t : Triple K A) : ClassFacts A :=
  open Classical in
  let x := t.leftAttribute
  let y := t.middle.2
  let z := t.right.2
  if facts.skipTriple t then facts else
    match firstSeparator m candidates facts t with
    | none => facts.addAncestor x z
    | some ds =>
      if t.middle ∉ ds.map Dependency.source then (facts.addArrow x y).addArrow z y
      else if x = z then facts.addArrow y x
      else facts.addNoncollider x y z

private theorem available_contains_true_parents {m : Model K A}
    {initial candidates : List (Dependency K A)} {facts : ClassFacts A} {t : Triple K A}
    (rep : Representative m t) (acyclic : m.acyclic) (sound : facts.sound m)
    (proper : ∀ c ∈ initial, c.source ≠ canonical m.itemClass c.effect)
    (retainedElts : candidates.Sublist initial)
    (keeps : candidates.filter m.trueDependency = initial.filter m.trueDependency) :
    (initial.filter fun d => decide (d.effect = t.leftAttribute) && m.trueDependency d).Sublist
      (availableParents m candidates facts t) := by
  classical
  let p : Dependency K A → Bool := fun d => decide (d.effect = t.leftAttribute)
  have reorder : (initial.filter fun d => p d && m.trueDependency d) =
      (candidates.filter fun d => p d && m.trueDependency d) := by
    simp only [← List.filter_filter, keeps]
  rw [reorder]
  have combine : (candidates.filter fun d => p d && m.trueDependency d) =
      (availableParents m candidates facts t).filter (fun d => p d && m.trueDependency d) := by
    rw [availableParents, List.filter_filter]
    apply List.filter_congr
    intro d mem
    by_cases keep : (p d && m.trueDependency d) = true
    · obtain ⟨eq, trueD⟩ := Bool.and_eq_true_iff.mp keep
      have effects : d.effect = t.leftAttribute := of_decide_eq_true eq
      have leftOut : d.source ≠ t.left m := by
        rw [Triple.left, ← effects]
        exact proper d (retainedElts.subset mem)
      have rightOut : d.source ≠ t.right := by
        intro equal
        have same : d = t.endpointDependency := by
          cases d
          simp_all [Dependency.source, Triple.endpointDependency, Prod.ext_iff]
        subst d
        exact rep.endpoint_pair_absent (.inl trueD)
      have toward : m.classArrow d.cause t.leftAttribute :=
        ⟨d.path, by cases d; simp_all⟩
      have notAway : ¬ facts.directed t.leftAttribute d.cause :=
        fun away => acyclic d.cause (.extend (.single toward) (sound.1 _ _ away))
      simp [p, effects, leftOut, rightOut, notAway]
    · change (p d && m.trueDependency d) = ((p d && m.trueDependency d) && _)
      rw [Bool.eq_false_iff.mpr keep]
      rfl
  rw [combine]
  exact List.filter_sublist

private theorem available_parent_endpoints_excluded {m : Model K A}
    {candidates : List (Dependency K A)} {facts : ClassFacts A} {t : Triple K A}
    {ds : List (Dependency K A)} (sub : ds.Sublist (availableParents m candidates facts t)) :
    t.left m ∉ ds.map Dependency.source ∧ t.right ∉ ds.map Dependency.source := by
  classical
  have excluded (d : Dependency K A) (mem : d ∈ ds) :
      d.source ≠ t.left m ∧ d.source ≠ t.right := by
    have pass := (List.mem_filter.mp (sub.subset mem)).2
    exact ⟨(of_decide_eq_true pass).2.1, (of_decide_eq_true pass).2.2.1⟩
  constructor <;> intro endpoint
  · obtain ⟨d, mem, eq⟩ := List.mem_map.mp endpoint
    exact (excluded d mem).1 eq
  · obtain ⟨d, mem, eq⟩ := List.mem_map.mp endpoint
    exact (excluded d mem).2 eq

private theorem separator_conditions {m : Model K A}
    {candidates : List (Dependency K A)} {facts : ClassFacts A} {t : Triple K A}
    {ds : List (Dependency K A)} (found : firstSeparator m candidates facts t = some ds) :
    m.independent (t.left m) t.right (ds.map Dependency.source) = true ∧
      t.left m ∉ ds.map Dependency.source ∧ t.right ∉ ds.map Dependency.source := by
  obtain ⟨visited, as, bs, all, _⟩ := List.find?_eq_some_iff_append.mp found
  have sub : ds.Sublist (availableParents m candidates facts t) :=
    mem_conditioningLists.mp (by rw [all]; simp)
  exact ⟨visited, available_parent_endpoints_excluded sub⟩

/-- Every update in Algorithm 1's representative-triple loop is sound
under the oracle properties used in Lemma 2 and Proposition 1. -/
theorem orient_triple_sound {m : Model K A} {t : Triple K A}
    {initial candidates : List (Dependency K A)} {facts : ClassFacts A}
    (rep : Representative m t) (acyclic : m.acyclic) (sound : facts.sound m)
    (proper : ∀ c ∈ initial, c.source ≠ canonical m.itemClass c.effect)
    (retainedElts : candidates.Sublist initial)
    (keeps : candidates.filter m.trueDependency = initial.filter m.trueDependency)
    (orientationFaithful : OrientationFaithful m)
    (parentSeparation : CanonicalParentSeparation m initial)
    (symmetric : SymmetricOracle m) :
    (orientTriple m candidates facts t).sound m := by
  classical
  unfold orientTriple
  split
  · exact sound
  · split
    next missing =>
      apply ClassFacts.addAncestor_sound sound
      apply Classical.byContradiction
      intro noAncestor
      have parentCI := parentSeparation t.endpointDependency rep.leftRightDistinct.symm
        rep.endpoint_pair_absent noAncestor
      let ds := initial.filter fun d => decide (d.effect = t.leftAttribute) && m.trueDependency d
      have available := available_contains_true_parents rep acyclic sound proper retainedElts keeps
      have tested := mem_conditioningLists.mpr available
      have noTest := List.find?_eq_none.mp missing ds tested
      have outs := available_parent_endpoints_excluded available
      apply noTest
      rw [symmetric _ _ _ rep.leftRightDistinct outs.1 outs.2]
      exact parentCI
    next ds found =>
      have ⟨ci, leftOutside, rightOutside⟩ := separator_conditions found
      have compatible : ¬ ((t.collider m ∧ t.middle ∈ ds.map Dependency.source) ∨
          (¬ t.collider m ∧ t.middle ∉ ds.map Dependency.source)) := by
        intro rejected
        rw [orientationFaithful t rep _ leftOutside rightOutside rejected] at ci
        contradiction
      split
      next middleOutside =>
        have collider : t.collider m := Classical.byContradiction
          (fun h => compatible (.inr ⟨h, middleOutside⟩))
        obtain ⟨left, right⟩ := (rep.class_collider_iff acyclic).mpr collider
        exact ClassFacts.addArrow_sound (ClassFacts.addArrow_sound sound left) right
      next notOutside =>
        have noClassCollider : ¬ t.classCollider m := by
          intro collider
          exact compatible (.inl ⟨(rep.class_collider_iff acyclic).mp collider,
            Classical.not_not.mp notOutside⟩)
        change ClassFacts.sound m
          (if t.leftAttribute = t.right.2 then facts.addArrow t.middle.2 t.leftAttribute
            else facts.addNoncollider t.leftAttribute t.middle.2 t.right.2)
        split
        next equal =>
          apply ClassFacts.addArrow_sound sound
          rcases rep.classes_adjacent.1 with inwards | outwards
          · exact (noClassCollider ⟨inwards, by rwa [← equal]⟩).elim
          · exact outwards
        · exact ClassFacts.addNoncollider_sound sound noClassCollider

/-- The order of representative triples may change the found separators.
Each choice recorded by the loop remains correct. -/
noncomputable def orientationPhase (m : Model K A) (candidates : List (Dependency K A))
    (triples : List (Triple K A)) (background : ClassFacts A) : ClassFacts A :=
  triples.foldl (orientTriple m candidates) background

theorem orientation_phase_sound {m : Model K A}
    {initial candidates : List (Dependency K A)} {triples : List (Triple K A)}
    {background : ClassFacts A}
    (reps : ∀ t ∈ triples, Representative m t) (acyclic : m.acyclic)
    (sound : background.sound m)
    (proper : ∀ c ∈ initial, c.source ≠ canonical m.itemClass c.effect)
    (retainedElts : candidates.Sublist initial)
    (keeps : candidates.filter m.trueDependency = initial.filter m.trueDependency)
    (orientationFaithful : OrientationFaithful m)
    (parentSeparation : CanonicalParentSeparation m initial)
    (symmetric : SymmetricOracle m) :
    (orientationPhase m candidates triples background).sound m := by
  induction triples generalizing background with
  | nil => exact sound
  | cons t remaining ih =>
    have newSound := orient_triple_sound (reps t (by simp)) acyclic sound proper
      retainedElts keeps orientationFaithful parentSeparation symmetric
    exact ih (fun r present => reps r (List.mem_cons_of_mem t present)) newSound

end Orientation

section ClassRules

def candidateAdjacent (candidates : List (Dependency K A)) (a b : A) : Prop :=
  ∃ d ∈ candidates, (d.cause = a ∧ d.effect = b) ∨ (d.cause = b ∧ d.effect = a)

def ClassFacts.unoriented (adjacent : A → A → Prop) (facts : ClassFacts A) (a b : A) : Prop :=
  adjacent a b ∧ ¬ facts.oriented a b

/-- RCD-Light Figure 3. Each pair of red edges in R1, R3, and R4 marks a
known noncollider. R1 permits either status for the third adjacency. -/
inductive ClassRule (adjacent : A → A → Prop) (facts : ClassFacts A) : A → A → Prop
  | r1 {a b c} :
      facts.unoriented adjacent a b → facts.directed c a → facts.noncollider c a b →
      ClassRule adjacent facts a b
  | r2 {a b c} :
      facts.unoriented adjacent a b → facts.directed a c → facts.directed c b →
      ClassRule adjacent facts a b
  | r3 {a b c d} :
      facts.unoriented adjacent a b →
      facts.unoriented adjacent a c → facts.unoriented adjacent a d →
      facts.directed c b → facts.directed d b → facts.noncollider c a d →
      ClassRule adjacent facts a b
  | r4 {a b c d} :
      facts.unoriented adjacent a b →
      facts.unoriented adjacent a c → facts.unoriented adjacent a d →
      facts.directed c d → facts.directed d b → facts.noncollider b a c →
      ClassRule adjacent facts a b

omit [DecidableEq K] [DecidableEq A] in
private theorem must_align {m : Model K A} (acyclic : m.acyclic) {a b : A}
    (path : Reach m.classArrow a b) (adjacent : m.classAdjacent a b) : m.classArrow a b :=
  adjacent.elim id (fun back => (acyclic a (.extend path back)).elim)

omit [DecidableEq K] [DecidableEq A] in
theorem class_rule_sound {m : Model K A} {adjacent : A → A → Prop} {facts : ClassFacts A}
    (acyclic : m.acyclic) (sound : facts.sound m)
    (trueAdjacency : ∀ a b, adjacent a b → m.classAdjacent a b) {a b : A}
    (rule : ClassRule adjacent facts a b) : m.classArrow a b := by
  cases rule with
  | r1 ab ca n =>
    exact (trueAdjacency _ _ ab.1).elim id
      (fun back => (sound.2.2 _ _ _ n ⟨sound.1 _ _ ca, back⟩).elim)
  | r2 ab ac cb =>
    exact must_align acyclic (.extend (.single (sound.1 _ _ ac)) (sound.1 _ _ cb))
      (trueAdjacency _ _ ab.1)
  | r3 ab ac ad cb db n =>
    rcases trueAdjacency _ _ ab.1 with arrow | back
    · exact arrow
    · have ca := must_align acyclic (.extend (.single (sound.1 _ _ cb)) back)
        (trueAdjacency _ _ ac.1).symm
      have da := must_align acyclic (.extend (.single (sound.1 _ _ db)) back)
        (trueAdjacency _ _ ad.1).symm
      exact (sound.2.2 _ _ _ n ⟨ca, da⟩).elim
  | r4 ab ac _ cd db n =>
    rcases trueAdjacency _ _ ab.1 with arrow | back
    · exact arrow
    · have ca := must_align acyclic
        (.extend (.extend (.single (sound.1 _ _ cd)) (sound.1 _ _ db)) back)
        (trueAdjacency _ _ ac.1).symm
      exact (sound.2.2 _ _ _ n ⟨back, ca⟩).elim

def classRound (adjacent : A → A → Prop) (facts : ClassFacts A) : ClassFacts A :=
  { facts with directed := fun a b => facts.directed a b ∨ ClassRule adjacent facts a b }

def classRounds (adjacent : A → A → Prop) : Nat → ClassFacts A → ClassFacts A
  | 0, facts => facts
  | n + 1, facts => classRound adjacent (classRounds adjacent n facts)

omit [DecidableEq K] [DecidableEq A] in
theorem class_rounds_sound {m : Model K A} {adjacent : A → A → Prop} {facts : ClassFacts A}
    (acyclic : m.acyclic) (sound : facts.sound m)
    (trueAdjacency : ∀ a b, adjacent a b → m.classAdjacent a b) (rounds : Nat) :
    (classRounds adjacent rounds facts).sound m := by
  induction rounds with
  | zero => exact sound
  | succ n prior =>
    exact ⟨fun a b added => added.elim (prior.1 a b)
      (class_rule_sound acyclic prior trueAdjacency), prior.2⟩

end ClassRules

section Learner

open RelationalFiniteSearch

omit [DecidableEq K] [DecidableEq A] in
private theorem candidate_class_adjacency {m : Model K A}
    {candidates : List (Dependency K A)}
    (pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d) :
    ∀ a b, candidateAdjacent candidates a b → m.classAdjacent a b := by
  intro a b known
  obtain ⟨d, hmem, sides⟩ := known
  rcases pairsSound d hmem with forward | backward
  · have edge : m.classArrow d.cause d.effect := ⟨d.path, by cases d; exact forward⟩
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl edge
    · exact .inr edge
  · have edge : m.classArrow d.effect d.cause :=
      ⟨d.path.reverse, by cases d; exact backward⟩
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr edge
    · exact .inl edge

/-- Line 21 retains both candidate directions when no class orientation is
known and otherwise discards the opposite candidate. -/
noncomputable def orientDependencies (candidates : List (Dependency K A)) (facts : ClassFacts A) :
    List (Dependency K A) :=
  open Classical in
  candidates.filter fun d => decide (¬ facts.directed d.effect d.cause)

omit [DecidableEq K] [DecidableEq A] in
private theorem orientation_preserves_true {m : Model K A} {facts : ClassFacts A}
    {candidates : List (Dependency K A)} (acyclic : m.acyclic) (sound : facts.sound m)
    {d : Dependency K A} (retained : d ∈ candidates) (trueD : m.trueDependency d = true) :
    d ∈ orientDependencies candidates facts := by
  classical
  apply List.mem_filter.mpr
  refine ⟨retained, decide_eq_true ?_⟩
  intro opposite
  have forward : m.classArrow d.cause d.effect := ⟨d.path, by cases d; exact trueD⟩
  exact acyclic d.cause (.extend (.single forward) (sound.1 _ _ opposite))

omit [DecidableEq K] [DecidableEq A] in
private theorem one_sided_orientation_sound {m : Model K A} {facts : ClassFacts A}
    {candidates : List (Dependency K A)} (acyclic : m.acyclic) (sound : facts.sound m)
    (closed : PairClosed m.query candidates)
    (pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    {d : Dependency K A} (kept : d ∈ orientDependencies candidates facts)
    (removed : d.reverse ∉ orientDependencies candidates facts) :
    m.trueDependency d = true := by
  have initial := (List.mem_filter.mp kept).1
  rcases pairsSound d initial with forward | backward
  · exact forward
  · exact (removed (orientation_preserves_true acyclic sound (closed d initial) backward)).elim

omit [DecidableEq K] [DecidableEq A] in
private theorem oriented_output_sound {m : Model K A} {facts : ClassFacts A}
    {candidates : List (Dependency K A)} (acyclic : m.acyclic) (sound : facts.sound m)
    (closed : PairClosed m.query candidates)
    (pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    (containsTruth : ∀ d, m.trueDependency d = true → d ∈ candidates) :
    (∀ d, m.trueDependency d = true → d ∈ orientDependencies candidates facts) ∧
      (∀ d ∈ orientDependencies candidates facts, d.reverse ∉ orientDependencies candidates facts →
        m.trueDependency d = true) ∧
      ∀ d, (d ∈ orientDependencies candidates facts ∨ d.reverse ∈ orientDependencies candidates facts) ↔
        pairPresent m.query m.trueDependency d := by
  have retains (d : Dependency K A) (truth : m.trueDependency d = true) :
      d ∈ orientDependencies candidates facts :=
    orientation_preserves_true acyclic sound (containsTruth d truth) truth
  refine ⟨retains, fun _ kept removed =>
    one_sided_orientation_sound acyclic sound closed pairsSound kept removed, ?_⟩
  intro d
  constructor
  · rintro (direct | reverse)
    · exact pairsSound d (List.mem_filter.mp direct).1
    · have pair := pairsSound d.reverse (List.mem_filter.mp reverse).1
      exact pair.elim (fun back => .inr back)
        (fun forward => .inl (by simpa [Model.query, Dependency.reverse_reverse] using forward))
  · rintro (direct | reverse)
    · exact .inl (retains d direct)
    · exact .inr (retains d.reverse reverse)

/-- Compose both oracle passes and the RCD-Light class rules. The class rule
rounds can stop at any point for soundness. -/
noncomputable def learn (m : Model K A) (initial : List (Dependency K A))
    (representatives : List (Triple K A)) (background : ClassFacts A) (rounds : Nat) :
    List (Dependency K A) × ClassFacts A :=
  let candidates := adjacencyPhase m initial
  let adjacent := candidateAdjacent candidates
  let start := classRounds adjacent rounds background
  let marked := orientationPhase m candidates representatives start
  let finished := classRounds adjacent rounds marked
  (orientDependencies candidates finished, finished)

/-- The checked soundness assertion for Algorithm 1. Every true dependency
is retained and every newly one-sided direction is correct. The surviving
undirected pairs are exactly the true dependency pairs. The premises give
the canonical ground-CI properties and soundness of supplied representatives. -/
theorem learner_sound (m : Model K A) (initial : List (Dependency K A))
    (representatives : List (Triple K A)) (background : ClassFacts A) (rounds : Nat)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (faithful : AdjacencyFaithful m) (parentSeparation : CanonicalParentSeparation m initial)
    (reps : ∀ t ∈ representatives, Representative m t) (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) (symmetric : SymmetricOracle m) :
    let out := learn m initial representatives background rounds
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      ∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d := by
  let candidates := adjacencyPhase m initial
  let adjacent := candidateAdjacent candidates
  let start := classRounds adjacent rounds background
  let marked := orientationPhase m candidates representatives start
  let finished := classRounds adjacent rounds marked
  have exactPairs d := adjacency_phase_exact m initial acyclic reverseClosed proper faithful
    parentSeparation d
  have pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d :=
    fun d mem => ((exactPairs d).mp mem).2
  have adjSound := candidate_class_adjacency pairsSound
  have startSound := class_rounds_sound acyclic backgroundSound adjSound rounds
  have candidatesSublist : candidates.Sublist initial :=
    search_sublist m.query initial (Nat.zero_le (initial.length + 1))
  have keeps : candidates.filter m.trueDependency = initial.filter m.trueDependency :=
    search_keeps_truth m.query m.trueDependency initial (initial.length + 1) _
      (fun _ h => h) proper faithful
  have markedSound := orientation_phase_sound reps acyclic startSound proper candidatesSublist
    keeps orientationFaithful parentSeparation symmetric
  have finishedSound : finished.sound m := class_rounds_sound acyclic markedSound adjSound rounds
  have closed : PairClosed m.query candidates :=
    search_closed m.query Dependency.reverse_reverse initial reverseClosed (initial.length + 1)
  exact ⟨finishedSound, oriented_output_sound acyclic finishedSound closed pairsSound
    (fun d truth => (exactPairs d).mpr ⟨exhaustive d truth, .inl truth⟩)⟩

/-- Algorithm 1 propagates class orientations immediately after visiting each
representative. The number of rounds is a finite implementation parameter. -/
noncomputable def learnInterleaved (m : Model K A) (initial : List (Dependency K A))
    (representatives : List (Triple K A)) (background : ClassFacts A) (rounds : Nat) :
    List (Dependency K A) × ClassFacts A :=
  let candidates := adjacencyPhase m initial
  let adjacent := candidateAdjacent candidates
  let close := classRounds adjacent rounds
  let finished := representatives.foldl
    (fun facts triple => close (orientTriple m candidates facts triple)) (close background)
  (orientDependencies candidates finished, finished)

theorem learner_interleaved_sound (m : Model K A) (initial : List (Dependency K A))
    (representatives : List (Triple K A)) (background : ClassFacts A) (rounds : Nat)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (faithful : AdjacencyFaithful m) (parentSeparation : CanonicalParentSeparation m initial)
    (reps : ∀ t ∈ representatives, Representative m t) (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) (symmetric : SymmetricOracle m) :
    let out := learnInterleaved m initial representatives background rounds
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      ∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d := by
  let candidates := adjacencyPhase m initial
  let adjacent := candidateAdjacent candidates
  let close := classRounds adjacent rounds
  let step facts t := close (orientTriple m candidates facts t)
  let finished := representatives.foldl step (close background)
  have exactPairs d := adjacency_phase_exact m initial acyclic reverseClosed proper faithful parentSeparation d
  have pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d :=
    fun d member => ((exactPairs d).mp member).2
  have adjSound := candidate_class_adjacency pairsSound
  have candidatesSublist : candidates.Sublist initial :=
    search_sublist m.query initial (Nat.zero_le (initial.length + 1))
  have keeps : candidates.filter m.trueDependency = initial.filter m.trueDependency :=
    search_keeps_truth m.query m.trueDependency initial (initial.length + 1) _
      (fun _ h => h) proper faithful
  have soundFold (schedule : List (Triple K A)) (start : ClassFacts A)
      (valid : ∀ t ∈ schedule, Representative m t) (startSound : start.sound m) :
      (schedule.foldl step start).sound m := by
    induction schedule generalizing start with
    | nil => exact startSound
    | cons t rest ih =>
      have marked := orient_triple_sound (valid t (by simp)) acyclic startSound proper candidatesSublist
        keeps orientationFaithful parentSeparation symmetric
      exact ih (step start t) (fun u included => valid u (List.mem_cons_of_mem t included))
        (class_rounds_sound acyclic marked adjSound rounds)
  have finishedSound : finished.sound m := soundFold representatives (close background) reps
    (class_rounds_sound acyclic backgroundSound adjSound rounds)
  have closed : PairClosed m.query candidates :=
    search_closed m.query Dependency.reverse_reverse initial reverseClosed (initial.length + 1)
  exact ⟨finishedSound, oriented_output_sound acyclic finishedSound closed pairsSound
    (fun d truth => (exactPairs d).mpr ⟨exhaustive d truth, .inl truth⟩)⟩

end Learner

end RCDLight.Learning

end
