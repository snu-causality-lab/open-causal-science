module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.Enumeration
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDPathValidity
public import OpenCausalScience.Graph.ActiveSimplePath

/-! The ground-graph argument for the separating direction of Proposition 1.
Grounded variables that already appear among the conditioning variables are
removed from the query endpoints, as for conditional independence of vectors
with shared conditioned components. -/

@[expose] public section

namespace RCDLight.Learning

open RCDPathValidity RelationalFiniteSearch
open OpenCausalScience.ActiveSimplePath (Activated ActiveSuffix Adjacent DConnected OpenTurn)

def activeWord {V : Type} (arrow : V → V → Prop) (conditioned : V → Prop) :
    List V → Prop
  | [a, b] => Adjacent arrow a b
  | a :: b :: c :: tail => Adjacent arrow a b ∧ OpenTurn arrow conditioned a b c ∧
      activeWord arrow conditioned (b :: c :: tail)
  | _ => True

private theorem activeWord_snoc {V : Type} {arrow : V → V → Prop} {conditioned : V → Prop}
    (pref : List V) {a b c : V} (word : activeWord arrow conditioned (pref ++ [a, b]))
    (turn : OpenTurn arrow conditioned a b c) (edge : Adjacent arrow b c) :
    activeWord arrow conditioned (pref ++ [a, b, c]) := by
  induction pref with
  | nil => exact ⟨word, turn, edge⟩
  | cons x pref ih =>
    cases pref with
    | nil => exact ⟨word.1, word.2.1, ih word.2.2⟩
    | cons y pref =>
      cases pref with
      | nil => exact ⟨word.1, word.2.1, ih word.2.2⟩
      | cons z pref => exact ⟨word.1, word.2.1, ih word.2.2⟩

private theorem openTurn_symm {V : Type} {arrow : V → V → Prop}
    {conditioned : V → Prop} {a b c : V} (turn : OpenTurn arrow conditioned a b c) :
    OpenTurn arrow conditioned c b a := by
  rcases turn with ⟨collider, activate⟩ | ⟨notCollider, outside⟩
  · exact .inl ⟨collider.symm, activate⟩
  · exact .inr ⟨notCollider ∘ And.symm, outside⟩

private theorem activeWord_reverse {V : Type} {arrow : V → V → Prop} {conditioned : V → Prop}
    {vs : List V} (word : activeWord arrow conditioned vs) :
    activeWord arrow conditioned vs.reverse := by
  induction vs with
  | nil => trivial
  | cons a tail ih =>
    cases tail with
    | nil => trivial
    | cons b tail =>
      cases tail with
      | nil => exact word.symm
      | cons c tail =>
        have suffix := ih word.2.2
        have prior : activeWord arrow conditioned (tail.reverse ++ [c, b]) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using suffix
        simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
          (activeWord_snoc tail.reverse prior (openTurn_symm word.2.1) word.1.symm)

private theorem activeSuffix_to_word {V : Type} {arrow : V → V → Prop}
    {conditioned : V → Prop} {a b finish : V} {rest : List V}
    (walk : ActiveSuffix arrow conditioned a b rest finish) :
    activeWord arrow conditioned (a :: b :: rest) ∧
      (a :: b :: rest).getLast? = some finish := by
  induction walk with
  | last edge => exact ⟨edge, rfl⟩
  | cons edge turn _ ih => exact ⟨⟨edge, turn, ih.1⟩, by simpa using ih.2⟩

private theorem activeSuffix_of_word {V : Type} {arrow : V → V → Prop}
    {conditioned : V → Prop} {a b finish : V} {rest : List V}
    (word : activeWord arrow conditioned (a :: b :: rest))
    (last : (a :: b :: rest).getLast? = some finish) :
    ActiveSuffix arrow conditioned a b rest finish := by
  induction rest generalizing a b with
  | nil =>
    have same : b = finish := by simpa using last
    subst finish
    exact .last word
  | cons c tail ih => exact .cons word.1 word.2.1 (ih word.2.2 (by simpa using last))

theorem dconnected_reverse {V : Type} {arrow : V → V → Prop} {conditioned : V → Prop}
    {a b : V} (active : DConnected arrow conditioned a b) :
    DConnected arrow conditioned b a := by
  obtain ⟨second, rest, route, simple⟩ := active
  obtain ⟨word, last⟩ := activeSuffix_to_word route
  let xs := a :: second :: rest
  have wordRev : activeWord arrow conditioned xs.reverse := activeWord_reverse word
  have revHead : xs.reverse.head? = some b := List.head?_reverse.trans last
  have revLast : xs.reverse.getLast? = some a := List.getLast?_reverse
  have simpleRev : xs.reverse.Nodup := List.pairwise_reverse.mpr (simple.imp (fun h => Ne.symm h))
  obtain ⟨tail, revEq⟩ := List.head?_eq_some_iff.mp revHead
  cases tail with
  | nil =>
    have impossible := congrArg List.length revEq
    simp [xs] at impossible
  | cons next tail =>
    rw [revEq] at wordRev revLast simpleRev
    exact ⟨next, tail, activeSuffix_of_word wordRev revLast, simpleRev⟩

private theorem activating_parent_reaches {V : Type} {arrow : V → V → Prop} {root current : V}
    (active : Activated arrow (fun p => arrow p root) current) : Reach arrow current root := by
  induction active with
  | conditioned parent => exact .single parent
  | parent edge _ ih => exact (.single edge : Reach arrow _ _).trans ih

private theorem with_parent_conditions_forward {V : Type} {arrow : V → V → Prop}
    (acyclic : ∀ x, ¬ Reach arrow x x) {root prior current finish : V} {rest : List V}
    (walk : ActiveSuffix arrow (fun p => arrow p root) prior current rest finish)
    (reached : Reach arrow root current) (incoming : arrow prior current) :
    Reach arrow root finish := by
  induction walk with
  | last _ => exact reached
  | @cons a b c tail finish _ turn walk ih =>
    have forward : arrow b c := walk.first_adjacent.elim id (fun back => by
      rcases turn with ⟨_, active⟩ | ⟨noCollider, _⟩
      · exact (acyclic root (reached.trans (activating_parent_reaches active))).elim
      · exact (noCollider ⟨incoming, back⟩).elim)
    exact ih (.extend reached forward) forward

/-- The local Markov d-separation fact on a directed acyclic graph. The
query endpoint is outside the parent conditioning set. -/
theorem dseparated_from_nondescendants_given_parents {V : Type} {arrow : V → V → Prop}
    (acyclic : ∀ x, ¬ Reach arrow x x) {root other : V}
    (notParent : ¬ arrow other root) (notDescendant : ¬ Reach arrow root other) :
    ¬ DConnected arrow (fun p => arrow p root) root other := by
  rintro ⟨first, rest, walk, _⟩
  rcases walk.first_adjacent with start | intoRoot
  · exact notDescendant (with_parent_conditions_forward acyclic walk (.single start) start)
  · cases walk with
    | last _ => exact notParent intoRoot
    | @cons _ _ next _ _ _ turn _ =>
      rcases turn with ⟨⟨fromRoot, _⟩, _⟩ | ⟨_, outside⟩
      · exact acyclic root (.extend (.single fromRoot) intoRoot)
      · exact outside intoRoot

variable {K A : Type} {S : Schema K} {m : Model K A}

structure GroundVertex (m : Model K A) (g : Skeleton S) where
  item : g.Item
  attr : A
  typed : g.kind item = m.itemClass attr
  present : g.present item

def groundArrow (m : Model K A) (g : Skeleton S) (u v : GroundVertex m g) : Prop :=
  ∃ path, m.trueDependency ⟨path, u.attr, v.attr⟩ = true ∧
    Terminal g path v.item u.item

def instantiates (g : Skeleton S) (base : g.Item) (v : Variable K A)
    (x : GroundVertex m g) : Prop :=
  x.attr = v.2 ∧ Terminal g v.1 base x.item

def conditionedAt (g : Skeleton S) (base : g.Item) (conditions : List (Variable K A))
    (x : GroundVertex m g) : Prop :=
  ∃ v ∈ conditions, instantiates g base v x

def GroundSeparated (m : Model K A) (S : Schema K) (u v : Variable K A)
    (conditions : List (Variable K A)) : Prop :=
  ∀ (g : Skeleton S) (base : g.Item) (x y : GroundVertex m g),
    instantiates g base u x →
    instantiates g base v y →
    ¬ conditionedAt g base conditions x →
    ¬ conditionedAt g base conditions y →
    x ≠ y ∧ ¬ DConnected (groundArrow m g) (conditionedAt g base conditions) y x

/-- The oracle answers relational separation on every legal ground graph.
The contract is restricted to distinct relational query variables outside
the relational conditioning list. -/
def GroundOracle (m : Model K A) (S : Schema K) : Prop :=
  ∀ u v conditions, u ≠ v → u ∉ conditions → v ∉ conditions →
    (m.independent u v conditions = true ↔ GroundSeparated m S u v conditions)

theorem GroundSeparated.symm {u v : Variable K A} {conditions : List (Variable K A)}
    (sep : GroundSeparated m S u v conditions) : GroundSeparated m S v u conditions := by
  intro g base x y xt yt xOut yOut
  obtain ⟨different, noPath⟩ := sep g base y x yt xt yOut xOut
  exact ⟨different.symm, fun path => noPath (dconnected_reverse path)⟩

theorem symmetric_oracle_from_ground (oracle : GroundOracle m S) : SymmetricOracle m := by
  intro u v conditions different leftOut rightOut
  have forward := oracle u v conditions different leftOut rightOut
  have backward := oracle v u conditions different.symm rightOut leftOut
  apply Bool.eq_iff_iff.mpr
  exact forward.trans ⟨fun sep => backward.mpr sep.symm,
    fun trueCI => (backward.mp trueCI).symm⟩

private theorem ground_directed_path_has_class_path {g : Skeleton S} {x y : GroundVertex m g}
    (path : Reach (groundArrow m g) x y) : Reach m.classArrow x.attr y.attr := by
  induction path with
  | single edge =>
    obtain ⟨d, trueD, _⟩ := edge
    exact .single ⟨d, trueD⟩
  | extend _ edge ih =>
    obtain ⟨d, trueD, _⟩ := edge
    exact .extend ih ⟨d, trueD⟩

private theorem singleton_terminal_eq {g : Skeleton S} {k : K} {base other : g.Item}
    (h : Terminal g [k] base other) : other = base := by
  obtain ⟨head, tail, eq, _, _, rest⟩ := h
  obtain ⟨rfl, rfl⟩ := List.cons.inj eq
  exact rest

theorem ground_parent_conditions_exact [DecidableEq K] [DecidableEq A]
    {g : Skeleton S} {base : g.Item} {y : GroundVertex m g}
    (initial : List (Dependency K A)) (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    {b : A} (canonicalY : instantiates g base (canonical m.itemClass b) y) :
    conditionedAt g base (m.trueParents initial b) = (fun x => groundArrow m g x y) := by
  have sameItem := singleton_terminal_eq canonicalY.2
  have sameAttr : y.attr = b := canonicalY.1
  funext x
  apply propext
  constructor
  · rintro ⟨v, inList, rel⟩
    obtain ⟨d, kept, source⟩ := List.mem_map.mp inList
    obtain ⟨target, trueD⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp kept).2
    have exactTarget : d.effect = b := of_decide_eq_true target
    refine ⟨d.path, ?_, ?_⟩
    · have attr : x.attr = d.cause := rel.1.trans (congrArg Prod.snd source).symm
      rw [attr, sameAttr, ← exactTarget]
      cases d
      exact trueD
    · rw [sameItem, show d.path = v.1 from congrArg Prod.fst source]
      exact rel.2
  · rintro ⟨path, trueD, terminal⟩
    let d : Dependency K A := ⟨path, x.attr, y.attr⟩
    have mem : d ∈ initial := exhaustive _ trueD
    have eligible : (decide (d.effect = b) && m.trueDependency d) = true :=
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true sameAttr, trueD⟩
    refine ⟨d.source, List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨mem, eligible⟩, rfl⟩, rfl, ?_⟩
    simpa only [sameItem, Dependency.source] using terminal

theorem canonical_parent_separator_in_ground_graphs [DecidableEq K] [DecidableEq A]
    (initial : List (Dependency K A)) (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (acyclic : m.acyclic) {d : Dependency K A}
    (distinct : d.source ≠ canonical m.itemClass d.effect)
    (noClassDescendant : ¬ Reach m.classArrow d.effect d.cause) :
    GroundSeparated m S d.source (canonical m.itemClass d.effect) (m.trueParents initial d.effect) := by
  intro g base x y source target xOutside _
  have sameItem := singleton_terminal_eq target.2
  have xKind : x.attr = d.cause := source.1
  have yKind : y.attr = d.effect := target.1
  have conditions := ground_parent_conditions_exact initial exhaustive target
  refine ⟨?_, ?_⟩
  · intro same
    subst x
    have queryAtBase : Terminal g d.path base base := sameItem ▸ source.2
    have pathEq := noncanonical_excludes_base queryAtBase
    have baseKind : g.kind base = m.itemClass d.effect := by
      rw [← sameItem, y.typed, yKind]
    apply distinct
    apply Prod.ext
    · exact pathEq.trans (congrArg (fun k => [k]) baseKind)
    · exact xKind.symm.trans yKind
  · rw [conditions] at xOutside ⊢
    have groundAcyclic : ∀ z : GroundVertex m g, ¬ Reach (groundArrow m g) z z :=
      fun z cycle => acyclic z.attr (ground_directed_path_has_class_path cycle)
    apply dseparated_from_nondescendants_given_parents groundAcyclic xOutside
    intro groundDescendant
    have classDescendant := ground_directed_path_has_class_path groundDescendant
    exact noClassDescendant (by simpa only [xKind, yKind] using classDescendant)

theorem canonical_parent_separation_from_ground_oracle [DecidableEq K] [DecidableEq A]
    (initial : List (Dependency K A)) (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (acyclic : m.acyclic) (oracle : GroundOracle m S) : CanonicalParentSeparation m initial := by
  intro d distinct missing noAncestor
  let C := m.trueParents initial d.effect
  have directOut : d.source ∉ C := by
    intro overlap
    obtain ⟨c, kept, source⟩ := List.mem_map.mp overlap
    obtain ⟨_, accepted⟩ := List.mem_filter.mp kept
    obtain ⟨sameEffect, trueC⟩ := Bool.and_eq_true_iff.mp accepted
    have effect : c.effect = d.effect := of_decide_eq_true sameEffect
    have same : c = d := by cases c; cases d; simp_all [Dependency.source]
    exact missing (.inl (same ▸ trueC))
  have canonicalOut : canonical m.itemClass d.effect ∉ C := by
    intro overlap
    obtain ⟨c, found, source⟩ := List.mem_map.mp overlap
    obtain ⟨_, accepted⟩ := List.mem_filter.mp found
    obtain ⟨sameEffect, trueC⟩ := Bool.and_eq_true_iff.mp accepted
    have effect : c.effect = d.effect := of_decide_eq_true sameEffect
    have cause : c.cause = d.effect := congrArg Prod.snd source
    have loop : m.classArrow d.effect d.effect := ⟨c.path, by cases c; simp_all⟩
    exact acyclic _ (.single loop)
  exact (oracle d.source (canonical m.itemClass d.effect) C distinct directOut canonicalOut).mpr
    (canonical_parent_separator_in_ground_graphs initial exhaustive acyclic distinct noAncestor)

theorem learner_sound_with_ground_separator [DecidableEq K] [DecidableEq A]
    (initial : List (Dependency K A)) (background : ClassFacts A) (rounds : Nat)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (oracle : GroundOracle m S) (faithful : AdjacencyFaithful m)
    (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) (symmetric : SymmetricOracle m) :
    let out := learnWithEnumeration m initial background rounds
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      ∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d :=
  learner_with_enumeration_sound m initial background rounds acyclic reverseClosed
    exhaustive proper faithful (canonical_parent_separation_from_ground_oracle initial exhaustive
      acyclic oracle) backgroundSound orientationFaithful symmetric

end RCDLight.Learning

end
