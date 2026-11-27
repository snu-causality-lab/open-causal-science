module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.AdjacencyWitness
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.BridgeBurningEnumeration

/-! RCD-Light Algorithm 1, line 1: enumerate all legal relational
dependencies up to the given hop threshold. -/

@[expose] public section

namespace RCDLight.Learning

open RCDPathValidity RelationalFiniteSearch RCDLemma5

variable {K A : Type} [DecidableEq K] [DecidableEq A]

def legalWordsOfLength (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (classes : List K) : Nat → List (List K)
  | 0 => [[]]
  | n + 1 =>
    let suffixes := legalWordsOfLength S classes n
    classes.flatMap fun k =>
      suffixes.filterMap fun w =>
        if validBridgeBurningPath S (k :: w) then some (k :: w) else none

omit [DecidableEq K] in
private theorem local_tail (S : Schema K) {k : K} {xs : List K}
    (valid : Local S.adj S.retrace (k :: xs)) : Local S.adj S.retrace xs := by
  cases xs with
  | nil => trivial
  | cons a xs =>
    cases xs with
    | nil => trivial
    | cons b xs => exact valid.2.2

omit [DecidableEq A] in
private theorem mem_legalWordsOfLength {S : Schema K} [DecidableRel S.role] [DecidableRel S.many]
    {classes : List K} {n : Nat} {w : List K} :
    w ∈ legalWordsOfLength S classes n ↔
      w.length = n ∧ (∀ k ∈ w, k ∈ classes) ∧ (w = [] ∨ HasTerminal S w) := by
  induction n generalizing w with
  | zero => cases w <;> simp [legalWordsOfLength]
  | succ n ih =>
    cases w with
    | nil =>
      simp only [legalWordsOfLength, List.mem_flatMap, List.mem_filterMap, List.length_nil,
        Nat.zero_ne_add_one, false_and, iff_false]
      rintro ⟨k, _, tail, _, eq⟩
      split at eq <;> simp at eq
    | cons k w =>
      constructor
      · intro mem
        obtain ⟨head, headMem, inner⟩ := List.mem_flatMap.mp mem
        obtain ⟨tail, tailMem, eq⟩ := List.mem_filterMap.mp inner
        split at eq
        next valid =>
          obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj eq)
          obtain ⟨tailLength, tailInside, _⟩ := ih.mp tailMem
          exact ⟨by simp [tailLength], (fun r inside => (List.mem_cons.mp inside).elim
            (fun same => same.symm ▸ headMem) (tailInside r)),
            .inr ((valid_bridge_burning_path_iff S _).mp valid)⟩
        · contradiction
      · rintro ⟨length, allClasses, valid⟩
        have whole : HasTerminal S (k :: w) := valid.resolve_left (List.cons_ne_nil _ _)
        have suffixValid : w = [] ∨ HasTerminal S w := by
          by_cases empty : w = []
          · exact .inl empty
          · exact .inr (has_terminal_iff.mpr ⟨empty, local_tail S (has_terminal_iff.mp whole).2⟩)
        have suffix : w ∈ legalWordsOfLength S classes n := ih.mpr
          ⟨by simpa using length, fun r member => allClasses r (List.mem_cons_of_mem _ member),
            suffixValid⟩
        apply List.mem_flatMap.mpr
        refine ⟨k, allClasses k (by simp), List.mem_filterMap.mpr ⟨w, suffix, ?_⟩⟩
        rw [ite_eq_left ((valid_bridge_burning_path_iff S _).mpr whole)]

def assignAttributes (itemClass : A → K) (attributes : List A) (w : List K) :
    List (Dependency K A) :=
  attributes.flatMap fun cause =>
    attributes.filterMap fun effect =>
      if cause ≠ effect ∧ w.head? = some (itemClass effect) ∧
          w.getLast? = some (itemClass cause) then
        some ⟨w, cause, effect⟩
      else none

private theorem mem_assignedAttributes {itemClass : A → K} {attributes : List A}
    {w : List K} {d : Dependency K A} :
    d ∈ assignAttributes itemClass attributes w ↔
      d.path = w ∧ d.cause ∈ attributes ∧ d.effect ∈ attributes ∧ d.cause ≠ d.effect ∧
        w.head? = some (itemClass d.effect) ∧ w.getLast? = some (itemClass d.cause) := by
  constructor
  · intro mem
    obtain ⟨cause, causeMem, inner⟩ := List.mem_flatMap.mp mem
    obtain ⟨effect, effectMem, eq⟩ := List.mem_filterMap.mp inner
    split at eq
    next matchEndpoints =>
      cases Option.some.inj eq
      exact ⟨rfl, causeMem, effectMem, matchEndpoints⟩
    · contradiction
  · rintro ⟨rfl, causeMem, effectMem, proper⟩
    apply List.mem_flatMap.mpr
    refine ⟨d.cause, causeMem, List.mem_filterMap.mpr ⟨d.effect, effectMem, ?_⟩⟩
    rw [ite_eq_left proper]

/-- The word of a dependency with h hops has h+1 item classes. Zero hops
allows dependencies between different attributes of the same item. -/
def boundedDependencies (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (itemClass : A → K) (classes : List K) (attributes : List A) (maximumHops : Nat) :
    List (Dependency K A) :=
  ((List.range (maximumHops + 1)).flatMap fun n =>
    (legalWordsOfLength S classes (n + 1)).flatMap (assignAttributes itemClass attributes)).eraseDups

theorem mem_boundedDependencies {S : Schema K} [DecidableRel S.role] [DecidableRel S.many]
    {itemClass : A → K} {classes : List K} {attributes : List A} {maximumHops : Nat}
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes)
    {d : Dependency K A} :
    d ∈ boundedDependencies S itemClass classes attributes maximumHops ↔
      HasTerminal S d.path ∧ d.path.head? = some (itemClass d.effect) ∧
        d.path.getLast? = some (itemClass d.cause) ∧ d.cause ≠ d.effect ∧
        d.path.length ≤ maximumHops + 1 := by
  simp only [boundedDependencies, List.mem_eraseDups, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨n, atMost, w, listed, matched⟩
    obtain ⟨same, _, _, different, head, tail⟩ := mem_assignedAttributes.mp matched
    obtain ⟨length, _, valid⟩ := mem_legalWordsOfLength.mp listed
    have wordNonempty : w ≠ [] := by
      intro nil
      simp [nil] at length
    refine ⟨same.symm ▸ valid.resolve_left wordNonempty, same ▸ head, same ▸ tail,
      different, ?_⟩
    rw [same, length]
    omega
  · rintro ⟨legal, first, last, different, bound⟩
    have positive : 0 < d.path.length := List.length_pos_iff.mpr (has_terminal_iff.mp legal).1
    let hopCount := d.path.length - 1
    refine ⟨hopCount, by dsimp [hopCount]; omega, d.path, ?_, ?_⟩
    · exact mem_legalWordsOfLength.mpr
        ⟨by dsimp [hopCount]; omega, fun c _ => coversClasses c, .inr legal⟩
    · exact mem_assignedAttributes.mpr
        ⟨rfl, coversAttributes _, coversAttributes _, different, first, last⟩

theorem bounded_dependencies_reverse_closed (S : Schema K)
    [DecidableRel S.role] [DecidableRel S.many] (m : Model K A)
    {classes : List K} {attributes : List A} (maximumHops : Nat)
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes) :
    PairClosed m.query (boundedDependencies S m.itemClass classes attributes maximumHops) := by
  intro d member
  have membership := mem_boundedDependencies coversClasses coversAttributes
    (S := S) (itemClass := m.itemClass) (maximumHops := maximumHops) (d := d)
  obtain ⟨valid, first, last, different, bound⟩ := membership.mp member
  obtain ⟨nonempty, localValid⟩ := has_terminal_iff.mp valid
  have reverseValid : HasTerminal S d.path.reverse := has_terminal_iff.mpr
    ⟨fun empty => nonempty (List.reverse_eq_nil_iff.mp empty),
      local_reverse (fun h => S.symm h) localValid⟩
  apply (mem_boundedDependencies coversClasses coversAttributes).mpr
  exact ⟨reverseValid, by simpa [Model.query, Dependency.reverse] using last,
    by simpa [Model.query, Dependency.reverse] using first,
    different.symm, by simpa [Model.query, Dependency.reverse] using bound⟩

/-- The executable schema enumeration supplies the finite-list premises of
the learner. The maximum-hop assumption only needs to bound true dependencies. -/
theorem bounded_dependencies_learner_inputs (S : Schema K)
    [DecidableRel S.role] [DecidableRel S.many] (m : Model K A)
    {classes : List K} {attributes : List A} (maximumHops : Nat)
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes)
    (pathSemantics : ∀ p, m.validPath p ↔ HasTerminal S p)
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (hopBound : ∀ d, m.trueDependency d = true → d.path.length ≤ maximumHops + 1) :
    let candidates := boundedDependencies S m.itemClass classes attributes maximumHops
    PairClosed m.query candidates ∧
      (∀ d, m.trueDependency d = true → d ∈ candidates) ∧
      (∀ d ∈ candidates, d.source ≠ canonical m.itemClass d.effect) ∧
      ∀ d ∈ candidates, d.Typed m := by
  dsimp only
  have mem {d : Dependency K A} := mem_boundedDependencies coversClasses coversAttributes
    (S := S) (itemClass := m.itemClass) (maximumHops := maximumHops) (d := d)
  refine ⟨bounded_dependencies_reverse_closed S m maximumHops coversClasses coversAttributes,
    ?_, ?_, ?_⟩
  · intro d truth
    obtain ⟨legal, first, last⟩ := typed d truth
    have distinct : d.cause ≠ d.effect := by
      intro same
      have loop : m.classArrow d.effect d.effect := ⟨d.path, by cases d; simp_all⟩
      exact acyclic _ (.single loop)
    exact mem.mpr ⟨legal, first, last, distinct, hopBound d truth⟩
  · intro d listed eq
    exact (mem.mp listed).2.2.2.1 (congrArg Prod.snd eq)
  · intro d listed
    obtain ⟨legal, first, last, different, _⟩ := mem.mp listed
    exact ⟨(pathSemantics _).mpr legal, first, last, different⟩

noncomputable def learnBounded (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (m : Model K A) (classes : List K) (attributes : List A) (maximumHops : Nat)
    (background : ClassFacts A) : List (Dependency K A) × ClassFacts A :=
  learnToClosure m (boundedDependencies S m.itemClass classes attributes maximumHops) background

theorem bounded_learner_sound (S : Schema K)
    [DecidableRel S.role] [DecidableRel S.many] (m : Model K A)
    {classes : List K} {attributes : List A} (maximumHops : Nat) (background : ClassFacts A)
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes)
    (pathSemantics : ∀ p, m.validPath p ↔ HasTerminal S p)
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (hopBound : ∀ d, m.trueDependency d = true → d.path.length ≤ maximumHops + 1)
    (oracle : GroundOracle m S) (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) :
    let initial := boundedDependencies S m.itemClass classes attributes maximumHops
    let out := learnBounded S m classes attributes maximumHops background
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      (∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d) ∧
      classRound (candidateAdjacent (adjacencyPhase m initial)) out.2 = out.2 := by
  let initial := boundedDependencies S m.itemClass classes attributes maximumHops
  obtain ⟨closed, exhaustive, proper, _⟩ := bounded_dependencies_learner_inputs S m maximumHops
    coversClasses coversAttributes pathSemantics typed acyclic hopBound
  exact learner_to_closure_with_ground_adjacency initial background acyclic closed exhaustive
    proper typed oracle backgroundSound orientationFaithful

end RCDLight.Learning

end
