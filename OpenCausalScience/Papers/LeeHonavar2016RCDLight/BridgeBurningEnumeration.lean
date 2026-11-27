module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.Enumeration
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDPathValidity

/-! Connect Lemma 5 in bridge-burning semantics to Algorithm 1's finite line 11 schedule. -/

@[expose] public section

namespace RCDLight.Learning

open RCDPathValidity RelationalFiniteSearch

variable {K A : Type} [DecidableEq K] [DecidableEq A]

/-- A dependency joins two distinct attributes, and its path starts at the effect class. -/
def Dependency.Typed (m : Model K A) (d : Dependency K A) : Prop :=
  m.validPath d.path ∧ d.path.head? = some (m.itemClass d.effect) ∧
    d.path.getLast? = some (m.itemClass d.cause) ∧ d.cause ≠ d.effect

/-- Interpret the finite list after Phase I as the reverse-closed relational model. -/
def bridgeBurningCandidates (S : Schema K) (m : Model K A) (candidates : List (Dependency K A))
    (pathSemantics : ∀ path, m.validPath path ↔ HasTerminal S path)
    (closed : PairClosed m.query candidates)
    (typed : ∀ d ∈ candidates, d.Typed m) : PhaseOne S A where
  owner := m.itemClass
  dependency path cause effect := (⟨path,cause,effect⟩ : Dependency K A) ∈ candidates
  valid_dependency h := (pathSemantics _).mp (typed _ h).1
  dependency_endpoints h := ⟨(typed _ h).2.1, (typed _ h).2.2.1⟩
  reverse_dependency h := closed _ h
  different_attributes h := (typed _ h).2.2.2

private theorem candidate_arrow_iff (S : Schema K) (m : Model K A)
    (candidates : List (Dependency K A)) (pathSemantics : ∀ path, m.validPath path ↔ HasTerminal S path)
    (closed : PairClosed m.query candidates) (typed : ∀ d ∈ candidates, d.Typed m)
    (u v : Variable K A) :
    UnrolledEdge (bridgeBurningCandidates S m candidates pathSemantics closed typed) u v ↔
      (m.candidateModel candidates).unrolled u v := by
  constructor
  · rintro ⟨d, member, valid, splice⟩
    exact ⟨(pathSemantics _).mpr valid, d, decide_eq_true member, RCDLemma5.splice_iff.mp splice⟩
  · rintro ⟨valid, d, member, pivot⟩
    have hMem : (⟨d,u.2,v.2⟩ : Dependency K A) ∈ candidates := of_decide_eq_true member
    exact ⟨d, hMem, (pathSemantics _).mp valid, RCDLemma5.splice_iff.mpr pivot⟩

/-- On valid variables the relational and learner graphs have the same unshielded triples. -/
theorem candidate_unshielded_iff (S : Schema K) (m : Model K A)
    (candidates : List (Dependency K A)) (pathSemantics : ∀ path, m.validPath path ↔ HasTerminal S path)
    (closed : PairClosed m.query candidates) (typed : ∀ d ∈ candidates, d.Typed m)
    (p q r : Variable K A) (validP : m.validPath p.1) (validR : m.validPath r.1) :
    UnshieldedTriple (bridgeBurningCandidates S m candidates pathSemantics closed typed) p q r ↔
      (m.candidateModel candidates).unrolledAdjacent p q ∧
      (m.candidateModel candidates).unrolledAdjacent r q ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ ¬ (m.candidateModel candidates).unrolledAdjacent r p := by
  let arrows := candidate_arrow_iff S m candidates pathSemantics closed typed
  have reverse {u v : Variable K A} (validV : m.validPath v.1)
      (h : (m.candidateModel candidates).unrolled u v) :
      (m.candidateModel candidates).unrolled v u := by
    obtain ⟨d, dep, _, splice⟩ := (arrows u v).mpr h
    let C := bridgeBurningCandidates S m candidates pathSemantics closed typed
    exact (arrows v u).mp ⟨d.reverse, C.reverse_dependency dep,
      (pathSemantics _).mp validV, RCDLemma5.splice_triangle splice⟩
  constructor
  · rintro ⟨left, right, leftNe, rightNe, flankNe, noRight, noLeft⟩
    exact ⟨.inl ((arrows p q).mp left), .inl ((arrows r q).mp right), leftNe, rightNe, flankNe,
      fun h => h.elim (fun e => noRight ((arrows r p).mpr e))
        (fun e => noLeft ((arrows p r).mpr e))⟩
  · rintro ⟨left, right, leftNe, rightNe, flankNe, noShield⟩
    exact ⟨(arrows p q).mpr (left.elim id (reverse validP)),
      (arrows r q).mpr (right.elim id (reverse validR)), leftNe, rightNe, flankNe,
      fun e => noShield (.inl ((arrows r p).mp e)), fun e => noShield (.inr ((arrows p r).mp e))⟩

/-- Every unshielded triple in the bridge-burning interpretation of the finite Phase I
output contributes a representative to the actual enumeration of Algorithm 1. -/
theorem enumeration_covers_unshielded (S : Schema K) (m : Model K A)
    (candidates : List (Dependency K A)) (pathSemantics : ∀ path, m.validPath path ↔ HasTerminal S path)
    (closed : PairClosed m.query candidates) (typed : ∀ d ∈ candidates, d.Typed m)
    (complete : ∀ d, m.trueDependency d = true → d ∈ candidates)
    (sound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    {p q r : List K} {x y z : A}
    (unshielded : UnshieldedTriple (bridgeBurningCandidates S m candidates pathSemantics closed typed)
      (p,x) (q,y) (r,z)) :
    ∃ d₁ d₂ c : List K,
      (⟨d₁,x,y⟩ : Dependency K A) ∈ candidates ∧
      (⟨d₂,z,y⟩ : Dependency K A) ∈ candidates ∧
      (⟨x,(d₁.reverse,y),(c,z)⟩ : Triple K A) ∈ enumerateRepresentatives m candidates ∧
      ¬ Intersectable S ([m.itemClass x],x) (c,z) ∧
      RCDLemma5.Splice p c r := by
  obtain ⟨d₁,d₂,c, dep1,dep2, canon, middle, right, triple, disjoint, _, _, _, compatible⟩ :=
    RCDPathValidity.representative_unshielded_triple unshielded
  obtain ⟨first, second, _, _, different, shield1, shield2⟩ := triple
  let t : Triple K A := ⟨x,(d₁.reverse,y),(c,z)⟩
  let arrowEq := candidate_arrow_iff S m candidates pathSemantics closed typed
  have representative : Representative (m.candidateModel candidates) t :=
    ⟨different, .inl ((arrowEq _ _).mp first), .inr ((arrowEq _ _).mp second),
      fun h => h.elim (fun edge => shield2 ((arrowEq _ _).mpr edge))
        (fun edge => shield1 ((arrowEq _ _).mpr edge)),
      (pathSemantics _).mpr right.1, right.2.1,
      (pathSemantics _).mpr middle.1, (pathSemantics _).mpr canon.1⟩
  have actual := (candidate_representative_iff m candidates complete sound t).mp representative
  exact ⟨d₁,d₂,c, dep1,dep2,
    (mem_enumerate_representatives m candidates closed complete sound t).mpr actual,
    disjoint, compatible⟩

/-- The same coverage with the surviving list supplied by lines 1–8. The Phase I
hypotheses are precisely those used by `adjacency_phase_exact`. -/
theorem enumeration_after_adjacency_phase (S : Schema K) (m : Model K A)
    (initial : List (Dependency K A)) (pathSemantics : ∀ path, m.validPath path ↔ HasTerminal S path)
    (acyclic : m.acyclic) (closed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (typing : ∀ d ∈ initial, d.Typed m)
    (faithful : AdjacencyFaithful m) (parentSeparation : CanonicalParentSeparation m initial)
    {p q r : List K} {x y z : A}
    (unshielded : UnshieldedTriple (bridgeBurningCandidates S m (adjacencyPhase m initial) pathSemantics
      (search_closed m.query Dependency.reverse_reverse initial closed (initial.length + 1))
      (fun d hd => typing d ((adjacency_phase_exact m initial acyclic closed proper faithful
        parentSeparation d).mp hd).1)) (p,x) (q,y) (r,z)) :
    ∃ d₁ d₂ c : List K,
      (⟨d₁,x,y⟩ : Dependency K A) ∈ adjacencyPhase m initial ∧
      (⟨d₂,z,y⟩ : Dependency K A) ∈ adjacencyPhase m initial ∧
      (⟨x,(d₁.reverse,y),(c,z)⟩ : Triple K A) ∈
        enumerateRepresentatives m (adjacencyPhase m initial) ∧
      ¬ Intersectable S ([m.itemClass x],x) (c,z) ∧
      RCDLemma5.Splice p c r := by
  have exactPairs d := adjacency_phase_exact m initial acyclic closed proper faithful parentSeparation d
  have complete d (edge : m.trueDependency d = true) := (exactPairs d).mpr ⟨exhaustive d edge, .inl edge⟩
  have sound d (member : d ∈ adjacencyPhase m initial) := ((exactPairs d).mp member).2
  exact enumeration_covers_unshielded S m _ pathSemantics _ _ complete sound unshielded

def localDecidable (adj retrace : K → K → Prop)
    [DecidableRel adj] [DecidableRel retrace] : (w : List K) →
    Decidable (RCDLemma5.Local adj retrace w)
  | a :: b :: c :: rest =>
    letI := localDecidable adj retrace (b :: c :: rest)
    inferInstanceAs (Decidable
      (adj a b ∧ (a ≠ c ∨ retrace a b) ∧ RCDLemma5.Local adj retrace (b :: c :: rest)))
  | [a,b] => inferInstanceAs (Decidable (adj a b))
  | [] | [_] => isTrue trivial

/-- The bridge-burning path-validity check uses the equivalent local schema tests. -/
def validBridgeBurningPath (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (w : List K) : Bool :=
  letI : DecidableRel S.adj := fun a b => inferInstanceAs (Decidable (S.role a b ∨ S.role b a))
  letI : DecidableRel S.retrace := fun a b => inferInstanceAs (Decidable (S.role a b ∧ S.many a b))
  letI := localDecidable S.adj S.retrace w
  decide (w ≠ [] ∧ RCDLemma5.Local S.adj S.retrace w)

omit [DecidableEq A] in
theorem valid_bridge_burning_path_iff (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (w : List K) : validBridgeBurningPath S w = true ↔ HasTerminal S w := by
  simpa only [validBridgeBurningPath, decide_eq_true_eq] using
    (has_terminal_iff (S := S) (w := w)).symm

def finiteArrow (valid : List K → Bool) (candidates : List (Dependency K A))
    (u v : Variable K A) : Bool :=
  valid u.1 && candidates.any fun d =>
    decide (d.cause = u.2 ∧ d.effect = v.2) &&
      (List.range d.path.length).any fun i =>
        decide (Pivot v.1.reverse d.path (i + 1) ∧ joinAt v.1 d.path (i + 1) = u.1)

private theorem finite_arrow_iff (m : Model K A) {valid : List K → Bool}
    (exactValid : ∀ path, valid path = true ↔ m.validPath path)
    (candidates : List (Dependency K A)) (u v : Variable K A) :
    finiteArrow valid candidates u v = true ↔ (m.candidateModel candidates).unrolled u v := by
  simp only [finiteArrow, Bool.and_eq_true, exactValid, List.any_eq_true,
    decide_eq_true_eq, List.mem_range]
  constructor
  · rintro ⟨validU, d, member, ⟨sameCause, sameEffect⟩, i, _, pivot, joined⟩
    have eq : (⟨d.path,u.2,v.2⟩ : Dependency K A) = d := by cases d; simp_all
    exact ⟨validU, d.path, decide_eq_true (eq ▸ member), i + 1, pivot, joined⟩
  · rintro ⟨validU, path, member, n, pivot, join⟩
    refine ⟨validU, (⟨path,u.2,v.2⟩ : Dependency K A), of_decide_eq_true member,
      ⟨rfl,rfl⟩, n - 1, ?_, ?_⟩
    · have positive := pivot.1
      have bound := pivot.2.2.1
      dsimp
      omega
    · have index : n - 1 + 1 = n := by have := pivot.1; omega
      simpa only [index] using And.intro pivot join

def finiteAdjacent (valid : List K → Bool) (candidates : List (Dependency K A))
    (u v : Variable K A) : Bool := finiteArrow valid candidates u v || finiteArrow valid candidates v u

def finiteRepresentative (itemClass : A → K) (valid : List K → Bool)
    (candidates : List (Dependency K A)) (t : Triple K A) : Bool :=
  let left := canonical itemClass t.leftAttribute
  decide (left ≠ t.right) &&
    finiteAdjacent valid candidates left t.middle && finiteAdjacent valid candidates t.middle t.right &&
    !(finiteAdjacent valid candidates left t.right) && valid t.right.1 &&
    decide (t.right.1.head? = some (itemClass t.leftAttribute)) && valid t.middle.1 && valid left.1

private theorem finite_representative_iff (m : Model K A) {valid : List K → Bool}
    (exactValid : ∀ path, valid path = true ↔ m.validPath path)
    (candidates : List (Dependency K A)) (t : Triple K A) :
    finiteRepresentative m.itemClass valid candidates t = true ↔
      Representative (m.candidateModel candidates) t := by
  have adjacent (u v : Variable K A) : finiteAdjacent valid candidates u v = true ↔
      (m.candidateModel candidates).unrolledAdjacent u v := by
    simp only [finiteAdjacent, Bool.or_eq_true, finite_arrow_iff m exactValid,
      Model.unrolledAdjacent]
  have canonicalEq : t.left (m.candidateModel candidates) = canonical m.itemClass t.leftAttribute := rfl
  simp only [finiteRepresentative, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.eq_false_iff, adjacent, exactValid, ← canonicalEq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨different, leftArm⟩, rightArm⟩, unshielded⟩, rightValid⟩, rightBase⟩,
      middleValid⟩, canonicalValid⟩
    exact ⟨different, leftArm, rightArm, fun edge => unshielded ((adjacent _ _).mpr edge),
      rightValid, rightBase, middleValid, canonicalValid⟩
  · intro triple
    exact ⟨⟨⟨⟨⟨⟨⟨triple.leftRightDistinct, triple.leftArm⟩, triple.rightArm⟩,
      fun edge => triple.unshielded ((adjacent _ _).mp edge)⟩,
      triple.rightValid⟩, triple.rightBase⟩, triple.middleValid⟩, triple.canonicalValid⟩

/-- Executable line 11 schedule. The pivot scan and list order are the same as the
propositionally specified search. -/
def computableRepresentatives (itemClass : A → K) (valid : List K → Bool)
    (candidates : List (Dependency K A)) : List (Triple K A) :=
  (rawRepresentatives candidates).filter (finiteRepresentative itemClass valid candidates)

theorem computable_representatives_eq (m : Model K A) {valid : List K → Bool}
    (exactValid : ∀ path, valid path = true ↔ m.validPath path)
    (candidates : List (Dependency K A)) :
    computableRepresentatives m.itemClass valid candidates = enumerateRepresentatives m candidates := by
  apply List.filter_congr
  intro t _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, finite_representative_iff m exactValid]

/-- Run the finite representative filter with bridge-burning path validity. -/
def bridgeBurningRepresentatives (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (itemClass : A → K) (candidates : List (Dependency K A)) : List (Triple K A) :=
  computableRepresentatives itemClass (validBridgeBurningPath S) candidates

theorem bridge_burning_representatives_eq (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (m : Model K A) (pathSemantics : ∀ p, m.validPath p ↔ HasTerminal S p)
    (candidates : List (Dependency K A)) :
    bridgeBurningRepresentatives S m.itemClass candidates = enumerateRepresentatives m candidates :=
  computable_representatives_eq m (fun p => (valid_bridge_burning_path_iff S p).trans (pathSemantics p).symm)
    candidates

/-- A dependency bound of `h` hops bounds line 11's middle word by `h` hops
and its right word by `2 * h` hops. -/
theorem raw_representative_hop_bound (candidates : List (Dependency K A)) (h : Nat)
    (bound : ∀ d ∈ candidates, d.path.length ≤ h + 1) {t : Triple K A}
    (member : t ∈ rawRepresentatives candidates) :
    t.middle.1.length ≤ h + 1 ∧ t.right.1.length ≤ 2 * h + 1 := by
  simp only [rawRepresentatives, List.mem_flatMap, List.mem_filterMap] at member
  obtain ⟨d₁, in₁, d₂, in₂, i, _, found⟩ := member
  split at found
  next parts =>
    obtain ⟨pivotEq⟩ := found
    simp only [List.length_reverse]
    refine ⟨bound _ in₁, ?_⟩
    have splice : RCDLemma5.Splice d₁.path.reverse d₂.path
        (joinAt d₁.path.reverse d₂.path (i + 1)) :=
      RCDLemma5.splice_iff.mpr ⟨i + 1, by simpa only [List.reverse_reverse] using parts.2, rfl⟩
    have localBound {p q r : List K} (s : RCDLemma5.Splice p q r) :
        r.length + 1 ≤ p.length + q.length := by
      cases s
      simp only [List.length_append, List.length_cons, List.length_reverse]
      omega
    have total := localBound splice
    simp only [List.length_reverse] at total
    have leftBound := bound d₁ in₁
    have rightBound := bound d₂ in₂
    omega
  next => contradiction

end RCDLight.Learning

end
