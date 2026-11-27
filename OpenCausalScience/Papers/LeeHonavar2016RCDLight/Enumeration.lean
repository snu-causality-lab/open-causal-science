module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDLearning
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.RCDLemma5

/-! Finite representative-triple search for RCD-Light Algorithm 1, line 11.
The input to the search is the surviving dependency list from Phase I. -/

@[expose] public section

namespace RCDLight.Learning

open RCDLemma5 RelationalFiniteSearch

variable {K A : Type} [DecidableEq K] [DecidableEq A]

def Model.candidateModel (m : Model K A) (candidates : List (Dependency K A)) : Model K A :=
  { m with trueDependency := fun d => decide (d ∈ candidates) }

private theorem candidate_unrolled_reverse (m : Model K A) (candidates : List (Dependency K A))
    (closed : PairClosed m.query candidates) {u v : Variable K A} (validTarget : m.validPath v.1)
    (edge : (m.candidateModel candidates).unrolled u v) :
    (m.candidateModel candidates).unrolled v u := by
  obtain ⟨_, path, assessed, pivot⟩ := edge
  have forward : (⟨path, u.2, v.2⟩ : Dependency K A) ∈ candidates := of_decide_eq_true assessed
  have backward := closed _ forward
  have joined := splice_triangle (splice_iff.mpr pivot)
  exact ⟨validTarget, path.reverse, decide_eq_true backward, splice_iff.mp joined⟩

private theorem candidate_unrolled_adjacent_iff (m : Model K A)
    (candidates : List (Dependency K A))
    (complete : ∀ d, m.trueDependency d = true → d ∈ candidates)
    (sound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    {u v : Variable K A} (validU : m.validPath u.1) (validV : m.validPath v.1) :
    (m.candidateModel candidates).unrolledAdjacent u v ↔ m.unrolledAdjacent u v := by
  have forward {p q : Variable K A} (validTarget : m.validPath q.1)
      (edge : (m.candidateModel candidates).unrolled p q) : m.unrolledAdjacent p q := by
    obtain ⟨validSource, path, assessed, pivot⟩ := edge
    have members : (⟨path, p.2, q.2⟩ : Dependency K A) ∈ candidates := of_decide_eq_true assessed
    rcases sound _ members with original | reverse
    · exact .inl ⟨validSource, path, original, pivot⟩
    · exact .inr ⟨validTarget, path.reverse, reverse, splice_iff.mp
        (splice_triangle (splice_iff.mpr pivot))⟩
  have backward {p q : Variable K A} (edge : m.unrolled p q) :
      (m.candidateModel candidates).unrolled p q := by
    obtain ⟨validSource, path, assessed, pivot⟩ := edge
    exact ⟨validSource, path, decide_eq_true (complete _ assessed), pivot⟩
  exact ⟨fun h => h.elim (forward validV) (fun back => (forward validU back).symm),
    fun h => h.imp backward backward⟩

theorem candidate_representative_iff (m : Model K A) (candidates : List (Dependency K A))
    (complete : ∀ d, m.trueDependency d = true → d ∈ candidates)
    (sound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    (t : Triple K A) : Representative (m.candidateModel candidates) t ↔ Representative m t := by
  have leftArm := fun (validLeft : m.validPath (t.left m).1) (validMiddle : m.validPath t.middle.1) =>
    candidate_unrolled_adjacent_iff m candidates complete sound validLeft validMiddle
  have rightArm := fun (validMiddle : m.validPath t.middle.1) (validRight : m.validPath t.right.1) =>
    candidate_unrolled_adjacent_iff m candidates complete sound validMiddle validRight
  have endpoints := fun (validLeft : m.validPath (t.left m).1) (validRight : m.validPath t.right.1) =>
    candidate_unrolled_adjacent_iff m candidates complete sound validLeft validRight
  constructor <;> intro rep
  · exact ⟨rep.leftRightDistinct, (leftArm rep.canonicalValid rep.middleValid).mp rep.leftArm,
      (rightArm rep.middleValid rep.rightValid).mp rep.rightArm,
      fun h => rep.unshielded ((endpoints rep.canonicalValid rep.rightValid).mpr h),
      rep.rightValid, rep.rightBase, rep.middleValid, rep.canonicalValid⟩
  · exact ⟨rep.leftRightDistinct, (leftArm rep.canonicalValid rep.middleValid).mpr rep.leftArm,
      (rightArm rep.middleValid rep.rightValid).mpr rep.rightArm,
      fun h => rep.unshielded ((endpoints rep.canonicalValid rep.rightValid).mp h),
      rep.rightValid, rep.rightBase, rep.middleValid, rep.canonicalValid⟩

def rawRepresentatives (candidates : List (Dependency K A)) : List (Triple K A) :=
  candidates.flatMap fun left =>
    candidates.flatMap fun right =>
      (List.range right.path.length).filterMap fun n =>
        if left.effect = right.effect ∧ Pivot left.path right.path (n + 1) then
          some ⟨left.cause, (left.path.reverse, left.effect),
            (joinAt left.path.reverse right.path (n + 1), right.cause)⟩
        else none

noncomputable def enumerateRepresentatives (m : Model K A) (candidates : List (Dependency K A)) :
    List (Triple K A) :=
  open Classical in
  (rawRepresentatives candidates).filter fun t =>
    decide (Representative (m.candidateModel candidates) t)

private theorem representatives_in_raw (m : Model K A) (candidates : List (Dependency K A))
    (closed : PairClosed m.query candidates) {t : Triple K A}
    (rep : Representative (m.candidateModel candidates) t) : t ∈ rawRepresentatives candidates := by
  let hat := m.candidateModel candidates
  have leftArrow : hat.unrolled (t.left m) t.middle :=
    rep.leftArm.elim id (candidate_unrolled_reverse m candidates closed rep.canonicalValid)
  have rightArrow : hat.unrolled t.right t.middle :=
    rep.rightArm.elim (candidate_unrolled_reverse m candidates closed rep.rightValid) id
  obtain ⟨_, left, leftMember, leftJoin⟩ := leftArrow
  obtain ⟨_, right, rightMember, i, rightPivot, rightJoin⟩ := rightArrow
  have leftReversed : left = t.middle.1.reverse :=
    splice_canonicality (splice_iff.mpr leftJoin) rfl
  let d₁ : Dependency K A := ⟨left, t.leftAttribute, t.middle.2⟩
  let d₂ : Dependency K A := ⟨right, t.right.2, t.middle.2⟩
  have d₁mem : d₁ ∈ candidates := of_decide_eq_true leftMember
  have d₂mem : d₂ ∈ candidates := of_decide_eq_true rightMember
  let n := i - 1
  have position : n + 1 = i := by have positive := rightPivot.1; dsimp [n]; omega
  have range : n ∈ List.range d₂.path.length := by
    apply List.mem_range.mpr
    have within := rightPivot.2.2.1
    change n < right.length
    omega
  apply List.mem_flatMap.mpr
  refine ⟨d₁, d₁mem, List.mem_flatMap.mpr ⟨d₂, d₂mem, List.mem_filterMap.mpr ⟨n, range, ?_⟩⟩⟩
  dsimp [d₁, d₂]
  rw [position]
  simp only [leftReversed, List.reverse_reverse, rightJoin, rightPivot, true_and, ite_true]

theorem mem_enumerate_representatives (m : Model K A) (candidates : List (Dependency K A))
    (closed : PairClosed m.query candidates)
    (complete : ∀ d, m.trueDependency d = true → d ∈ candidates)
    (sound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d)
    (t : Triple K A) :
    t ∈ enumerateRepresentatives m candidates ↔ Representative m t := by
  classical
  have bridge := candidate_representative_iff m candidates complete sound t
  constructor
  · intro found
    exact bridge.mp (of_decide_eq_true (List.mem_filter.mp found).2)
  · intro triple
    have rep := bridge.mpr triple
    exact List.mem_filter.mpr ⟨representatives_in_raw m candidates closed rep, decide_eq_true rep⟩

/-- Assemble the learner with the finite triple schedule computed from its
own Phase I output. -/
noncomputable def learnWithEnumeration (m : Model K A) (initial : List (Dependency K A))
    (background : ClassFacts A) (rounds : Nat) : List (Dependency K A) × ClassFacts A :=
  learn m initial (enumerateRepresentatives m (adjacencyPhase m initial)) background rounds

theorem learner_with_enumeration_sound (m : Model K A) (initial : List (Dependency K A))
    (background : ClassFacts A) (rounds : Nat)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (faithful : AdjacencyFaithful m) (parentSeparation : CanonicalParentSeparation m initial)
    (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) (symmetric : SymmetricOracle m) :
    let out := learnWithEnumeration m initial background rounds
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      ∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d := by
  let candidates := adjacencyPhase m initial
  have exactPairs d := adjacency_phase_exact m initial acyclic reverseClosed proper faithful
    parentSeparation d
  have pairsSound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d :=
    fun d mem => ((exactPairs d).mp mem).2
  have complete : ∀ d, m.trueDependency d = true → d ∈ candidates :=
    fun d exactD => (exactPairs d).mpr ⟨exhaustive d exactD, .inl exactD⟩
  have closed : PairClosed m.query candidates :=
    search_closed m.query Dependency.reverse_reverse initial reverseClosed (initial.length + 1)
  exact learner_sound m initial _ background rounds acyclic reverseClosed exhaustive proper
    faithful parentSeparation (fun t => (mem_enumerate_representatives m candidates
      closed complete pairsSound t).mp) backgroundSound orientationFaithful symmetric

end RCDLight.Learning

end
