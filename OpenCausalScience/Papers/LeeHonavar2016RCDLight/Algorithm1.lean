module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.OrientationWitness
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.BridgeBurningEnumeration

@[expose] public section

namespace RCDLight.Learning

open RCDPathValidity RelationalFiniteSearch

variable {K A : Type} [DecidableEq K] [DecidableEq A]

/-- RCD-Light with finite bridge-burning filters and full class-rule
propagation after each representative, as in Algorithm 1. -/
noncomputable def learnAlgorithm1 (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (m : Model K A) (classes : List K) (attributes : List A) (h : Nat)
    (background : ClassFacts A) : List (Dependency K A) × ClassFacts A :=
  let initial := boundedDependencies S m.itemClass classes attributes h
  let candidates := adjacencyPhase m initial
  let representatives := bridgeBurningRepresentatives S m.itemClass candidates
  learnInterleaved m initial representatives background (directedCandidates candidates).length

/-- Theorem 1 for the bounded learner that uses the corrected Lemma 5 and
the ground proofs of the two canonical faithfulness properties. -/
theorem algorithm1_sound (S : Schema K) [DecidableRel S.role] [DecidableRel S.many]
    (m : Model K A) {classes : List K} {attributes : List A} (h : Nat) (background : ClassFacts A)
    (coversClasses : ∀ c, c ∈ classes) (coversAttributes : ∀ a, a ∈ attributes)
    (pathSemantics : ∀ p, m.validPath p ↔ HasTerminal S p)
    (typed : m.typedGroundDependencies S) (acyclic : m.acyclic)
    (hopBound : ∀ d, m.trueDependency d = true → d.path.length ≤ h + 1)
    (oracle : GroundOracle m S) (backgroundSound : background.sound m) :
    let initial := boundedDependencies S m.itemClass classes attributes h
    let out := learnAlgorithm1 S m classes attributes h background
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      (∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d) ∧
      classRound (candidateAdjacent (adjacencyPhase m initial)) out.2 = out.2 := by
  let initial := boundedDependencies S m.itemClass classes attributes h
  let candidates := adjacencyPhase m initial
  let representatives := bridgeBurningRepresentatives S m.itemClass candidates
  obtain ⟨closedInitial, exhaustive, proper, _⟩ :=
    bounded_dependencies_learner_inputs S m h coversClasses coversAttributes pathSemantics typed acyclic hopBound
  have faithful := canonical_adjacency_faithfulness_from_ground_oracle typed acyclic oracle
  have parentCI := canonical_parent_separation_from_ground_oracle initial exhaustive acyclic oracle
  have exactPairs d := adjacency_phase_exact m initial acyclic closedInitial proper faithful parentCI d
  have closed : PairClosed m.query candidates :=
    search_closed m.query Dependency.reverse_reverse initial closedInitial (initial.length + 1)
  have complete : ∀ d, m.trueDependency d = true → d ∈ candidates :=
    fun d truth => (exactPairs d).mpr ⟨exhaustive d truth, .inl truth⟩
  have sound : ∀ d ∈ candidates, pairPresent m.query m.trueDependency d :=
    fun d member => ((exactPairs d).mp member).2
  have exactRows (t : Triple K A) : t ∈ representatives ↔ Representative m t := by
    unfold representatives
    rw [bridge_burning_representatives_eq S m pathSemantics candidates]
    exact mem_enumerate_representatives m candidates closed complete sound t
  have orientation := representative_orientation_faithfulness typed (fun p => (pathSemantics p).mp) acyclic oracle
  have proof := learner_interleaved_sound m initial representatives background
    (directedCandidates candidates).length acyclic closedInitial exhaustive proper faithful parentCI
    (fun t => (exactRows t).mp) backgroundSound orientation (symmetric_oracle_from_ground oracle)
  refine ⟨proof.1, proof.2.1, proof.2.2.1, proof.2.2.2, ?_⟩
  have loopFixed (ts : List (Triple K A)) (state : ClassFacts A)
      (fixed : classRound (candidateAdjacent candidates) state = state) :
      let finish := ts.foldl
        (fun facts t => saturateClassRules candidates (orientTriple m candidates facts t)) state
      classRound (candidateAdjacent candidates) finish = finish := by
    induction ts generalizing state with
    | nil => exact fixed
    | cons t next ih =>
      exact ih _ (saturation_fixed candidates (orientTriple m candidates state t))
  exact loopFixed representatives _ (saturation_fixed candidates background)

end RCDLight.Learning

end
