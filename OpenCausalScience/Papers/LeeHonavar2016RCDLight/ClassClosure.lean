module
public import OpenCausalScience.Papers.LeeHonavar2016RCDLight.GroundOracle

/-! Termination of repeated Figure 3 orientations. Every added class arrow
comes from the finite skeleton learned in Phase I. -/

@[expose] public section

namespace RCDLight.Learning

open RelationalFiniteSearch

variable {K A : Type}

def directedCandidates (candidates : List (Dependency K A)) : List (A × A) :=
  candidates.flatMap fun d => [(d.cause, d.effect), (d.effect, d.cause)]

private theorem candidate_pair_listed {candidates : List (Dependency K A)} {a b : A}
    (adjacent : candidateAdjacent candidates a b) : (a, b) ∈ directedCandidates candidates := by
  obtain ⟨d, mem, sides⟩ := adjacent
  apply List.mem_flatMap.mpr
  rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨d, mem, by simp⟩
  · exact ⟨d, mem, by simp⟩

private theorem class_rule_orients_candidate {adjacent : A → A → Prop} {facts : ClassFacts A}
    {a b : A} (rule : ClassRule adjacent facts a b) : adjacent a b := by
  cases rule with
  | r1 ab _ _ => exact ab.1
  | r2 ab _ _ => exact ab.1
  | r3 ab _ _ _ _ _ => exact ab.1
  | r4 ab _ _ _ _ _ => exact ab.1

private theorem count_monotone {T : Type} {p q : T → Bool}
    (le : ∀ t, p t = true → q t = true) (xs : List T) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons]
    cases hx : p x with
    | true => simp [le x hx, ih]
    | false =>
      cases q x <;> simp <;> omega

private theorem count_strict {T : Type} {p q : T → Bool}
    (le : ∀ t, p t = true → q t = true) {xs : List T} {w : T}
    (listed : w ∈ xs) (notBefore : p w = false) (after : q w = true) :
    xs.countP p < xs.countP q := by
  induction xs with
  | nil => simp at listed
  | cons x xs ih =>
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp listed with rfl | tail
    · have prior := count_monotone le xs
      simp [notBefore, after]
      omega
    · have prior := ih tail
      cases hx : p x with
      | true => simp [le x hx, prior]
      | false => cases q x <;> simp <;> omega

noncomputable def countDirections (candidates : List (Dependency K A)) (facts : ClassFacts A) : Nat :=
  open Classical in (directedCandidates candidates).countP
    (fun pair => decide (facts.directed pair.1 pair.2))

private theorem count_increases_if_changed (candidates : List (Dependency K A))
    (facts : ClassFacts A) (changed : classRound (candidateAdjacent candidates) facts ≠ facts) :
    countDirections candidates facts <
      countDirections candidates (classRound (candidateAdjacent candidates) facts) := by
  classical
  have delta : ∃ a b, ClassRule (candidateAdjacent candidates) facts a b ∧ ¬ facts.directed a b := by
    apply Classical.byContradiction
    intro noNew
    apply changed
    have same : (fun a b => facts.directed a b ∨ ClassRule (candidateAdjacent candidates) facts a b) =
        facts.directed := by
      funext a b
      apply propext
      refine ⟨fun h => h.elim id (fun rule => Classical.byContradiction ?_), Or.inl⟩
      exact fun absent => noNew ⟨a, b, rule, absent⟩
    cases facts
    simp_all [classRound]
  obtain ⟨a, b, rule, absent⟩ := delta
  have added : (classRound (candidateAdjacent candidates) facts).directed a b := .inr rule
  unfold countDirections
  exact count_strict (fun pair h => decide_eq_true (.inl (of_decide_eq_true h)))
    (candidate_pair_listed (class_rule_orients_candidate rule))
    (decide_eq_false_iff_not.mpr absent) (decide_eq_true added)

private theorem count_at_most_pairs (candidates : List (Dependency K A)) (facts : ClassFacts A) :
    countDirections candidates facts ≤ (directedCandidates candidates).length := by
  unfold countDirections
  exact List.countP_le_length

private theorem count_after_unstable_rounds (candidates : List (Dependency K A))
    (facts : ClassFacts A) (rounds : Nat) :
    let adj := candidateAdjacent candidates
    let atRound := classRounds adj rounds facts
    classRound adj atRound ≠ atRound → rounds ≤ countDirections candidates atRound := by
  induction rounds with
  | zero => exact fun _ => Nat.zero_le _
  | succ n ih =>
    dsimp only
    intro future
    let adj := candidateAdjacent candidates
    let prior := classRounds adj n facts
    have unstable : classRound adj prior ≠ prior := by
      intro stable
      apply future
      change classRound adj (classRound adj prior) = classRound adj prior
      rw [stable]
      exact stable
    have increase := count_increases_if_changed candidates prior unstable
    have earlier := ih unstable
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt earlier increase)

def saturateClassRules (candidates : List (Dependency K A)) (facts : ClassFacts A) : ClassFacts A :=
  classRounds (candidateAdjacent candidates) (directedCandidates candidates).length facts

/-- Every configured orientation rule has reached a fixed point after at
most the number of candidate class directions. -/
theorem saturation_fixed (candidates : List (Dependency K A)) (facts : ClassFacts A) :
    classRound (candidateAdjacent candidates) (saturateClassRules candidates facts) =
      saturateClassRules candidates facts := by
  apply Classical.byContradiction
  intro changed
  have prior := count_after_unstable_rounds candidates facts (directedCandidates candidates).length
    changed
  have strict := count_increases_if_changed candidates (saturateClassRules candidates facts) changed
  have bound := count_at_most_pairs candidates
    (classRound (candidateAdjacent candidates) (saturateClassRules candidates facts))
  change (directedCandidates candidates).length ≤
    countDirections candidates (saturateClassRules candidates facts) at prior
  omega

variable [DecidableEq K] [DecidableEq A]

noncomputable def learnToClosure (m : Model K A) (initial : List (Dependency K A))
    (background : ClassFacts A) : List (Dependency K A) × ClassFacts A :=
  let candidates := adjacencyPhase m initial
  learnWithEnumeration m initial background (directedCandidates candidates).length

theorem learner_to_closure_sound {S : RCDPathValidity.Schema K} {m : Model K A}
    (initial : List (Dependency K A)) (background : ClassFacts A)
    (acyclic : m.acyclic) (reverseClosed : PairClosed m.query initial)
    (exhaustive : ∀ d, m.trueDependency d = true → d ∈ initial)
    (proper : ∀ d ∈ initial, d.source ≠ canonical m.itemClass d.effect)
    (oracle : GroundOracle m S) (faithful : AdjacencyFaithful m)
    (backgroundSound : background.sound m)
    (orientationFaithful : OrientationFaithful m) (symmetric : SymmetricOracle m) :
    let out := learnToClosure m initial background
    out.2.sound m ∧
      (∀ d, m.trueDependency d = true → d ∈ out.1) ∧
      (∀ d ∈ out.1, d.reverse ∉ out.1 → m.trueDependency d = true) ∧
      (∀ d, (d ∈ out.1 ∨ d.reverse ∈ out.1) ↔ pairPresent m.query m.trueDependency d) ∧
      classRound (candidateAdjacent (adjacencyPhase m initial)) out.2 = out.2 := by
  have sound := learner_sound_with_ground_separator initial background
    (directedCandidates (adjacencyPhase m initial)).length acyclic reverseClosed exhaustive proper
    oracle faithful backgroundSound orientationFaithful symmetric
  exact ⟨sound.1, sound.2.1, sound.2.2.1, sound.2.2.2, saturation_fixed _ _⟩

end RCDLight.Learning

end
