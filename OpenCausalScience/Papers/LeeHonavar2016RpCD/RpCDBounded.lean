module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.CutSchedule
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDCandidatePaths

@[expose] public section

namespace RpCD

open Ground CutSchedule RelationalFiniteSearch

variable {A C : Type} [DecidableEq A] [DecidableEq C] {schema : CutComplete.Schema C}

/-- Well-formed causal models with dependencies of at most the given hop length. -/
def HasHopBound (vocab : AttributeSchema C A) (h : Nat) (M : Model A (List C)) : Prop :=
  ∀ d ∈ M.dependencies, dependencyValid schema vocab d ∧ d.path.length ≤ h + 1

theorem bounded_dependencies {vocab : AttributeSchema C A} {h : Nat}
    {M : Model A (List C)} (valid : HasHopBound (schema := schema) vocab h M)
    {classes : List C} (covers : ∀ c, c ∈ classes) :
    ∀ d ∈ M.dependencies, d ∈ boundedCandidates schema vocab classes h := by
  intro d dc
  refine (mem_boundedCandidates covers).mpr ⟨?_, valid d dc⟩
  intro same
  exact (Nat.lt_irrefl (M.rank d.target)) (same ▸ M.acyclic d dc)

private theorem hop_bound_of_listed {vocab : AttributeSchema C A} {h : Nat}
    {M : Model A (List C)} {classes : List C} (covers : ∀ c, c ∈ classes)
    (included : ∀ d ∈ M.dependencies, d ∈ boundedCandidates schema vocab classes h) :
    HasHopBound (schema := schema) vocab h M := by
  intro d dc
  exact ((mem_boundedCandidates covers).mp (included d dc)).2

/-- The corrected executable learner, from the schema and hop bound to
the learned dependency skeleton and the compelled class directions. -/
def learnBounded (vocab : AttributeSchema C A) (classes : List C) (covers : ∀ c, c ∈ classes)
    (h : Nat) {M : Model A (List C)} (O : Oracle (groundSchema schema vocab) M)
    (bound : HasHopBound (schema := schema) vocab h M) :
    List (Dependency A (List C)) × (A → A → Bool) :=
  correctedRpCD vocab O (boundedCandidates schema vocab classes h)
    (bounded_dependencies bound covers)
    (fun _ h => boundedCandidates_reverse covers h)
    (fun _ h => ((mem_boundedCandidates covers).mp h).1)
    (fun _ h => ((mem_boundedCandidates covers).mp h).2.1)

/-- Soundness and completeness of corrected RpCD under the exact relational
CI oracle, for all legal finite role-free skeletons and hop-bounded models. -/
theorem learnBounded_correct (vocab : AttributeSchema C A) (classes : List C)
    (covers : ∀ c, c ∈ classes) (h : Nat) {M : Model A (List C)}
    (O : Oracle (groundSchema schema vocab) M) (bound : HasHopBound (schema := schema) vocab h M)
    (nodup : vocab.attributes.Nodup) :
    let result := learnBounded vocab classes covers h O bound
    (∀ d, d ∈ result.1 ↔ d ∈ M.dependencies ∨ reverseDependency d ∈ M.dependencies) ∧
    (∀ u v, classAdjacent result.1 u v = true →
      (result.2 u v = true ↔
        ∀ N : Model A (List C), HasHopBound (schema := schema) vocab h N →
          SameRelCI (groundSchema schema vocab) M N → N.classArrow u v)) := by
  have verified := correctedRpCD_correct vocab O (boundedCandidates schema vocab classes h)
    (bounded_dependencies bound covers)
    (fun _ h => boundedCandidates_reverse covers h)
    (fun _ h => ((mem_boundedCandidates covers).mp h).1)
    (fun _ h => ((mem_boundedCandidates covers).mp h).2.1) nodup
  refine ⟨verified.1, fun u v adj => ?_⟩
  simp only [learnBounded]
  rw [verified.2 u v adj]
  exact ⟨fun forallListed N bound same => forallListed N (bounded_dependencies bound covers) same,
    fun forallBound N listed same => forallBound N (hop_bound_of_listed covers listed) same⟩


omit [DecidableEq C] in
private theorem parent_query_detects_pair {S : Type} {B : Schema A (List C) S}
    {M N : Model A (List C)} (L : PathSemantics B)
    {q : Dependency A (List C)} (proper : q.source ≠ q.target) (legal : L.valid q)
    (notInM : q ∉ M.dependencies) (rankOrder : M.rank q.source ≤ M.rank q.target)
    (same : SameRelCI B M N)
    (inN : q ∈ N.dependencies ∨ L.reverse q ∈ N.dependencies) : False := by
  have parentCI := (same q _).mp (parents_separate B M proper.symm rankOrder)
  obtain ⟨s, x, z, hit, isolated⟩ := L.isolate q legal proper
  let pa := parents M q.target
  have leftOut : ∀ p ∈ pa, B.realizes s p x x = false := by
    intro p isParent
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨target, source⟩ := B.types s p x x yes
    have increases := M.acyclic p (List.mem_filter.mp isParent).1
    have sameClass := source.symm.trans target
    simp [sameClass] at increases
  have rightOut : ∀ p ∈ pa, B.realizes s p x z = false := by
    intro p isParent
    apply Bool.eq_false_iff.mpr
    intro yes
    exact notInM ((isolated p yes) ▸ (List.mem_filter.mp isParent).1)
  rcases inN with forward | backward
  · exact adjacent_not_separated B N forward hit (.inl hit) pa leftOut rightOut parentCI
  · have reverseHit : B.realizes s (L.reverse q) z x = true :=
      (L.reverse_realizes s q x z).trans hit
    exact adjacent_not_separated B N backward hit (.inr reverseHit) pa leftOut rightOut parentCI

/-- Equivalence cannot add a dependency path beyond the given hop bound. -/
theorem equivalent_models_share_hop_bound (vocab : AttributeSchema C A) (h : Nat)
    {M N : Model A (List C)} (bound : HasHopBound (schema := schema) vocab h M)
    (legalN : ∀ d ∈ N.dependencies, dependencyValid schema vocab d)
    (same : SameRelCI (groundSchema schema vocab) M N) :
    HasHopBound (schema := schema) vocab h N := by
  let L := concretePathSemantics schema vocab
  intro d member
  have valid := legalN d member
  refine ⟨valid, ?_⟩
  by_cases forward : d ∈ M.dependencies
  · exact (bound d forward).2
  by_cases backward : L.reverse d ∈ M.dependencies
  · simpa [L, concretePathSemantics, reverseDependency] using (bound _ backward).2
  have proper : d.source ≠ d.target := fun equal =>
    (Nat.lt_irrefl (N.rank d.target)) (equal ▸ N.acyclic d member)
  rcases Nat.le_total (M.rank d.source) (M.rank d.target) with earlier | later
  · exact (parent_query_detects_pair L proper valid forward earlier same (.inl member)).elim
  · have type := L.endpoints d
    have properReverse : (L.reverse d).source ≠ (L.reverse d).target := by
      simpa [type.1, type.2] using proper.symm
    have opposite : M.rank (L.reverse d).source ≤ M.rank (L.reverse d).target := by
      simpa [type.1, type.2] using later
    exact (parent_query_detects_pair L properReverse (L.valid_reverse _ valid) backward opposite same
      (.inr (by rw [L.involution]; exact member))).elim

/-- The set of compatible directions is also exact among all well-formed
models agreeing on relational CI, without supplying them a hop bound. -/
theorem learnBounded_correct_all_equivalent (vocab : AttributeSchema C A) (classes : List C)
    (covers : ∀ c, c ∈ classes) (h : Nat) {M : Model A (List C)}
    (O : Oracle (groundSchema schema vocab) M) (bound : HasHopBound (schema := schema) vocab h M)
    (nodup : vocab.attributes.Nodup) :
    let result := learnBounded vocab classes covers h O bound
    (∀ d, d ∈ result.1 ↔ d ∈ M.dependencies ∨ reverseDependency d ∈ M.dependencies) ∧
    (∀ u v, classAdjacent result.1 u v = true →
      (result.2 u v = true ↔
        ∀ N : Model A (List C), (∀ d ∈ N.dependencies, dependencyValid schema vocab d) →
          SameRelCI (groundSchema schema vocab) M N → N.classArrow u v)) := by
  have checked := learnBounded_correct vocab classes covers h O bound nodup
  refine ⟨checked.1, fun u v edge => (checked.2 u v edge).trans ?_⟩
  exact ⟨fun all N valid same => all N (equivalent_models_share_hop_bound vocab h bound valid same) same,
    fun all N boundN same => all N (fun d mem => (boundN d mem).1) same⟩

end RpCD

end
