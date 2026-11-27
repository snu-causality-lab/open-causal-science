module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDConcretePaths

@[expose] public section

open CutComplete

namespace RpCD

variable {C A : Type}

instance [DecidableEq C] (schema : CutComplete.Schema C) (classes : Fin n → C) :
    Decidable (ValidPathLabel schema classes) := by
  letI (a b : C) : Decidable (TypedIncidence schema a b) := by
    unfold TypedIncidence
    infer_instance
  letI (a b : C) : Decidable (AtMostOne schema a b) := by
    unfold AtMostOne
    infer_instance
  apply decidable_of_iff
    ((∀ a b : Fin n, b.val = a.val+1 → TypedIncidence schema (classes a) (classes b)) ∧
      (∀ a b c : Fin n, b.val = a.val+1 → a.val = c.val+1 → classes b = classes c →
        ¬ AtMostOne schema (classes a) (classes b)))
  exact ⟨fun ⟨typed, localRule⟩ => ⟨typed _ _, localRule _ _ _⟩,
    fun valid => ⟨fun _ _ => valid.typed, fun _ _ _ => valid.localRule⟩⟩

def wordClass (word : List C) (length : word.length = n+1) (i : Fin (n+1)) : C :=
  word[i.val]'(length.symm ▸ i.isLt)

private theorem wordClass_list (word : List C) (length : word.length = n+1) :
    (List.finRange (n+1)).map (wordClass word length) = word := by
  change (List.ofFn id).map (wordClass word length) = word
  rw [List.map_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, length]
  · intro i bound _
    rw [List.getElem_ofFn bound]
    rfl

private theorem matching_class_words {c d : Fin n → C}
    (same : (List.finRange n).map c = (List.finRange n).map d) : c = d := by
  change (List.ofFn id).map c = (List.ofFn id).map d at same
  simp only [List.map_ofFn] at same
  funext i
  have equal := congrArg (fun xs : List C => xs[i.val]?) same
  simpa only [List.getElem?_ofFn, i.isLt, dite_true, Function.comp_apply,
    id_eq, Option.some.injEq] using equal

variable [DecidableEq C] [DecidableEq A]

def withAttributes (vocab : AttributeSchema C A) (word : List C)
    (first last : C) : List (Ground.Dependency A (List C)) :=
  vocab.attributes.flatMap fun source =>
    vocab.attributes.filterMap fun target =>
      if source ≠ target ∧ vocab.attributeClass target = first ∧
          vocab.attributeClass source = last then
        some ⟨source, target, word⟩
      else none

private theorem mem_withAttributes {vocab : AttributeSchema C A} {word : List C}
    {first last : C} {d : Ground.Dependency A (List C)} :
    d ∈ withAttributes vocab word first last ↔
      d.path = word ∧ d.source ≠ d.target ∧
      vocab.attributeClass d.target = first ∧ vocab.attributeClass d.source = last := by
  rw [withAttributes, List.mem_flatMap]
  constructor
  · rintro ⟨source, _, found⟩
    obtain ⟨target, _, eq⟩ := List.mem_filterMap.mp found
    split at eq
    · rename_i accepted
      cases Option.some.inj eq
      exact ⟨rfl, accepted⟩
    · contradiction
  · rintro ⟨rfl, different, atFirst, atLast⟩
    refine ⟨d.source, vocab.covers _, List.mem_filterMap.mpr ⟨d.target, vocab.covers _, ?_⟩⟩
    rw [ite_eq_left ⟨different, atFirst, atLast⟩]

def candidatesOfLength (schema : CutComplete.Schema C) (vocab : AttributeSchema C A)
    (classes : List C) (n : Nat) : List (Ground.Dependency A (List C)) :=
  (listsOfLength classes (n+1)).attach.flatMap fun word =>
    let letters := wordClass word.val (mem_listsOfLength.mp word.property).1
    if ValidPathLabel schema letters then
      withAttributes vocab word.val (letters 0) (letters (Fin.last n))
    else []

private theorem mem_candidatesOfLength {schema : CutComplete.Schema C} {vocab : AttributeSchema C A}
    {classes : List C} (covers : ∀ c, c ∈ classes) {n : Nat}
    {d : Ground.Dependency A (List C)} :
    d ∈ candidatesOfLength schema vocab classes n ↔
      d.source ≠ d.target ∧ ∃ letters, PathSpec vocab schema d n letters := by
  unfold candidatesOfLength
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨word, listed⟩, _, inside⟩
    let letters := wordClass word (mem_listsOfLength.mp listed).1
    change d ∈ (if ValidPathLabel schema letters then
      withAttributes vocab word (letters 0) (letters (Fin.last n)) else []) at inside
    split at inside
    · rename_i valid
      obtain ⟨pathEqual, different, first, last⟩ := mem_withAttributes.mp inside
      exact ⟨different, letters, (wordClass_list word _).trans pathEqual.symm, valid, first.symm, last.symm⟩
    · simp at inside
  · rintro ⟨different, letters, spec⟩
    have wordLength : d.path.length = n+1 := by rw [← spec.labels]; simp
    have listed : d.path ∈ listsOfLength classes (n+1) :=
      mem_listsOfLength.mpr ⟨wordLength, fun c _ => covers c⟩
    refine ⟨⟨d.path, listed⟩, List.mem_attach .., ?_⟩
    let classesFromWord := wordClass d.path wordLength
    have equal : classesFromWord = letters :=
      matching_class_words ((wordClass_list d.path wordLength).trans spec.labels.symm)
    change d ∈ (if ValidPathLabel schema classesFromWord then
      withAttributes vocab d.path (classesFromWord 0) (classesFromWord (Fin.last n)) else [])
    rw [equal, ite_eq_left spec.valid]
    exact mem_withAttributes.mpr ⟨rfl, different, spec.first.symm, spec.last.symm⟩

/-- All well-typed dependencies of at most the specified hop count, in both directions. -/
def boundedCandidates (schema : CutComplete.Schema C) (vocab : AttributeSchema C A)
    (classes : List C) (maximumHops : Nat) : List (Ground.Dependency A (List C)) :=
  (List.range (maximumHops+1)).flatMap (candidatesOfLength schema vocab classes)

theorem mem_boundedCandidates {schema : CutComplete.Schema C} {vocab : AttributeSchema C A}
    {classes : List C} (covers : ∀ c, c ∈ classes) {maximumHops : Nat}
    {d : Ground.Dependency A (List C)} :
    d ∈ boundedCandidates schema vocab classes maximumHops ↔
      d.source ≠ d.target ∧ dependencyValid schema vocab d ∧ d.path.length ≤ maximumHops+1 := by
  rw [boundedCandidates, List.mem_flatMap]
  constructor
  · rintro ⟨n, inRange, listed⟩
    obtain ⟨different, letters, spec⟩ := (mem_candidatesOfLength covers).mp listed
    refine ⟨different, dependencyValid_iff_pathSpec.mpr ⟨n, letters, spec⟩, ?_⟩
    rw [← spec.labels, List.length_map, List.length_finRange]
    have bound := List.mem_range.mp inRange
    omega
  · rintro ⟨different, valid, bound⟩
    obtain ⟨n, letters, spec⟩ := dependencyValid_iff_pathSpec.mp valid
    refine ⟨n, List.mem_range.mpr ?_, (mem_candidatesOfLength covers).mpr ⟨different, letters, spec⟩⟩
    rw [← spec.labels, List.length_map, List.length_finRange] at bound
    omega

theorem boundedCandidates_reverse {schema : CutComplete.Schema C} {vocab : AttributeSchema C A}
    {classes : List C} (covers : ∀ c, c ∈ classes) {maximumHops : Nat}
    {d : Ground.Dependency A (List C)} (listed : d ∈ boundedCandidates schema vocab classes maximumHops) :
    reverseDependency d ∈ boundedCandidates schema vocab classes maximumHops := by
  obtain ⟨different, valid, bound⟩ := (mem_boundedCandidates covers).mp listed
  apply (mem_boundedCandidates covers).mpr
  refine ⟨Ne.symm different, (concretePathSemantics schema vocab).valid_reverse d valid, ?_⟩
  simpa [reverseDependency] using bound

end RpCD

end
