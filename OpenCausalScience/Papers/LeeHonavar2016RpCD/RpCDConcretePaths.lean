module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDItemSchema
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDPhaseOne

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)
open CutComplete

namespace RpCD

variable {C A : Type} [DecidableEq C] [DecidableEq A]
  {schema : CutComplete.Schema C} {vocab : AttributeSchema C A}

def reverseDependency (d : Ground.Dependency A (List C)) : Ground.Dependency A (List C) :=
  ⟨d.target, d.source, d.path.reverse⟩

theorem groundRealizes_reverse (s : ItemSkeleton schema) (d : Ground.Dependency A (List C))
    (x z : Fin (variables vocab s).length) :
    groundRealizes vocab s (reverseDependency d) z x = groundRealizes vocab s d x z := by
  apply Bool.eq_iff_iff.mpr
  simp only [groundRealizes_spec, reverseDependency,
    realizes_reverse_iff (fun e => s.legal.symmetric e), and_left_comm]

theorem groundRealizes_base {s : ItemSkeleton schema} {d : Ground.Dependency A (List C)}
    {x : Fin (variables vocab s).length} (hit : groundRealizes vocab s d x x = true) :
    d.path = [vocab.attributeClass d.target] := by
  obtain ⟨target, _, realized⟩ := groundRealizes_spec.mp hit
  have eq := variableAt_type vocab s x
  rw [target] at eq
  rw [sameItem_realizes_iff.mp realized, ← eq]

private theorem chain_adjacent {edge : V → V → Prop} {a : V} {tail : List V}
    (chain : Chain edge a tail) (i : Nat) (bound : i + 1 < (a :: tail).length) :
    edge ((a :: tail)[i]'(by omega)) ((a :: tail)[i+1]'bound) := by
  induction tail generalizing a i with
  | nil => simp at bound
  | cons next rest ih =>
    cases i with
    | zero => exact chain.1
    | succ i => exact ih chain.2 i (by simpa using bound)

structure PathSpec (vocab : AttributeSchema C A) (schema : CutComplete.Schema C)
    (d : Ground.Dependency A (List C)) (n : Nat) (classes : Fin (n+1) → C) : Prop where
  labels : (List.finRange (n+1)).map classes = d.path
  valid : ValidPathLabel schema classes
  first : classes 0 = vocab.attributeClass d.target
  last : classes (Fin.last n) = vocab.attributeClass d.source

theorem pathSpec_of_groundRealizes {s : ItemSkeleton schema}
    {d : Ground.Dependency A (List C)} {x z : Fin (variables vocab s).length}
    (hit : groundRealizes vocab s d x z = true) :
    ∃ n classes, PathSpec vocab schema d n classes := by
  obtain ⟨target, source, items, path, labels⟩ := groundRealizes_spec.mp hit
  let a := (variableAt vocab s x).1
  change Path s.edge a (variableAt vocab s z).1 items at path
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp path.1
  let f (i : Fin (tail.length+1)) : Fin s.size := (a :: tail)[i.val]'(by simp)
  let classes := s.itemClass ∘ f
  have representation : List.ofFn f = a :: tail := @List.ofFn_getElem _ (a :: tail)
  have preserve {i j : Fin (tail.length+1)} (direction : j.val = i.val+1) :
      s.edge (f i) (f j) := by
    have bound : i.val+1 < tail.length+1 := by omega
    have after : (⟨i.val+1, bound⟩ : Fin (tail.length+1)) = j := Fin.ext direction.symm
    have adj : s.edge (f i) (f ⟨i.val+1, bound⟩) :=
      chain_adjacent path.2.2.2 i.val (by simpa using bound)
    rw [after] at adj
    exact adj
  have firstType := variableAt_type vocab s x
  have lastType := variableAt_type vocab s z
  rw [target] at firstType
  rw [source] at lastType
  refine ⟨tail.length, classes, ⟨?_, ⟨?_, ?_⟩, firstType.symm, ?_⟩⟩
  · change (List.ofFn id).map (s.itemClass ∘ f) = d.path
    rw [← List.map_map, List.map_ofFn]
    change (List.ofFn f).map s.itemClass = d.path
    rw [representation]
    exact labels
  · intro i j next
    exact s.legal.typed (preserve next)
  · intro i j k forward backward equal unique
    have same := s.legal.unique (preserve forward) (s.legal.symmetric (preserve backward))
      equal unique
    have nodup : (List.ofFn f).Nodup := by rw [representation]; exact path.2.2.1
    have indices := congrArg Fin.val (injective_ofFn_nodup nodup same)
    omega
  · have dest := path.2.1
    rw [List.getLast?_eq_getElem?] at dest
    have bound : (a :: tail).length - 1 < (a :: tail).length := by simp
    rw [List.getElem?_eq_getElem bound] at dest
    have eq : f (Fin.last tail.length) = (variableAt vocab s z).1 :=
      Option.some.inj dest
    exact (congrArg s.itemClass eq).trans lastType.symm

theorem isolate_dependency_of_pathSpec {d : Ground.Dependency A (List C)}
    {n : Nat} {classes : Fin (n+1) → C} (valid : PathSpec vocab schema d n classes) :
    ∃ (s : ItemSkeleton schema) (x z : Fin (variables vocab s).length),
      groundRealizes vocab s d x z = true ∧
      ∀ q, groundRealizes vocab s q x z = true → q = d := by
  let line := lineEdge (n+1)
  let classOf := completionClass schema classes line
  let edge := completionEdge schema classes line
  haveI : DecidableRel line := inferInstanceAs (DecidableRel (lineEdge (n+1)))
  haveI : DecidableRel edge := inferInstanceAs (DecidableRel (completionEdge schema classes line))
  obtain ⟨legal, isolated⟩ := isolate_path_label valid.valid
  let items := completionItems schema classes line (List.finRange (n+1)) List.mem_finRange
  let covers := mem_completionItems (schema := schema) (classOf := classes)
    (edge := line) List.mem_finRange
  let s := pack items covers classOf edge legal
  let h : Fin s.size := packedIndex items covers (.inl 0)
  let t : Fin s.size := packedIndex items covers (.inl (Fin.last n))
  have headIndex : packItem items h = .inl 0 := packItem_index items covers _
  have tailIndex : packItem items t = .inl (Fin.last n) := packItem_index items covers _
  have headType : vocab.attributeClass d.target = s.itemClass h := by
    change _ = classOf (packItem items h)
    rw [headIndex]
    exact valid.first.symm
  have tailType : vocab.attributeClass d.source = s.itemClass t := by
    change _ = classOf (packItem items t)
    rw [tailIndex]
    exact valid.last.symm
  let x := variableIndex vocab s h d.target headType
  let z := variableIndex vocab s t d.source tailType
  have variableX : variableAt vocab s x = (h, d.target) :=
    variableAt_index vocab s h d.target headType
  have variableZ : variableAt vocab s z = (t, d.source) :=
    variableAt_index vocab s t d.source tailType
  have only (label : List C) :
      Realizes s.edge s.itemClass h t label ↔ label = d.path := by
    change Realizes (pack items covers classOf edge legal).edge
      (pack items covers classOf edge legal).itemClass h t label ↔ label = d.path
    rw [pack_realizes_iff, headIndex, tailIndex, ← valid.labels]
    exact isolated label
  refine ⟨s, x, z, groundRealizes_spec.mpr ?_, ?_⟩
  · rw [variableX, variableZ]
    exact ⟨rfl, rfl, (only d.path).mpr rfl⟩
  · intro q hit
    obtain ⟨target, source, realized⟩ := groundRealizes_spec.mp hit
    rw [variableX] at target realized
    rw [variableZ] at source realized
    have sameLabels := (only q.path).mp realized
    cases q
    cases d
    simp_all

/-- A valid dependency is realizable in some finite legal skeleton with its
specified endpoint attributes. The equivalent local criterion is PathSpec. -/
def dependencyValid (schema : CutComplete.Schema C) (vocab : AttributeSchema C A)
    (d : Ground.Dependency A (List C)) : Prop :=
  ∃ (s : ItemSkeleton schema) (x z : Fin (variables vocab s).length),
    groundRealizes vocab s d x z = true

theorem dependencyValid_iff_pathSpec {d : Ground.Dependency A (List C)} :
    dependencyValid schema vocab d ↔ ∃ n classes, PathSpec vocab schema d n classes := by
  constructor
  · rintro ⟨_, _, _, hit⟩
    exact pathSpec_of_groundRealizes hit
  · rintro ⟨_, _, spec⟩
    obtain ⟨s, x, z, hit, _⟩ := isolate_dependency_of_pathSpec spec
    exact ⟨s, x, z, hit⟩

def concretePathSemantics (schema : CutComplete.Schema C) (vocab : AttributeSchema C A) :
    PathSemantics (groundSchema schema vocab) where
  canonical a := [vocab.attributeClass a]
  reverse := reverseDependency
  involution d := by cases d; simp [reverseDependency]
  endpoints _ := ⟨rfl, rfl⟩
  reverse_realizes := groundRealizes_reverse (vocab := vocab)
  base_identity _ _ _ := groundRealizes_base
  valid := dependencyValid schema vocab
  valid_reverse d h := by
    obtain ⟨s, x, z, hit⟩ := h
    exact ⟨s, z, x, (groundRealizes_reverse s d x z).trans hit⟩
  isolate _ h _ := by
    obtain ⟨_, _, localRule⟩ := dependencyValid_iff_pathSpec.mp h
    exact isolate_dependency_of_pathSpec localRule

end RpCD

end
