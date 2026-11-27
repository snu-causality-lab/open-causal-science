module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.IsolatedPath
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RpCDGround

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)
open CutComplete

namespace RpCD

structure AttributeSchema (C A : Type) where
  attributeClass : A → C
  attributes : List A
  covers : ∀ a, a ∈ attributes

structure ItemSkeleton {C : Type} (schema : CutComplete.Schema C) where
  size : Nat
  itemClass : Fin size → C
  edge : Fin size → Fin size → Prop
  decidableEdge : DecidableRel edge
  legal : SkeletonLegal schema itemClass edge

variable {C A : Type} {schema : CutComplete.Schema C}

def uniqueItems [DecidableEq V] : List V → List V
  | [] => []
  | a :: rest =>
    if rest.any (fun b => decide (a = b)) then uniqueItems rest
    else a :: uniqueItems rest

private theorem repeated_item [DecidableEq V] (a : V) (items : List V) :
    items.any (fun b => decide (a = b)) = true ↔ a ∈ items := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨b, mem, eq⟩ => (of_decide_eq_true eq : a = b).symm ▸ mem,
    fun mem => ⟨a, mem, decide_eq_true rfl⟩⟩

theorem mem_uniqueItems [DecidableEq V] {a : V} (items : List V) :
    a ∈ uniqueItems items ↔ a ∈ items := by
  induction items with
  | nil => simp [uniqueItems]
  | cons b rest ih =>
    by_cases same : rest.any (fun c => decide (b = c)) = true
    · rw [uniqueItems, ite_eq_left same, ih]
      exact ⟨List.mem_cons_of_mem b, fun mem => (List.mem_cons.mp mem).elim
        (fun eq => eq.symm ▸ (repeated_item b rest).mp same) id⟩
    · rw [uniqueItems, ite_eq_right same]
      simp [ih]

private theorem nodup_uniqueItems [DecidableEq V] (items : List V) :
    (uniqueItems items).Nodup := by
  induction items with
  | nil => simp [uniqueItems]
  | cons a rest ih =>
    by_cases same : rest.any (fun b => decide (a = b)) = true
    · simpa only [uniqueItems, ite_eq_left same] using ih
    · rw [uniqueItems, ite_eq_right same, List.nodup_cons, mem_uniqueItems]
      exact ⟨fun mem => same ((repeated_item a rest).mpr mem), ih⟩

def variables [DecidableEq A] [DecidableEq C]
    (vocab : AttributeSchema C A) (s : ItemSkeleton schema) : List (Fin s.size × A) :=
  uniqueItems ((List.finRange s.size).flatMap fun i =>
    (vocab.attributes.filter fun a => decide (vocab.attributeClass a = s.itemClass i)).map
      fun a => (i, a))

theorem mem_variables [DecidableEq A] [DecidableEq C] {vocab : AttributeSchema C A}
    {s : ItemSkeleton schema} {i : Fin s.size} {a : A} :
    (i, a) ∈ variables vocab s ↔ vocab.attributeClass a = s.itemClass i := by
  simp [variables, mem_uniqueItems, List.mem_flatMap, List.mem_map, vocab.covers, eq_comm]

def variableAt [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (i : Fin (variables vocab s).length) : Fin s.size × A :=
  (variables vocab s)[i.val]

theorem variableAt_type [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (i : Fin (variables vocab s).length) :
    vocab.attributeClass (variableAt vocab s i).2 = s.itemClass (variableAt vocab s i).1 :=
  mem_variables.mp (List.getElem_mem i.isLt)

theorem variableAt_injective [DecidableEq A] [DecidableEq C] {vocab : AttributeSchema C A}
    {s : ItemSkeleton schema} {i j : Fin (variables vocab s).length}
    (equal : variableAt vocab s i = variableAt vocab s j) : i = j :=
  Fin.ext ((nodup_uniqueItems _).getElem_inj.mp equal)

def variableIndex [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (i : Fin s.size) (a : A)
    (typed : vocab.attributeClass a = s.itemClass i) :
    Fin (variables vocab s).length :=
  ⟨(variables vocab s).idxOf (i, a), List.idxOf_lt_length_iff.mpr (mem_variables.mpr typed)⟩

theorem variableAt_index [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (i : Fin s.size) (a : A)
    (typed : vocab.attributeClass a = s.itemClass i) :
    variableAt vocab s (variableIndex vocab s i a typed) = (i, a) :=
  List.getElem_idxOf _

theorem exists_variableAt [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (i : Fin s.size) (a : A)
    (typed : vocab.attributeClass a = s.itemClass i) :
    ∃ j, variableAt vocab s j = (i, a) :=
  ⟨variableIndex vocab s i a typed, variableAt_index vocab s i a typed⟩

def itemNeighbors (s : ItemSkeleton schema) (a : Fin s.size) : List (Fin s.size) :=
  letI : DecidableRel s.edge := s.decidableEdge
  (List.finRange s.size).filter fun b => decide (s.edge a b)

private theorem itemNeighbors_eq (s : ItemSkeleton schema) :
    (fun a b => b ∈ itemNeighbors s a) = s.edge := by
  funext a b
  apply propext
  simp [itemNeighbors]

def groundRealizes [DecidableEq A] [DecidableEq C] (vocab : AttributeSchema C A)
    (s : ItemSkeleton schema) (d : Ground.Dependency A (List C))
    (x z : Fin (variables vocab s).length) : Bool :=
  let base := variableAt vocab s x
  let other := variableAt vocab s z
  decide (base.2 = d.target ∧ other.2 = d.source) &&
    ExactCUT.realizesLabel (itemNeighbors s) s.itemClass base.1 other.1 d.path

theorem groundRealizes_spec [DecidableEq A] [DecidableEq C] {vocab : AttributeSchema C A}
    {s : ItemSkeleton schema} {d : Ground.Dependency A (List C)}
    {x z : Fin (variables vocab s).length} :
    groundRealizes vocab s d x z = true ↔
      (variableAt vocab s x).2 = d.target ∧ (variableAt vocab s z).2 = d.source ∧
      Realizes s.edge s.itemClass (variableAt vocab s x).1 (variableAt vocab s z).1 d.path := by
  simp only [groundRealizes, Bool.and_eq_true, decide_eq_true_eq, ExactCUT.realizesLabel_spec,
    itemNeighbors_eq, and_assoc]

def groundSchema [DecidableEq A] [DecidableEq C] (schema : CutComplete.Schema C)
    (vocab : AttributeSchema C A) : Ground.Schema A (List C) (ItemSkeleton schema) where
  size s := (variables vocab s).length
  attributeOf s i := (variableAt vocab s i).2
  realizes := groundRealizes vocab
  types _ _ _ _ hit :=
    ⟨(groundRealizes_spec.mp hit).1, (groundRealizes_spec.mp hit).2.1⟩

def packItem [DecidableEq V] (items : List V) (i : Fin (uniqueItems items).length) : V :=
  (uniqueItems items)[i.val]

theorem packItem_injective [DecidableEq V] {items : List V}
    {i j : Fin (uniqueItems items).length} (eq : packItem items i = packItem items j) :
    i = j :=
  Fin.ext ((nodup_uniqueItems items).getElem_inj.mp eq)

def packedIndex [DecidableEq V] (items : List V) (covers : ∀ a, a ∈ items) (a : V) :
    Fin (uniqueItems items).length :=
  ⟨(uniqueItems items).idxOf a, List.idxOf_lt_length_iff.mpr ((mem_uniqueItems items).mpr (covers a))⟩

theorem packItem_index [DecidableEq V] (items : List V) (covers : ∀ a, a ∈ items) (a : V) :
    packItem items (packedIndex items covers a) = a :=
  List.getElem_idxOf _

theorem exists_packItem [DecidableEq V] (items : List V) (covers : ∀ a, a ∈ items) (a : V) :
    ∃ i, packItem items i = a :=
  ⟨packedIndex items covers a, packItem_index items covers a⟩

def pack [DecidableEq V] (items : List V) (covers : ∀ a, a ∈ items)
    (classOf : V → C) (edge : V → V → Prop) [DecidableRel edge]
    (legal : SkeletonLegal schema classOf edge) : ItemSkeleton schema where
  size := (uniqueItems items).length
  itemClass := classOf ∘ packItem items
  edge a b := edge (packItem items a) (packItem items b)
  decidableEdge := fun _ _ => inferInstance
  legal := ⟨coreLegal_of_embedding legal.toCoreLegal (packItem items)
      (fun _ _ => packItem_injective) (fun _ => rfl) (fun _ _ adj => adj)
      (fun adj => legal.symmetric adj), fun a role required => by
        obtain ⟨b, adj, rightClass⟩ := legal.complete (packItem items a) role required
        obtain ⟨j, hj⟩ := exists_packItem items covers b
        exact ⟨j, hj.symm ▸ adj, (congrArg classOf hj).trans rightClass⟩⟩

theorem pack_realizes_iff [DecidableEq V] {items : List V} {covers : ∀ a, a ∈ items}
    {classOf : V → C} {edge : V → V → Prop} [DecidableRel edge]
    {legal : SkeletonLegal schema classOf edge} {a b : Fin (pack items covers classOf edge legal).size}
    {label : List C} :
    Realizes (pack items covers classOf edge legal).edge
      (pack items covers classOf edge legal).itemClass a b label ↔
    Realizes edge classOf (packItem items a) (packItem items b) label := by
  let f := packItem items
  have inj : ∀ a b, f a = f b → a = b := fun _ _ => packItem_injective
  constructor
  · exact ExactCUT.realization_survives_embedding f inj (fun _ _ adj => adj)
  · rintro ⟨pathItems, path, labels⟩
    obtain ⟨preimage, image, candidate, _⟩ := pullback_path (core := fun _ => True)
      (edge := (pack items covers classOf edge legal).edge) f
      (fun a _ next adjacent => by
        obtain ⟨i, rfl⟩ := exists_packItem items covers next
        exact ⟨i, trivial, adjacent, rfl⟩)
      (fun a _ b _ => inj a b) trivial trivial path
    refine ⟨preimage, candidate, ?_⟩
    change preimage.map (classOf ∘ f) = label
    rw [← List.map_map, image]
    exact labels

end RpCD

end
