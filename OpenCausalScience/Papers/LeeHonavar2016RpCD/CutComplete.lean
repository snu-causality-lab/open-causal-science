module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.CutCore

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)

namespace CutComplete

/-- The role-free schema and upper-cardinality conventions of the reference construction.
The list of roles specifies one required participant per listed entity class. -/
structure Schema (C : Type u) where
  relationship : C → Bool
  roles : C → List C
  entityOne : C → C → Bool
  roleTypes : ∀ {r e}, e ∈ roles r → relationship r = true ∧ relationship e = false

def TypedIncidence (schema : Schema C) (a b : C) : Prop :=
  b ∈ schema.roles a ∨ a ∈ schema.roles b

def AtMostOne (schema : Schema C) (a b : C) : Prop :=
  schema.relationship a = true ∨ schema.entityOne a b = true

structure CoreLegal (schema : Schema C) (classOf : V → C) (edge : V → V → Prop) : Prop where
  symmetric : ∀ {a b}, edge a b → edge b a
  typed : ∀ {a b}, edge a b → TypedIncidence schema (classOf a) (classOf b)
  unique : ∀ {a b c}, edge a b → edge a c → classOf b = classOf c →
    AtMostOne schema (classOf a) (classOf b) → b = c

structure SkeletonLegal (schema : Schema C) (classOf : V → C) (edge : V → V → Prop)
    : Prop extends CoreLegal schema classOf edge where
  complete : ∀ a role, role ∈ schema.roles (classOf a) → ∃ b, edge a b ∧ classOf b = role

theorem coreLegal_of_embedding {schema : Schema C} {classOf : V → C}
    {edge : V → V → Prop} {coreClass : U → C} {core : U → U → Prop}
    (legal : CoreLegal schema classOf edge) (f : U → V)
    (inj : ∀ a b, f a = f b → a = b)
    (typed : ∀ a, classOf (f a) = coreClass a)
    (mapEdge : ∀ a b, core a b → edge (f a) (f b))
    (symmetric : ∀ {a b}, core a b → core b a) :
    CoreLegal schema coreClass core := by
  refine ⟨symmetric, ?_, ?_⟩
  · intro a b adj
    simpa only [typed] using legal.typed (mapEdge a b adj)
  · intro a b c ab ac sameClass one
    exact inj _ _ (legal.unique (mapEdge a b ab) (mapEdge a c ac)
      (by simpa only [typed]) (by simpa only [typed]))

def MissingRole (schema : Schema C) (classOf : V → C) (edge : V → V → Prop) :=
  { role : V × C // role.2 ∈ schema.roles (classOf role.1) ∧
    ¬ ∃ b, edge role.1 b ∧ classOf b = role.2 }

abbrev Completed (schema : Schema C) (classOf : V → C) (edge : V → V → Prop) :=
  V ⊕ MissingRole schema classOf edge

instance [DecidableEq V] [DecidableEq C] (schema : Schema C)
    (classOf : V → C) (edge : V → V → Prop) : DecidableEq (MissingRole schema classOf edge) :=
  fun a b => if h : a.val = b.val then isTrue (Subtype.ext h)
    else isFalse (fun eq => h (congrArg Subtype.val eq))

def completionEdge (schema : Schema C) (classOf : V → C) (edge : V → V → Prop) :
    Completed schema classOf edge → Completed schema classOf edge → Prop :=
  addLeaves edge (fun leaf => leaf.val.1)

instance [DecidableEq V] (schema : Schema C) (classOf : V → C)
    (edge : V → V → Prop) [DecidableRel edge] :
    DecidableRel (completionEdge schema classOf edge) := by
  intro a b
  cases a <;> cases b <;> unfold completionEdge addLeaves <;> infer_instance

def completionClass (schema : Schema C) (classOf : V → C) (edge : V → V → Prop) :
    Completed schema classOf edge → C :=
  Sum.elim classOf (fun leaf => leaf.val.2)

theorem legal_completion {schema : Schema C} {classOf : V → C} {edge : V → V → Prop}
    (h : CoreLegal schema classOf edge) :
    SkeletonLegal schema (completionClass schema classOf edge)
      (completionEdge schema classOf edge) := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b adj
    cases a <;> cases b
    · exact h.symmetric adj
    · exact adj
    · exact adj
    · exact adj
  · intro a b adj
    cases a with
    | inl a =>
      cases b with
      | inl b => exact h.typed adj
      | inr b =>
        have eq : b.val.1 = a := adj
        exact Or.inl (eq ▸ b.property.1)
    | inr a =>
      cases b with
      | inl b =>
        have eq : a.val.1 = b := adj
        exact Or.inr (eq ▸ a.property.1)
      | inr b => exact adj.elim
  · intro a b c ab ac sameClass one
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases c with
        | inl c => exact congrArg Sum.inl (h.unique ab ac sameClass one)
        | inr c =>
          have eq : c.val.1 = a := ac
          exact (c.property.2 ⟨b, eq.symm ▸ ab, sameClass⟩).elim
      | inr b =>
        cases c with
        | inl c =>
          have eq : b.val.1 = a := ab
          exact (b.property.2 ⟨c, eq.symm ▸ ac, sameClass.symm⟩).elim
        | inr c =>
          have left : b.val.1 = a := ab
          have right : c.val.1 = a := ac
          exact congrArg Sum.inr (Subtype.ext (Prod.ext (left.trans right.symm) sameClass))
    | inr a =>
      cases b with
      | inr b => exact ab.elim
      | inl b =>
        cases c with
        | inr c => exact ac.elim
        | inl c =>
          have left : a.val.1 = b := ab
          have right : a.val.1 = c := ac
          exact congrArg Sum.inl (left.symm.trans right)
  · intro a role required
    cases a with
    | inl a =>
      change role ∈ schema.roles (classOf a) at required
      by_cases filled : ∃ b, edge a b ∧ classOf b = role
      · obtain ⟨b, adj, label⟩ := filled
        exact ⟨.inl b, adj, label⟩
      · exact ⟨.inr ⟨(a, role), required, filled⟩, rfl, rfl⟩
    | inr leaf =>
      have isEntity := (schema.roleTypes leaf.property.1).2
      have isRelationship : schema.relationship leaf.val.2 = true :=
        (schema.roleTypes required).1
      simp [isEntity] at isRelationship

theorem realization_completion_iff {schema : Schema C} {classOf : V → C}
    {edge : V → V → Prop} {a b : V} {label : List C} :
    Realizes (completionEdge schema classOf edge) (completionClass schema classOf edge)
      (.inl a) (.inl b) label ↔ Realizes edge classOf a b label := by
  constructor
  · intro h
    exact ExactCUT.completed_core_realizes_only_original_labels
      (core := edge) (ambient := edge) (classOf := classOf)
      (attach := fun (leaf : MissingRole schema classOf edge) => leaf.val.1) id
      (fun _ _ equal => equal) (fun _ _ adj => adj) (fun leaf => leaf.val.2) h
  · intro h
    exact ExactCUT.realization_survives_embedding (core := edge)
      (ambient := completionEdge schema classOf edge)
      (classOf := completionClass schema classOf edge) Sum.inl
      (fun _ _ => Sum.inl.inj) (fun _ _ adj => adj) h

def unshielded [DecidableEq C] (classOf : CoreItem code n → C)
    (a b : CoreItem code n) (queries : List (List C)) : Bool :=
  !(queries.any (ExactCUT.realizesLabel (neighbors code n) classOf a b))

theorem unshielded_spec [DecidableEq C] {classOf : CoreItem code n → C}
    {a b : CoreItem code n} {queries : List (List C)} :
    unshielded classOf a b queries = true ↔
    ∀ label ∈ queries, ¬ Realizes (coreEdge code n) classOf a b label := by
  have sameEdges : (fun (x y : CoreItem code n) => y ∈ neighbors code n x) =
      coreEdge code n := by
    funext x y
    exact propext mem_neighbors
  unfold unshielded
  rw [Bool.not_eq_true', ← Bool.not_eq_true, ExactCUT.any_label_spec, sameEdges]
  simp

private theorem neighbors_edge_eq (code : MatchingCode m) (n : Nat) :
    (fun (a b : CoreItem code n) => b ∈ neighbors code n a) = coreEdge code n := by
  funext a b
  exact propext mem_neighbors

def labelsBetween [BEq C] [LawfulBEq C] (classOf : CoreItem code n → C)
    (a b : CoreItem code n) : List (List C) :=
  pathLabels (neighbors code n) classOf (coreItems code n).length a b

theorem labelsBetween_spec [BEq C] [LawfulBEq C] {classOf : CoreItem code n → C}
    {a b : CoreItem code n} {label : List C} :
    label ∈ labelsBetween classOf a b ↔ Realizes (coreEdge code n) classOf a b label := by
  rw [labelsBetween, mem_pathLabels, neighbors_edge_eq]
  exact ⟨fun ⟨items, path, _, classes⟩ => ⟨items, path, classes⟩,
    fun ⟨items, path, classes⟩ => ⟨items, path,
      path.2.2.1.length_le_of_subset (fun {_} _ => mem_coreItems _), classes⟩⟩

private theorem path_suffix {edge : V → V → Prop} {a b c : V} {items : List V}
    (path : Path edge a b items) (inPath : c ∈ items) :
    ∃ suffix, Path edge c b suffix := by
  induction items generalizing a with
  | nil => simp at inPath
  | cons here tail ih =>
    have eq : here = a := Option.some.inj path.1
    subst here
    rcases List.mem_cons.mp inPath with rfl | h
    · exact ⟨_, path⟩
    · cases tail with
      | nil => simp at h
      | cons next rest =>
        exact ih ⟨rfl, path.2.1, (List.nodup_cons.mp path.2.2.1).2, path.2.2.2.2⟩ h

private theorem path_after_chain {edge : V → V → Prop} {a b c : V} {tail items : List V}
    (chain : Chain edge a tail) (last : (a :: tail).getLast? = some b)
    (path : Path edge b c items) :
    ∃ joined, Path edge a c joined := by
  classical
  induction tail generalizing a with
  | nil =>
    have eq : a = b := Option.some.inj last
    subst b
    exact ⟨items, path⟩
  | cons next rest ih =>
    obtain ⟨suffix, good⟩ := ih chain.2 (by simpa using last)
    by_cases already : a ∈ suffix
    · exact path_suffix good already
    · obtain ⟨remaining, rfl⟩ := List.head?_eq_some_iff.mp good.1
      exact ⟨a :: next :: remaining, rfl, good.2.1,
        List.nodup_cons.mpr ⟨already, good.2.2.1⟩, chain.1, good.2.2.2⟩

theorem path_between_joined {edge : V → V → Prop} {a b c : V} {p q : List V}
    (left : Path edge a b p) (right : Path edge b c q) :
    ∃ joined, Path edge a c joined := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp left.1
  exact path_after_chain left.2.2.2 left.2.1 right

def legalCore [DecidableEq C] (schema : Schema C) (classOf : CoreItem code n → C) : Bool :=
  (coreItems code n).all fun a =>
    (neighbors code n a).all fun b =>
      decide (classOf b ∈ schema.roles (classOf a) ∨ classOf a ∈ schema.roles (classOf b)) &&
      (neighbors code n a).all fun c =>
        decide (classOf b = classOf c →
          (schema.relationship (classOf a) = true ∨
            schema.entityOne (classOf a) (classOf b) = true) → b = c)

theorem legalCore_spec [DecidableEq C] {schema : Schema C} {classOf : CoreItem code n → C} :
    legalCore schema classOf = true ↔ CoreLegal schema classOf (coreEdge code n) := by
  simp only [legalCore, List.all_eq_true, mem_coreItems, true_implies, mem_neighbors,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨core_symmetric, fun ab => (h _ _ ab).1, fun ab ac eq one => (h _ _ ab).2 _ ac eq one⟩
  · intro h a b ab
    exact ⟨h.typed ab, fun _ ac => h.unique ab ac⟩

structure Inputs (C : Type u) (A : Type v) (m n : Nat) where
  pClass : Fin (m+1) → C
  qClass : Fin (n+1) → C
  x : A
  y : A
  z : A
  shields : List (List C)

def distinctVariables (a b c : V) (x y z : A) : Prop :=
  (a, x) ≠ (b, y) ∧ (b, y) ≠ (c, z) ∧ (a, x) ≠ (c, z)

instance [DecidableEq V] [DecidableEq A] (a b c : V) (x y z : A) :
    Decidable (distinctVariables a b c x y z) := by
  unfold distinctVariables
  infer_instance

theorem distinctVariables_of_image (f : V → W) {a b c : V} {x y z : A}
    (h : distinctVariables (f a) (f b) (f c) x y z) :
    distinctVariables a b c x y z := by
  let lift (v : V × A) := (f v.1, v.2)
  exact ⟨fun same => h.1 (congrArg lift same), fun same => h.2.1 (congrArg lift same),
    fun same => h.2.2 (congrArg lift same)⟩

/-- Retain a legal partial skeleton with three distinct variables and no X-Z dependency label.
The shields input lists all X-Z dependency paths in X's perspective. -/
def acceptedCodes [DecidableEq C] [DecidableEq A] (schema : Schema C)
    (input : Inputs C A m n) : List (MatchingCode (m+1)) :=
  (validCodes input.pClass input.qClass (Fin.last m) 0).filter fun code =>
    let a : CoreItem code (n+1) := pSlot code 0
    let b : CoreItem code (n+1) := pSlot code (Fin.last m)
    let c := qSlot code (Fin.last n)
    legalCore (code := code) schema (coreClass input.pClass input.qClass) &&
      decide (distinctVariables a b c input.x input.y input.z) &&
      unshielded (coreClass input.pClass input.qClass) a c input.shields

theorem mem_acceptedCodes_iff [DecidableEq C] [DecidableEq A] {schema : Schema C}
    {input : Inputs C A m n} {code : MatchingCode (m+1)} :
    code ∈ acceptedCodes schema input ↔
      code ∈ validCodes input.pClass input.qClass (Fin.last m) 0 ∧
      CoreLegal schema (coreClass input.pClass input.qClass) (coreEdge code (n+1)) ∧
      distinctVariables (pSlot code 0) (pSlot code (Fin.last m)) (qSlot code (Fin.last n))
        input.x input.y input.z ∧
      ∀ label ∈ input.shields,
        ¬ Realizes (coreEdge code (n+1)) (coreClass input.pClass input.qClass)
          (pSlot code 0) (qSlot code (Fin.last n)) label := by
  simp only [acceptedCodes, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    legalCore_spec, unshielded_spec, and_assoc]

structure GroundWitness (input : Inputs C A m n) (classOf : V → C)
    (edge : V → V → Prop) (pItems : Fin (m+1) → V) (qItems : Fin (n+1) → V) : Prop where
  pPath : Path edge (pItems 0) (pItems (Fin.last m)) (List.ofFn pItems)
  qPath : Path edge (qItems 0) (qItems (Fin.last n)) (List.ofFn qItems)
  typedP : ∀ i, classOf (pItems i) = input.pClass i
  typedQ : ∀ i, classOf (qItems i) = input.qClass i
  sameMiddle : pItems (Fin.last m) = qItems 0
  distinct : distinctVariables (pItems 0) (pItems (Fin.last m)) (qItems (Fin.last n))
    input.x input.y input.z
  notShielded : ∀ label ∈ input.shields,
    ¬ Realizes edge classOf (pItems 0) (qItems (Fin.last n)) label

theorem groundWitness_accepts [DecidableEq C] [DecidableEq A] [DecidableEq V]
    {schema : Schema C} {input : Inputs C A m n} {edge : V → V → Prop} {classOf : V → C}
    {pItems : Fin (m+1) → V} {qItems : Fin (n+1) → V}
    (legal : SkeletonLegal schema classOf edge)
    (ground : GroundWitness input classOf edge pItems qItems) :
    witnessCode pItems qItems ∈ acceptedCodes schema input := by
  let code := witnessCode pItems qItems
  let core := coreClass input.pClass input.qClass (code := code)
  let f := embed pItems qItems (code := code)
  have injP {i j} := injective_ofFn_nodup ground.pPath.2.2.1 (i := i) (j := j)
  have injQ {i j} := injective_ofFn_nodup ground.qPath.2.2.1 (i := i) (j := j)
  have inj := injective_embed injP injQ
  have labels : ∀ a, classOf (f a) = core a :=
    class_embed _ _ _ ground.typedP ground.typedQ
  have adj (a b) : coreEdge code (n+1) a b → edge (f a) (f b) :=
    mapped_edge legal.symmetric injP ground.pPath ground.qPath
  apply mem_acceptedCodes_iff.mpr
  refine ⟨witnessCode_in_validCodes classOf injP injQ ground.typedP ground.typedQ
    ground.sameMiddle, coreLegal_of_embedding legal.toCoreLegal f inj labels adj core_symmetric,
    ?_, ?_⟩
  · apply distinctVariables_of_image f
    change distinctVariables (pItems 0) (pItems (Fin.last m)) (f (qSlot code (Fin.last n)))
      input.x input.y input.z
    rw [show f (qSlot code (Fin.last n)) = qItems (Fin.last n) from embed_qSlot injP _]
    exact ground.distinct
  · intro label shielding realized
    apply ground.notShielded label shielding
    have classes : core = classOf ∘ f := funext (fun a => (labels a).symm)
    change Realizes (coreEdge code (n+1)) core (pSlot code 0) (qSlot code (Fin.last n))
      label at realized
    rw [classes] at realized
    have original := ExactCUT.realization_survives_embedding f inj adj realized
    rw [show f (qSlot code (Fin.last n)) = qItems (Fin.last n) from embed_qSlot injP _] at original
    exact original

def roleOccupied [DecidableEq C] (edge : V → V → Prop) [DecidableRel edge]
    (items : List V) (classOf : V → C) (a : V) (role : C) : Bool :=
  items.any fun b => decide (edge a b ∧ classOf b = role)

theorem roleOccupied_spec [DecidableEq C] {edge : V → V → Prop} [DecidableRel edge]
    {items : List V} (covers : ∀ a, a ∈ items) {classOf : V → C} {a : V} {role : C} :
    roleOccupied edge items classOf a role = false ↔ ¬ ∃ b, edge a b ∧ classOf b = role := by
  rw [← Bool.not_eq_true]
  simp [roleOccupied, List.any_eq_true, covers]

/-- Concrete item list of the canonical completion, including the fresh participants. -/
def completionItems [DecidableEq C] (schema : Schema C) (classOf : V → C)
    (edge : V → V → Prop) [DecidableRel edge] (items : List V) (covers : ∀ a, a ∈ items) :
    List (Completed schema classOf edge) :=
  items.map Sum.inl ++ items.flatMap fun a =>
    (schema.roles (classOf a)).attach.filterMap fun role =>
      if missing : roleOccupied edge items classOf a role.val = false then
        some (.inr ⟨(a, role.val), role.property, (roleOccupied_spec covers).mp missing⟩)
      else none

theorem mem_completionItems [DecidableEq C] {schema : Schema C}
    {classOf : V → C} {edge : V → V → Prop} [DecidableRel edge]
    {items : List V} (covers : ∀ a, a ∈ items) (item : Completed schema classOf edge) :
    item ∈ completionItems schema classOf edge items covers := by
  cases item with
  | inl a =>
    apply List.mem_append_left
    exact List.mem_map_of_mem (covers a)
  | inr leaf =>
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨leaf.val.1, covers _, ?_⟩
    refine List.mem_filterMap.mpr ⟨⟨leaf.val.2, leaf.property.1⟩, List.mem_attach .., ?_⟩
    simp [(roleOccupied_spec covers).mpr leaf.property.2]
    exact congrArg Sum.inr (Subtype.ext (Prod.eta leaf.val))

theorem acceptedCode_groundWitness [DecidableEq C] [DecidableEq A] {schema : Schema C}
    {input : Inputs C A m n} {code : MatchingCode (m+1)}
    (accepted : code ∈ acceptedCodes schema input) :
    let classOf := coreClass input.pClass input.qClass (code := code) (n := n+1)
    let edge := coreEdge code (n+1)
    SkeletonLegal schema (completionClass schema classOf edge)
      (completionEdge schema classOf edge) ∧
    GroundWitness input (completionClass schema classOf edge) (completionEdge schema classOf edge)
      (fun i => Sum.inl (pSlot code i)) (fun j => Sum.inl (qSlot code j)) := by
  obtain ⟨valid, legal, distinct, noShield⟩ := mem_acceptedCodes_iff.mp accepted
  have matching := (mem_validCodes_iff.mp valid).2
  obtain ⟨pPath, qPath⟩ := valid_matching_paths matching
  let classOf := coreClass input.pClass input.qClass (code := code) (n := n+1)
  let oldEdge := coreEdge code (n+1)
  let newEdge := completionEdge schema classOf oldEdge
  let includeItem : CoreItem code (n+1) → Completed schema classOf oldEdge := Sum.inl
  have includePath {a b : CoreItem code (n+1)} {items : List (CoreItem code (n+1))}
      (path : Path oldEdge a b items) :
      Path newEdge (includeItem a) (includeItem b) (items.map includeItem) :=
    path_map (edge := oldEdge) (edge' := newEdge) includeItem path
      (fun _ _ _ _ => Sum.inl.inj) (fun _ _ _ _ adj => adj)
  refine ⟨legal_completion legal, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have mapped := includePath pPath
    rw [List.map_ofFn] at mapped
    exact mapped
  · have mapped := includePath qPath
    rw [List.map_ofFn] at mapped
    exact mapped
  · intro i
    exact class_pSlot input.pClass input.qClass code i
  · intro j
    exact class_qSlot matching j
  · exact congrArg Sum.inl (same_middle matching)
  · let project : Completed schema (coreClass input.pClass input.qClass)
        (coreEdge code (n+1)) → CoreItem code (n+1) :=
      Sum.elim id (fun leaf => leaf.val.1)
    exact distinctVariables_of_image project distinct
  · intro label shielding realized
    exact noShield label shielding (realization_completion_iff.mp realized)

/-- A result contains the accepted matching, all middle labels, and one endpoint label. -/
structure Result (C : Type u) (m : Nat) where
  code : MatchingCode (m+1)
  middle : List (List C)
  endpoint : List C

def construct [DecidableEq C] [BEq C] [LawfulBEq C] [DecidableEq A]
    (schema : Schema C) (input : Inputs C A m n) : List (Result C m) :=
  (acceptedCodes schema input).flatMap fun code =>
    let classes := coreClass input.pClass input.qClass (code := code) (n := n+1)
    let middle := labelsBetween classes (pSlot code 0) (pSlot code (Fin.last m))
    (labelsBetween classes (pSlot code 0) (qSlot code (Fin.last n))).map fun endpoint =>
      ⟨code, middle, endpoint⟩

theorem mem_construct_iff [DecidableEq C] [BEq C] [LawfulBEq C] [DecidableEq A]
    {schema : Schema C} {input : Inputs C A m n} {out : Result C m} :
    out ∈ construct schema input ↔
      out.code ∈ acceptedCodes schema input ∧
      out.middle = labelsBetween (coreClass input.pClass input.qClass (n := n+1))
        (pSlot out.code 0) (pSlot out.code (Fin.last m)) ∧
      out.endpoint ∈ labelsBetween (coreClass input.pClass input.qClass)
        (pSlot out.code 0) (qSlot out.code (Fin.last n)) := by
  cases out
  simp only [construct, List.mem_flatMap, List.mem_map, Result.mk.injEq]
  constructor
  · rintro ⟨code, accepted, endpoint, realized, rfl, rfl, rfl⟩
    exact ⟨accepted, rfl, realized⟩
  · rintro ⟨accepted, rfl, realized⟩
    exact ⟨_, accepted, _, realized, rfl, rfl, rfl⟩

theorem construct_of_groundWitness [DecidableEq C] [BEq C] [LawfulBEq C] [DecidableEq A]
    [DecidableEq V] {schema : Schema C} {input : Inputs C A m n} {edge : V → V → Prop}
    {classOf : V → C} {pItems : Fin (m+1) → V} {qItems : Fin (n+1) → V}
    (legal : SkeletonLegal schema classOf edge)
    (ground : GroundWitness input classOf edge pItems qItems) :
    ∃ out ∈ construct schema input, out.code = witnessCode pItems qItems := by
  let code := witnessCode pItems qItems
  let classes := coreClass input.pClass input.qClass (code := code) (n := n+1)
  have accepted := groundWitness_accepts legal ground
  have matching := (mem_validCodes_iff.mp (mem_acceptedCodes_iff.mp accepted).1).2
  obtain ⟨pPath, qPath⟩ := valid_matching_paths matching
  rw [← same_middle matching] at qPath
  obtain ⟨items, connects⟩ := path_between_joined pPath qPath
  refine ⟨⟨code, labelsBetween classes (pSlot code 0) (pSlot code (Fin.last m)),
    items.map classes⟩, mem_construct_iff.mpr ⟨accepted, rfl, ?_⟩, rfl⟩
  exact labelsBetween_spec.mpr ⟨items, connects, rfl⟩

/-- Every output represents a ground unshielded triple, and its middle list contains
exactly the labels realized in the completed skeleton. -/
theorem construct_sound [DecidableEq C] [BEq C] [LawfulBEq C] [DecidableEq A]
    {schema : Schema C} {input : Inputs C A m n} {out : Result C m}
    (found : out ∈ construct schema input) :
    let classes := coreClass input.pClass input.qClass (code := out.code) (n := n+1)
    let classOf := completionClass schema classes (coreEdge out.code (n+1))
    let edge := completionEdge schema classes (coreEdge out.code (n+1))
    SkeletonLegal schema classOf edge ∧
    GroundWitness input classOf edge
      (fun i => Sum.inl (pSlot out.code i)) (fun j => Sum.inl (qSlot out.code j)) ∧
    (∀ label, label ∈ out.middle ↔ Realizes edge classOf
      (.inl (pSlot out.code 0)) (.inl (pSlot out.code (Fin.last m))) label) ∧
    Realizes edge classOf (.inl (pSlot out.code 0)) (.inl (qSlot out.code (Fin.last n)))
      out.endpoint := by
  obtain ⟨accepted, middle, endpoint⟩ := mem_construct_iff.mp found
  obtain ⟨legal, witness⟩ := acceptedCode_groundWitness accepted
  refine ⟨legal, witness, ?_, realization_completion_iff.mpr (labelsBetween_spec.mp endpoint)⟩
  intro label
  rw [middle, labelsBetween_spec, realization_completion_iff]

end CutComplete

end
