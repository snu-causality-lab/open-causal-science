module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.CutMatching

@[expose] public section

open RelationalPaths
open ExactCUT (Realizes)

namespace CutComplete

/-- A core contains each P position and each unmatched Q position. -/
def retained (code : MatchingCode m) : Fin m ⊕ Fin n → Prop
  | .inl _ => True
  | .inr j => assigned code j = none

abbrev CoreItem (code : MatchingCode m) (n : Nat) :=
  { i : Fin m ⊕ Fin n // retained code i }

instance (code : MatchingCode m) (n : Nat) : DecidableEq (CoreItem code n) :=
  fun a b => if h : a.val = b.val then isTrue (Subtype.ext h)
    else isFalse (fun eq => h (congrArg Subtype.val eq))

def pSlot (code : MatchingCode m) (i : Fin m) : CoreItem code n := ⟨.inl i, trivial⟩

def qSlot (code : MatchingCode m) (j : Fin n) : CoreItem code n :=
  match h : assigned code j with
  | none => ⟨.inr j, h⟩
  | some i => pSlot code i

theorem qSlot_val (code : MatchingCode m) (j : Fin n) :
    (qSlot code j).val = (assigned code j).elim (.inr j) Sum.inl := by
  unfold qSlot
  split <;> simp_all [pSlot]

def coreClass (pClass : Fin m → C) (qClass : Fin n → C)
    {code : MatchingCode m} (item : CoreItem code n) : C :=
  Sum.elim pClass qClass item.val

theorem class_pSlot (pClass : Fin m → C) (qClass : Fin n → C)
    (code : MatchingCode m) (i : Fin m) :
    coreClass pClass qClass (pSlot code i) = pClass i := rfl

theorem class_qSlot {pClass : Fin m → C} {qClass : Fin n → C}
    {pMiddle : Fin m} {qMiddle : Fin n} {code : MatchingCode m}
    (valid : ValidMatching pClass qClass pMiddle qMiddle code) (j : Fin n) :
    coreClass pClass qClass (qSlot code j) = qClass j := by
  rw [coreClass, qSlot_val]
  cases h : assigned code j with
  | none => rfl
  | some i => exact valid.2.1 i j h

theorem same_middle {pClass : Fin m → C} {qClass : Fin n → C}
    {pMiddle : Fin m} {qMiddle : Fin n} {code : MatchingCode m}
    (valid : ValidMatching pClass qClass pMiddle qMiddle code) :
    pSlot code pMiddle = qSlot code qMiddle := by
  apply Subtype.ext
  simp [qSlot_val, valid.1, pSlot]

def steps (items : List V) : List (V × V) := items.zip items.tail

private theorem steps_map (f : V → W) (items : List V) :
    steps (items.map f) = (steps items).map (fun (a, b) => (f a, f b)) := by
  unfold steps
  rw [← List.map_tail]
  exact zip_map f items items.tail

theorem chain_steps (head : V) (tail : List V) :
    Chain (fun a b => (a, b) ∈ steps (head :: tail)) head tail := by
  induction tail generalizing head with
  | nil => trivial
  | cons next rest ih =>
    constructor
    · simp [steps]
    · simpa using chain_map id (ih next) (fun a _ b _ edge => by
        simp only [steps, List.tail_cons, List.zip_cons_cons, List.mem_cons, id_eq]
        exact Or.inr edge)

/-- Keep just the graph edges traversed by the two generating paths. -/
def coreArrow (code : MatchingCode m) (n : Nat) (a b : CoreItem code n) : Prop :=
  (a, b) ∈ steps (List.ofFn (pSlot code)) ∨ (a, b) ∈ steps (List.ofFn (qSlot code))

def coreEdge (code : MatchingCode m) (n : Nat) (a b : CoreItem code n) : Prop :=
  coreArrow code n a b ∨ coreArrow code n b a

theorem core_symmetric {code : MatchingCode m} {a b : CoreItem code n}
    (ab : coreEdge code n a b) : coreEdge code n b a := ab.symm

instance (code : MatchingCode m) (n : Nat) : DecidableRel (coreEdge code n) := by
  intro a b
  letI : BEq (CoreItem code n) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (CoreItem code n) := { eq_of_beq := of_decide_eq_true }
  unfold coreEdge coreArrow
  infer_instance

/-- Every canonical item is attained by one of the original positions. -/
def coreItems (code : MatchingCode m) (n : Nat) : List (CoreItem code n) :=
  (List.ofFn (pSlot code)) ++ (List.ofFn (qSlot code))

theorem mem_coreItems {code : MatchingCode m} (item : CoreItem code n) :
    item ∈ coreItems code n := by
  obtain ⟨slot, kept⟩ := item
  cases slot with
  | inl i => exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  | inr j =>
    refine List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, ?_⟩)
    apply Subtype.ext
    simp [qSlot_val, show assigned code j = none from kept]

def neighbors (code : MatchingCode m) (n : Nat) (a : CoreItem code n) :
    List (CoreItem code n) :=
  (coreItems code n).filter fun b => decide (coreEdge code n a b)

theorem mem_neighbors {code : MatchingCode m} {a b : CoreItem code n} :
    b ∈ neighbors code n a ↔ coreEdge code n a b := by
  simp [neighbors, mem_coreItems]

def embed (pItems : Fin m → V) (qItems : Fin n → V)
    {code : MatchingCode m} (item : CoreItem code n) : V :=
  Sum.elim pItems qItems item.val

theorem embed_pSlot (pItems : Fin m → V) (qItems : Fin n → V)
    (code : MatchingCode m) (i : Fin m) :
    embed pItems qItems (pSlot code i) = pItems i := rfl

theorem embed_qSlot [DecidableEq V] {pItems : Fin m → V} {qItems : Fin n → V}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j) (j : Fin n) :
    embed pItems qItems (qSlot (witnessCode pItems qItems) j) = qItems j := by
  rw [embed, qSlot_val]
  cases h : assigned (witnessCode pItems qItems) j with
  | none => rfl
  | some i => exact (assigned_witness_iff pInjective i j).mp h

theorem injective_embed [DecidableEq V] {pItems : Fin m → V} {qItems : Fin n → V}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j)
    (qInjective : ∀ {i j}, qItems i = qItems j → i = j)
    (a b : CoreItem (witnessCode pItems qItems) n) (equal : embed pItems qItems a = embed pItems qItems b) :
    a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  cases a with
  | inl i =>
    cases b with
    | inl j => exact Subtype.ext (congrArg Sum.inl (pInjective equal))
    | inr j =>
      exact (Option.some_ne_none i ((assigned_witness_iff pInjective i j).mpr equal |>.symm.trans hb)).elim
  | inr i =>
    cases b with
    | inl j =>
      exact (Option.some_ne_none j
        ((assigned_witness_iff pInjective j i).mpr equal.symm |>.symm.trans ha)).elim
    | inr j => exact Subtype.ext (congrArg Sum.inr (qInjective equal))

theorem class_embed [DecidableEq V] [DecidableEq C]
    {pItems : Fin m → V} {qItems : Fin n → V}
    (pClass : Fin m → C) (qClass : Fin n → C) (classOf : V → C)
    (typedP : ∀ i, classOf (pItems i) = pClass i)
    (typedQ : ∀ i, classOf (qItems i) = qClass i)
    (a : CoreItem (witnessCode pItems qItems) n) :
    classOf (embed pItems qItems a) = coreClass pClass qClass a := by
  obtain ⟨slot, _⟩ := a
  cases slot with
  | inl i => exact typedP i
  | inr j => exact typedQ j

private theorem coreArrow_embed [DecidableEq V] {ambient : V → V → Prop}
    {pItems : Fin m → V} {qItems : Fin n → V}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j)
    {pStart pMiddle qMiddle qEnd : V}
    (pPath : Path ambient pStart pMiddle (List.ofFn pItems))
    (qPath : Path ambient qMiddle qEnd (List.ofFn qItems))
    {a b : CoreItem (witnessCode pItems qItems) n}
    (arrow : coreArrow (witnessCode pItems qItems) n a b) :
    ambient (embed pItems qItems a) (embed pItems qItems b) := by
  rcases arrow with fromP | fromQ
  · obtain ⟨tail, form⟩ := List.head?_eq_some_iff.mp pPath.1
    have image := List.mem_map_of_mem (f := fun (ij : _ × _) =>
      (embed pItems qItems ij.1, embed pItems qItems ij.2)) fromP
    rw [← steps_map, List.map_ofFn] at image
    have compose : embed pItems qItems ∘ pSlot (witnessCode pItems qItems) = pItems := rfl
    rw [compose] at image
    rw [steps, form] at image
    exact chain_of_zip (by simpa [form] using pPath.2.2.2) _ _ image
  · obtain ⟨tail, form⟩ := List.head?_eq_some_iff.mp qPath.1
    have image := List.mem_map_of_mem (f := fun (ij : _ × _) =>
      (embed pItems qItems ij.1, embed pItems qItems ij.2)) fromQ
    rw [← steps_map, List.map_ofFn] at image
    have compose : embed pItems qItems ∘ qSlot (witnessCode pItems qItems) = qItems :=
      funext (embed_qSlot pInjective)
    rw [compose] at image
    rw [steps, form] at image
    exact chain_of_zip (by simpa [form] using qPath.2.2.2) _ _ image

theorem mapped_edge [DecidableEq V] {ambient : V → V → Prop}
    (symmetric : ∀ {a b}, ambient a b → ambient b a)
    {pItems : Fin m → V} {qItems : Fin n → V}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j)
    {pStart pMiddle qMiddle qEnd : V}
    (pPath : Path ambient pStart pMiddle (List.ofFn pItems))
    (qPath : Path ambient qMiddle qEnd (List.ofFn qItems))
    {a b : CoreItem (witnessCode pItems qItems) n}
    (edge : coreEdge (witnessCode pItems qItems) n a b) :
    ambient (embed pItems qItems a) (embed pItems qItems b) :=
  edge.elim (coreArrow_embed pInjective pPath qPath)
    (fun back => symmetric (coreArrow_embed pInjective pPath qPath back))

theorem injective_ofFn_nodup {items : Fin m → V}
    (distinct : (List.ofFn items).Nodup) {i j : Fin m} (eq : items i = items j) :
    i = j := by
  have hi : i.val < (List.ofFn items).length := by simp
  have hj : j.val < (List.ofFn items).length := by simp
  exact Fin.ext ((distinct.getElem_inj (hi := hi) (hj := hj)).mp (by simpa using eq))

private theorem path_from_slots {edge : U → U → Prop} {ambient : V → V → Prop}
    (f : U → V) (inj : ∀ a b, f a = f b → a = b)
    {a b : U} {items : List U}
    (inAmbient : Path ambient (f a) (f b) (items.map f))
    (adj : ∀ x y, (x, y) ∈ steps items → edge x y) :
    Path edge a b items := by
  obtain ⟨head, last, distinct, _⟩ := inAmbient
  cases items with
  | nil => simp at head
  | cons x rest =>
    have x_eq_a : x = a := inj _ _ (by simpa using head)
    subst x
    refine ⟨rfl, ?_, (List.pairwise_map.mp distinct).imp (fun ne eq => ne (congrArg f eq)), ?_⟩
    · rw [List.getLast?_map] at last
      cases found : (a :: rest).getLast? with
      | none => simp [found] at last
      | some y => exact congrArg some (inj _ _ (by simpa [found] using last))
    · simpa using chain_map id (chain_steps a rest) (fun x _ y _ => adj x y)

theorem paths_in_core [DecidableEq V] {ambient : V → V → Prop}
    {pItems : Fin m → V} {qItems : Fin n → V}
    {pStart pMiddle : Fin m} {qMiddle qEnd : Fin n}
    (pPath : Path ambient (pItems pStart) (pItems pMiddle) (List.ofFn pItems))
    (qPath : Path ambient (qItems qMiddle) (qItems qEnd) (List.ofFn qItems)) :
    let code := witnessCode pItems qItems
    Path (coreEdge code n) (pSlot code pStart) (pSlot code pMiddle)
        (List.ofFn (pSlot code)) ∧
    Path (coreEdge code n) (qSlot code qMiddle) (qSlot code qEnd)
        (List.ofFn (qSlot code)) := by
  let code := witnessCode pItems qItems
  let f := embed pItems qItems (code := code)
  have pInjective {i j} := injective_ofFn_nodup pPath.2.2.1 (i := i) (j := j)
  have qInjective {i j} := injective_ofFn_nodup qPath.2.2.1 (i := i) (j := j)
  have inj := injective_embed pInjective qInjective
  have pMapped : f ∘ pSlot code = pItems := rfl
  have qMapped : f ∘ qSlot code = qItems := funext (embed_qSlot pInjective)
  constructor
  · apply path_from_slots f inj (ambient := ambient)
    · rw [List.map_ofFn, pMapped]
      exact pPath
    · intro a b ab
      exact Or.inl (Or.inl ab)
  · apply path_from_slots f inj (ambient := ambient)
    · rw [List.map_ofFn, qMapped]
      change Path ambient (f (qSlot code qMiddle)) (f (qSlot code qEnd)) (List.ofFn qItems)
      have qPoint (i : Fin n) : f (qSlot code i) = qItems i := congrFun qMapped i
      rw [qPoint, qPoint]
      exact qPath
    · intro a b ab
      exact Or.inl (Or.inr ab)

private theorem nodup_ofFn {f : Fin m → V} (inj : ∀ i j, f i = f j → i = j) :
    (List.ofFn f).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ]
    refine List.nodup_cons.mpr ⟨?_, ih (fun i j h => Fin.succ_inj.mp (inj _ _ h))⟩
    intro mem
    obtain ⟨i, eq⟩ := List.mem_ofFn.mp mem
    exact Fin.succ_ne_zero i (inj _ _ eq)

private theorem path_of_slots (f : Fin (m+1) → V) (edge : V → V → Prop)
    (inj : ∀ i j, f i = f j → i = j)
    (adj : ∀ x y, (x, y) ∈ steps (List.ofFn f) → edge x y) :
    Path edge (f 0) (f (Fin.last m)) (List.ofFn f) := by
  have first : (List.ofFn f).head? = some (f 0) := by rw [List.ofFn_succ]; rfl
  have last : (List.ofFn f).getLast? = some (f (Fin.last m)) := by
    rw [List.getLast?_eq_getElem?, List.length_ofFn, List.getElem?_ofFn]
    simp [Fin.last]
  refine ⟨first, last, nodup_ofFn inj, ?_⟩
  obtain ⟨tail, form⟩ := List.head?_eq_some_iff.mp first
  rw [form] at adj ⊢
  simpa using chain_map id (chain_steps (f 0) tail) (fun x _ y _ => adj x y)

theorem valid_matching_paths {pClass : Fin (m+1) → C} {qClass : Fin (n+1) → C}
    {code : MatchingCode (m+1)} (valid : ValidMatching pClass qClass (Fin.last m) 0 code) :
    Path (coreEdge code (n+1)) (pSlot code 0) (pSlot code (Fin.last m))
        (List.ofFn (pSlot code)) ∧
    Path (coreEdge code (n+1)) (qSlot code 0) (qSlot code (Fin.last n))
        (List.ofFn (qSlot code)) := by
  constructor
  · exact path_of_slots (pSlot code) _ (fun _ _ h => Sum.inl.inj (congrArg Subtype.val h))
      (fun _ _ adj => Or.inl (Or.inl adj))
  · apply path_of_slots (qSlot code) _
    · intro i j eq
      have valEq := congrArg Subtype.val eq
      rw [qSlot_val, qSlot_val] at valEq
      cases hi : assigned code i with
      | none =>
        cases hj : assigned code j with
        | none => exact Sum.inr.inj (by simpa only [hi, hj, Option.elim] using valEq)
        | some k => simp [hi, hj] at valEq
      | some k =>
        cases hj : assigned code j with
        | none => simp [hi, hj] at valEq
        | some l =>
          have same : k = l := Sum.inl.inj (by simpa only [hi, hj, Option.elim] using valEq)
          exact valid.2.2 k i j hi (same.symm ▸ hj)
    · exact fun _ _ adj => Or.inl (Or.inr adj)

end CutComplete

end
