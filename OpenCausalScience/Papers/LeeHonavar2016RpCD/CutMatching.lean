module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.ExactCUT

@[expose] public section

/-! Exact shared-item matching for the revised CUT construction.

Each position of the second generating path either names a position of the
first path or receives its own item. Enumeration is finite even when the
ambient skeleton is supplied as a proposition-valued graph.
-/

namespace CutComplete

def listsOfLength (options : List A) : Nat → List (List A)
  | 0 => [[]]
  | n + 1 => options.flatMap fun element =>
      (listsOfLength options n).map (element :: ·)

theorem mem_listsOfLength {options : List A} {length : Nat} {xs : List A} :
    xs ∈ listsOfLength options length ↔ xs.length = length ∧ ∀ a ∈ xs, a ∈ options := by
  induction length generalizing xs with
  | zero => cases xs <;> simp [listsOfLength]
  | succ n ih =>
    cases xs with
    | nil => simp [listsOfLength]
    | cons a rest =>
      constructor
      · intro mem
        obtain ⟨b, hb, mapped⟩ := List.mem_flatMap.mp mem
        obtain ⟨bs, hbs, eq⟩ := List.mem_map.mp mapped
        obtain ⟨rfl, rfl⟩ := List.cons.inj eq
        obtain ⟨len, elems⟩ := ih.mp hbs
        exact ⟨by simp [len], fun a' mem' => (List.mem_cons.mp mem').elim
          (fun eq => eq.symm ▸ hb) (fun h => elems a' h)⟩
      · rintro ⟨len, elems⟩
        apply List.mem_flatMap.mpr
        refine ⟨a, elems a (by simp), List.mem_map.mpr ⟨rest, ?_, rfl⟩⟩
        exact ih.mpr ⟨by simpa using len, fun x hx => elems x (List.mem_cons_of_mem _ hx)⟩

abbrev MatchingCode (m : Nat) := List (Option (Fin m))

def codes (m n : Nat) : List (MatchingCode m) :=
  listsOfLength (none :: (List.finRange m).map some) n

theorem mem_codes_iff {m n : Nat} {code : MatchingCode m} :
    code ∈ codes m n ↔ code.length = n := by
  rw [codes, mem_listsOfLength, and_iff_left_iff_imp]
  intro _ element _
  cases element <;> simp [List.mem_finRange]

def assigned (code : MatchingCode m) (j : Fin n) : Option (Fin m) :=
  (code[j.val]?).getD none

theorem assigned_ofFn (f : Fin n → Option (Fin m)) (j : Fin n) :
    assigned (List.ofFn f) j = f j := by
  simp [assigned, j.isLt]

def ValidMatching (pClass : Fin m → C) (qClass : Fin n → C)
    (pMiddle : Fin m) (qMiddle : Fin n) (code : MatchingCode m) : Prop :=
  assigned code qMiddle = some pMiddle ∧
  (∀ i : Fin m, ∀ j : Fin n, assigned code j = some i → pClass i = qClass j) ∧
  (∀ i : Fin m, ∀ j k : Fin n,
    assigned code j = some i → assigned code k = some i → j = k)

instance [DecidableEq C] (pClass : Fin m → C) (qClass : Fin n → C)
    (pMiddle : Fin m) (qMiddle : Fin n) (code : MatchingCode m) :
    Decidable (ValidMatching pClass qClass pMiddle qMiddle code) := by
  unfold ValidMatching
  infer_instance

def validCodes [DecidableEq C] (pClass : Fin m → C) (qClass : Fin n → C)
    (pMiddle : Fin m) (qMiddle : Fin n) : List (MatchingCode m) :=
  (codes m n).filter fun code => decide (ValidMatching pClass qClass pMiddle qMiddle code)

theorem mem_validCodes_iff [DecidableEq C] {pClass : Fin m → C} {qClass : Fin n → C}
    {pMiddle : Fin m} {qMiddle : Fin n} {code : MatchingCode m} :
    code ∈ validCodes pClass qClass pMiddle qMiddle ↔
      code.length = n ∧ ValidMatching pClass qClass pMiddle qMiddle code := by
  simp [validCodes, mem_codes_iff]

/-- The match that retains precisely the cross-path equalities of two item lists. -/
def witnessCode [DecidableEq V] (pItems : Fin m → V) (qItems : Fin n → V) : MatchingCode m :=
  List.ofFn fun j => (List.finRange m).find? (fun i => decide (pItems i = qItems j))

theorem assigned_witness_iff [DecidableEq V] {pItems : Fin m → V} {qItems : Fin n → V}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j) (i : Fin m) (j : Fin n) :
    assigned (witnessCode pItems qItems) j = some i ↔ pItems i = qItems j := by
  rw [witnessCode, assigned_ofFn]
  constructor
  · intro found
    exact of_decide_eq_true (List.find?_some (p := fun k => decide (pItems k = qItems j)) found)
  · intro eq
    cases hit : (List.finRange m).find? (fun i => decide (pItems i = qItems j)) with
    | none =>
      exact ((List.find?_eq_none.mp hit) i (List.mem_finRange i) (decide_eq_true eq)).elim
    | some k =>
      have hk : pItems k = qItems j :=
        of_decide_eq_true (List.find?_some (p := fun a => decide (pItems a = qItems j)) hit)
      simp [pInjective (hk.trans eq.symm)]

theorem witnessCode_in_validCodes [DecidableEq V] [DecidableEq C]
    {pItems : Fin m → V} {qItems : Fin n → V}
    {pClass : Fin m → C} {qClass : Fin n → C} (classOf : V → C)
    {pMiddle : Fin m} {qMiddle : Fin n}
    (pInjective : ∀ {i j}, pItems i = pItems j → i = j)
    (qInjective : ∀ {i j}, qItems i = qItems j → i = j)
    (typedP : ∀ i, classOf (pItems i) = pClass i)
    (typedQ : ∀ i, classOf (qItems i) = qClass i)
    (sameMiddle : pItems pMiddle = qItems qMiddle) :
    witnessCode pItems qItems ∈ validCodes pClass qClass pMiddle qMiddle := by
  apply mem_validCodes_iff.mpr
  refine ⟨List.length_ofFn, (assigned_witness_iff pInjective _ _).mpr sameMiddle, ?_, ?_⟩
  · intro i j matched
    have equal := (assigned_witness_iff pInjective i j).mp matched
    rw [← typedP, ← typedQ, equal]
  · intro i j k left right
    exact qInjective (((assigned_witness_iff pInjective i j).mp left).symm.trans
      ((assigned_witness_iff pInjective i k).mp right))

end CutComplete

end
