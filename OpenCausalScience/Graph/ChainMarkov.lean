module
public import OpenCausalScience.Graph.ChainGraph
public import OpenCausalScience.Probability.FiniteMass

/-! # Block-recursive Markov statements of chain graphs

Drton (2009), §2.2, Definition 2. The syntax is independent of any choice
of conditional-independence relation or probability parameterization.
-/

namespace OpenCausalScience.ChainGraph

@[expose] public section

variable {n : Nat}

def difference (x y : Vertices n) : Vertices n := fun v => x v && !y v

def union (x y : Vertices n) : Vertices n := fun v => x v || y v

def subset (x y : Vertices n) : Bool := (List.finRange n).all fun v => !x v || y v

/-- The vertices in parent components of the component of `root`. -/
def componentParents (G : ChainGraph n) (root : Fin n) : Vertices n :=
  fun v => (List.finRange n).any fun a => G.component v a && G.parents (G.component root) a

structure CIStatement (n : Nat) where
  left : Vertices n
  right : Vertices n
  given : Vertices n

namespace CIStatement

def nonvacuous (query : CIStatement n) : Bool :=
  (List.finRange n).any query.left && (List.finRange n).any query.right

end CIStatement

inductive MarkovType
  | I
  | II
  | III
  | IV
  deriving DecidableEq

def MarkovType.conditionOnInternalNeighbors : MarkovType → Bool
  | .I | .II => true
  | .III | .IV => false

def MarkovType.conditionOnExternalNeighbors : MarkovType → Bool
  | .I | .III => true
  | .II | .IV => false

/-- Drton's (C1) statement for one chain component. -/
def componentStatement (G : ChainGraph n) (root : Fin n) : CIStatement n :=
  ⟨G.component root, difference (G.nonDescendants root) (G.componentParents root),
    G.componentParents root⟩

/-- Drton's (C2a) or (C2b) for a subset of one chain component. -/
def internalStatement (G : ChainGraph n) (kind : MarkovType) (root : Fin n)
    (vertices : Vertices n) : CIStatement n :=
  let adjacent := G.neighbors vertices
  let parents := G.componentParents root
  ⟨vertices, difference (G.component root) (union vertices adjacent),
    if kind.conditionOnInternalNeighbors then union parents adjacent else parents⟩

/-- Drton's (C3a) or (C3b) for a subset of one chain component. -/
def externalStatement (G : ChainGraph n) (kind : MarkovType) (root : Fin n)
    (vertices : Vertices n) : CIStatement n :=
  let parents := G.parents vertices
  ⟨vertices, difference (G.componentParents root) parents,
    if kind.conditionOnExternalNeighbors then union parents (G.neighbors vertices) else parents⟩

def ofMask (mask : BitVec n) : Vertices n := fun v => mask.getLsbD v.val

def allMasks (n : Nat) : List (BitVec n) := (List.finRange (2 ^ n)).map BitVec.ofFin

theorem mem_allMasks (mask : BitVec n) : mask ∈ allMasks n :=
  List.mem_map.mpr ⟨mask.toFin, List.mem_finRange _, rfl⟩

def componentSubsets (G : ChainGraph n) (root : Fin n) : List (BitVec n) :=
  (allMasks n).filter fun mask => subset (ofMask mask) (G.component root)

theorem mem_componentSubsets_iff (G : ChainGraph n) (root : Fin n) (mask : BitVec n) :
    mask ∈ G.componentSubsets root ↔ ∀ v, ofMask mask v = true → G.component root v = true := by
  simp only [componentSubsets, List.mem_filter, mem_allMasks, true_and, subset, List.all_eq_true,
    List.mem_finRange, Bool.or_eq_true_iff, Bool.not_eq_true']
  constructor
  · intro sat v selected
    simpa [selected] using sat v trivial
  · intro sat v _
    cases selected : ofMask mask v with
    | false => exact .inl rfl
    | true => exact .inr (sat v selected)

/-- Enumerate the nonvacuous equations of the chosen block-recursive property.
The representative of a component need not be unique. -/
def statements (G : ChainGraph n) (kind : MarkovType) : List (CIStatement n) :=
  let candidates := (List.finRange n).flatMap fun root =>
    G.componentStatement root ::
      ((G.componentSubsets root).flatMap fun mask =>
        [G.internalStatement kind root (ofMask mask), G.externalStatement kind root (ofMask mask)])
  candidates.filter CIStatement.nonvacuous

def obeys (G : ChainGraph n) (kind : MarkovType) (ci : CIStatement n → Prop) : Prop :=
  ∀ query ∈ G.statements kind, ci query

def check (G : ChainGraph n) (kind : MarkovType) (ci : CIStatement n → Bool) : Bool :=
  (G.statements kind).all ci

theorem check_iff (G : ChainGraph n) (kind : MarkovType) (ci : CIStatement n → Bool) :
    G.check kind ci = true ↔ G.obeys kind (fun query => ci query = true) := by
  unfold check obeys
  exact List.all_eq_true

namespace CIStatement

open Probability.FiniteMass (mass)

def valueCell (vertices : Vertices n) (value : BitVec n) (sample : BitVec n) : Bool :=
  (List.finRange n).all fun v => !vertices v || (ofMask value v == ofMask sample v)

/-- A cross-product for one assignment to the variables in the query.
Coordinates outside the query are ignored. -/
def binaryCrossProduct (query : CIStatement n) (weight : BitVec n → Rat) (value : BitVec n) : Prop :=
  let left := valueCell query.left value
  let right := valueCell query.right value
  let given := valueCell query.given value
  mass (allMasks n) weight (fun u => given u && left u && right u) *
    mass (allMasks n) weight given =
      mass (allMasks n) weight (fun u => given u && left u) *
        mass (allMasks n) weight (fun u => given u && right u)

instance (query : CIStatement n) (weight : BitVec n → Rat) (value : BitVec n) :
    Decidable (query.binaryCrossProduct weight value) := by
  unfold binaryCrossProduct
  infer_instance

def binaryCI (query : CIStatement n) (weight : BitVec n → Rat) : Prop :=
  ∀ value, query.binaryCrossProduct weight value

def binaryCheck (weight : BitVec n → Rat) (query : CIStatement n) : Bool :=
  (allMasks n).all fun value => decide (query.binaryCrossProduct weight value)

theorem binary_check_iff (weight : BitVec n → Rat) (query : CIStatement n) :
    binaryCheck weight query = true ↔ query.binaryCI weight := by
  simp [binaryCheck, binaryCI, List.all_eq_true, mem_allMasks]

theorem block_binary_check_iff (G : ChainGraph n) (kind : MarkovType) (weight : BitVec n → Rat) :
    G.check kind (binaryCheck weight) = true ↔ G.obeys kind (fun query => query.binaryCI weight) := by
  rw [G.check_iff]
  simp only [obeys, binary_check_iff]

end CIStatement

end
end OpenCausalScience.ChainGraph
