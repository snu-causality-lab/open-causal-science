module
public import Std

/-! # Pathwise m-separation for endpoint-marked mixed graphs

The endpoint marks, simple paths, and collider and noncollider rules follow
Richardson and Spirtes (2002), Sections 2.2–2.4 and 3.4. A finite bit mask
represents a conditioning set. The executable reference enumerates vertex
sequences, and the reflection proofs establish that its positive answers
are exactly those witnessed by simple paths.
Source: https://doi.org/10.1214/aos/1031689015
-/

namespace OpenCausalScience

@[expose] public section

/-- A loop-free mixed graph with at most one edge per pair. A true endpoint
mark is an arrowhead and a false mark is a tail. Swapping endpoints reverses
the order of the two marks. -/
structure MarkedGraph (n : Nat) where
  marks : Fin n → Fin n → Option (Bool × Bool)
  loop_free : ∀ v, marks v v = none
  swap_marks : ∀ u v, marks v u = (marks u v).map Prod.swap

namespace MarkedGraph

variable {n : Nat}

/-- Construct a graph from the portion of its table above the diagonal. -/
def ofAscending (table : Fin n → Fin n → Option (Bool × Bool)) : MarkedGraph n where
  marks u v :=
    if u < v then table u v else
    if v < u then (table v u).map Prod.swap else none
  loop_free v := by simp
  swap_marks u v := by
    by_cases uv : u < v
    · have vu : ¬v < u := by omega
      simp [uv, vu]
    · by_cases vu : v < u
      · cases table v u <;> simp [uv, vu, Prod.swap]
      · simp [uv, vu]

def adjacent (G : MarkedGraph n) (u v : Fin n) : Bool :=
  (G.marks u v).isSome

def directed (G : MarkedGraph n) (u v : Fin n) : Bool :=
  G.marks u v == some (false, true)

def arrowheadAt (G : MarkedGraph n) (middle neighbor : Fin n) : Bool :=
  (G.marks middle neighbor).any Prod.fst

def collider (G : MarkedGraph n) (left middle right : Fin n) : Bool :=
  G.arrowheadAt middle left && G.arrowheadAt middle right

def conditioned (cond : BitVec n) (v : Fin n) : Bool :=
  cond.getLsbD v.val

def vertexSequences [DecidableEq α] (vertices : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => [] :: vertices.flatMap fun v =>
      (vertexSequences (vertices.filter (· != v)) k).map (v :: ·)

private theorem mem_vertexSequences_of_simple {α : Type} [DecidableEq α] (k : Nat)
    {vertices p : List α} (len : p.length ≤ k) (simple : p.Nodup)
    (inside : ∀ v ∈ p, v ∈ vertices) : p ∈ vertexSequences vertices k := by
  induction k generalizing vertices p with
  | zero =>
    cases p with
    | nil => simp [vertexSequences]
    | cons v tail => simp at len
  | succ k ih =>
    cases p with
    | nil => exact List.mem_cons_self
    | cons v tail =>
      obtain ⟨absent, tailSimple⟩ := List.nodup_cons.mp simple
      have tailLength : tail.length ≤ k := by simpa using len
      have tailInside (w : α) (member : w ∈ tail) :
          w ∈ vertices.filter (· != v) := by
        apply List.mem_filter.mpr
        exact ⟨inside w (List.mem_cons_of_mem _ member), bne_iff_ne.mpr
          fun same => absent (same ▸ member)⟩
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨v, inside v List.mem_cons_self,
        List.mem_map.mpr ⟨tail, ih tailLength tailSimple tailInside, rfl⟩⟩

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] (l : List α) :
    ∀ m : List α, l.Nodup → (∀ a ∈ l, a ∈ m) → l.length ≤ m.length := by
  induction l with
  | nil => exact fun _ _ _ => Nat.zero_le _
  | cons a l ih =>
    intro m nodup inside
    obtain ⟨absent, rest⟩ := List.nodup_cons.mp nodup
    have present : a ∈ m := inside a List.mem_cons_self
    have smaller : l.length ≤ (m.erase a).length :=
      ih (m.erase a) rest fun b member =>
        (List.mem_erase_of_ne fun (same : b = a) => absent (same ▸ member)).mpr
          (inside b (List.mem_cons_of_mem _ member))
    rw [List.length_erase_of_mem present] at smaller
    have positive := List.length_pos_of_mem present
    simp only [List.length_cons]
    omega

def sequences (n : Nat) : List (List (Fin n)) :=
  vertexSequences (List.finRange n) n

private theorem mem_sequences_of_nodup {p : List (Fin n)} (simple : p.Nodup) :
    p ∈ sequences n := by
  have inside (v : Fin n) (_ : v ∈ p) : v ∈ List.finRange n := List.mem_finRange v
  have bound := length_le_of_nodup_subset p (List.finRange n) simple inside
  rw [List.length_finRange] at bound
  exact mem_vertexSequences_of_simple n bound simple inside

def followsArrows (G : MarkedGraph n) : List (Fin n) → Bool
  | u :: v :: rest => G.directed u v && G.followsArrows (v :: rest)
  | _ => true

/-- Reflexive ancestry in the directed part of the mixed graph. -/
def AncestorOfConditioned (G : MarkedGraph n) (cond : BitVec n) (v : Fin n) : Prop :=
  ∃ p : List (Fin n), p.Nodup ∧ p.head? = some v ∧
    p.getLast?.any (conditioned cond) = true ∧ G.followsArrows p = true

def activated (G : MarkedGraph n) (cond : BitVec n) (v : Fin n) : Bool :=
  (sequences n).any fun p =>
    decide p.Nodup && (p.head? == some v) &&
    p.getLast?.any (conditioned cond) && G.followsArrows p

theorem activated_iff (G : MarkedGraph n) (cond : BitVec n) (v : Fin n) :
    G.activated cond v = true ↔ G.AncestorOfConditioned cond v := by
  simp only [activated, AncestorOfConditioned, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨p, _, ⟨⟨hs, hh⟩, ht⟩, ha⟩
    exact ⟨p, hs, hh, ht, ha⟩
  · rintro ⟨p, hs, hh, ht, ha⟩
    exact ⟨p, mem_sequences_of_nodup hs, ⟨⟨hs, hh⟩, ht⟩, ha⟩

theorem activated_of_conditioned (G : MarkedGraph n) (cond : BitVec n) (v : Fin n)
    (h : conditioned cond v = true) : G.activated cond v = true := by
  apply (G.activated_iff cond v).2
  exact ⟨[v], by simp, rfl, h, rfl⟩

/-- Check every edge and interior vertex. Endpoints have no interior
activation requirement. -/
def activePath (G : MarkedGraph n) (cond : BitVec n) : List (Fin n) → Bool
  | u :: v :: w :: rest =>
    G.adjacent u v &&
      (if G.collider u v w then G.activated cond v else !conditioned cond v) &&
      G.activePath cond (v :: w :: rest)
  | [u, v] => G.adjacent u v
  | _ => true

def MConnected (G : MarkedGraph n) (left right : Fin n) (cond : BitVec n) : Prop :=
  ∃ p : List (Fin n), p.Nodup ∧ p.head? = some left ∧
    p.getLast? = some right ∧ G.activePath cond p = true

def MSeparated (G : MarkedGraph n) (left right : Fin n) (cond : BitVec n) : Prop :=
  ¬G.MConnected left right cond

def mConnected (G : MarkedGraph n) (left right : Fin n) (cond : BitVec n) : Bool :=
  (sequences n).any fun p =>
    decide p.Nodup && (p.head? == some left) &&
    (p.getLast? == some right) && G.activePath cond p

theorem mConnected_iff (G : MarkedGraph n) (left right : Fin n) (cond : BitVec n) :
    G.mConnected left right cond = true ↔ G.MConnected left right cond := by
  simp only [mConnected, MConnected, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨p, _, ⟨⟨hs, hh⟩, ht⟩, ha⟩
    exact ⟨p, hs, hh, ht, ha⟩
  · rintro ⟨p, hs, hh, ht, ha⟩
    exact ⟨p, mem_sequences_of_nodup hs, ⟨⟨hs, hh⟩, ht⟩, ha⟩

theorem mConnected_false_iff (G : MarkedGraph n) (left right : Fin n) (cond : BitVec n) :
    G.mConnected left right cond = false ↔ G.MSeparated left right cond := by
  rw [MSeparated, ← G.mConnected_iff]
  cases G.mConnected left right cond <;> simp

def LegalQuery (left right : Fin n) (cond : BitVec n) : Prop :=
  left ≠ right ∧ conditioned cond left = false ∧ conditioned cond right = false

/-- The separation property that defines maximality among ancestral graphs. -/
def HasSeparators (G : MarkedGraph n) : Prop :=
  ∀ left right, left ≠ right → G.adjacent left right = false →
    ∃ cond, LegalQuery left right cond ∧ G.MSeparated left right cond

/-- The equality of the singleton separation relations. The general
separation relation between two vertex sets is the conjunction over endpoint
pairs, as in Ali, Richardson and Spirtes (2009), Section 3.10. -/
def SameSeparations (G H : MarkedGraph n) : Prop :=
  ∀ left right cond, LegalQuery left right cond →
    (G.MSeparated left right cond ↔ H.MSeparated left right cond)

theorem sameSeparations_of_checks {G H : MarkedGraph n}
    (checks : ∀ x y : Fin n, ∀ z : Fin (2^n), x ≠ y →
      conditioned (BitVec.ofFin z) x = false → conditioned (BitVec.ofFin z) y = false →
      G.mConnected x y (BitVec.ofFin z) = H.mConnected x y (BitVec.ofFin z)) :
    G.SameSeparations H := by
  intro x y z legal
  rw [← G.mConnected_false_iff, ← H.mConnected_false_iff]
  have equal : G.mConnected x y z = H.mConnected x y z :=
    checks x y z.toFin legal.1 legal.2.1 legal.2.2
  rw [equal]

def UnshieldedCollider (G : MarkedGraph n) (x b y : Fin n) : Prop :=
  x ≠ b ∧ x ≠ y ∧ b ≠ y ∧ G.adjacent x b = true ∧
    G.adjacent b y = true ∧ G.adjacent x y = false ∧ G.collider x b y = true

theorem adjacent_mConnected (G : MarkedGraph n) {x y : Fin n}
    (ne : x ≠ y) (edge : G.adjacent x y = true) (cond : BitVec n) : G.MConnected x y cond := by
  exact ⟨[x, y], by simp [ne], rfl, rfl, edge⟩

theorem collider_excluded_from_separator (G : MarkedGraph n) {x b y : Fin n}
    {cond : BitVec n} (triple : G.UnshieldedCollider x b y) (sep : G.MSeparated x y cond) :
    conditioned cond b = false := by
  obtain ⟨xb, xy, by', first, second, _, col⟩ := triple
  cases h : conditioned cond b with
  | false => rfl
  | true =>
    exfalso
    apply sep
    refine ⟨[x, b, y], by simp [xb, xy, by'], rfl, rfl, ?_⟩
    simp [activePath, first, second, col, G.activated_of_conditioned cond b h]

theorem noncollider_in_separator (G : MarkedGraph n) {x b y : Fin n}
    {cond : BitVec n} (xb : x ≠ b) (xy : x ≠ y) (by' : b ≠ y)
    (first : G.adjacent x b = true) (second : G.adjacent b y = true)
    (col : G.collider x b y = false) (sep : G.MSeparated x y cond) :
    conditioned cond b = true := by
  cases h : conditioned cond b with
  | true => rfl
  | false =>
    exfalso
    apply sep
    refine ⟨[x, b, y], by simp [xb, xy, by'], rfl, rfl, ?_⟩
    simp [activePath, first, second, col, h]

end MarkedGraph

end

end OpenCausalScience
