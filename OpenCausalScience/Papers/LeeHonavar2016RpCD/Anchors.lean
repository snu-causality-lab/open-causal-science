module
public import OpenCausalScience.Papers.LeeHonavar2016RpCD.RelationalPaths

@[expose] public section

open RelationalPaths

namespace RpCD

inductive ItemClass
  | S | H | W | U | J | K
  | A | B | R | T | D | L | M
  deriving DecidableEq, Repr

open ItemClass

def pLabels : List ItemClass := [S, A, H, R, W, T, U, L, J]
def qLabels : List ItemClass := [J, M, U, D, W, T, S, A, K, B, H, R]

/-- The role list of each relationship class. Each role has cardinality one. -/
def roles : ItemClass → List ItemClass
  | A => [S, H, K]
  | B => [K, H]
  | R => [H, W]
  | T => [S, W, U]
  | D => [U, W]
  | L | M => [U, J]
  | _ => []

def roleNeighbors (c : ItemClass) : List ItemClass :=
  [S, H, W, U, J, K, A, B, R, T, D, L, M].filter fun d =>
    (roles c).contains d || (roles d).contains c

/-- All legal P/Q identifications are unions of these four blocks plus J. -/
structure Blocks where
  sa : Bool
  hr : Bool
  wt : Bool
  u : Bool
  deriving DecidableEq, Repr

def Blocks.shared (m : Blocks) : ItemClass → Bool
  | S | A => m.sa
  | H | R => m.hr
  | W | T => m.wt
  | U => m.u
  | J => true
  | _ => false

def full : Blocks := ⟨true, true, true, true⟩

/-- False denotes the P item or a Q-only item. True denotes a separate Q copy. -/
abbrev Item := ItemClass × Bool

def pItem (c : ItemClass) : Item := (c, false)
def qItem (m : Blocks) (c : ItemClass) : Item :=
  (c, pLabels.contains c && !m.shared c)

def pItems : List Item := pLabels.map pItem
def qItems (m : Blocks) : List Item := qLabels.map (qItem m)

def vertices (m : Blocks) : List Item := (pItems ++ qItems m).eraseDups

def walkEdges (m : Blocks) : List (Item × Item) :=
  pItems.zip pItems.tail ++ (qItems m).zip (qItems m).tail

def neighbors (m : Blocks) (v : Item) : List Item :=
  ((walkEdges m).filterMap fun (a, b) =>
    if v == a then some b else if v == b then some a else none).eraseDups

def CoreEdge (m : Blocks) (u v : Item) : Prop := v ∈ neighbors m u

instance (m : Blocks) : DecidableRel (CoreEdge m) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ _))

def start : Item := pItem S
def middle : Item := pItem J
def finish (m : Blocks) : Item := qItem m R

def labels (m : Blocks) (a b : Item) : List (List ItemClass) :=
  pathLabels (neighbors m) Prod.fst (vertices m).length a b

/-- The twelve distinct shielding dependencies from the September witness. -/
def shields : List (List ItemClass) :=
  [[S,A,H,R,W,T,U,L,J,M,U,D,W,T,S,A,K,B,H,R],
   [S,T,W,D,U,M,J,L,U,T,W,R,H,A,K,B,H,R],
   [S,A,H,B,K,A,S,T,W,D,U,M,J,L,U,T,W,R],
   [S,A,H,R,W,T,S,A,K,B,H,R],
   [S,A,H,R,W,T,U,D,W,T,S,A,K,B,H,R],
   [S,T,W,D,U,M,J,L,U,T,W,R],
   [S,T,W,R,H,A,K,B,H,R],
   [S,T,W,D,U,T,W,R,H,A,K,B,H,R],
   [S,A,H,B,K,A,S,T,W,R],
   [S,A,H,B,K,A,S,T,W,D,U,T,W,R],
   [S,T,U,L,J,M,U,D,W,R],
   [S,T,W,D,U,T,W,R]]

def endpointPaths (m : Blocks) : List (List ItemClass) :=
  labels m start (finish m)

def matchingIsShielded (m : Blocks) : Bool :=
  (endpointPaths m).any shields.contains

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem shielded_iff_proper (m : Blocks) :
    matchingIsShielded m = true ↔ m ≠ full := by
  rcases m with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem full_path_counts :
    (vertices full).length = 13 ∧ (endpointPaths full).length = 4 ∧
    (labels full start middle).length = 12 ∧
    (labels full (finish full) middle).length = 12 := by
  decide

def everyCoreIncidenceIsLegal (m : Blocks) : Bool :=
  (vertices m).all fun v =>
    (neighbors m v).all (fun w => (roleNeighbors v.1).contains w.1) &&
      decide (((neighbors m v).map Prod.fst).Nodup)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem all_cores_are_legal (m : Blocks) : everyCoreIncidenceIsLegal m = true := by
  rcases m with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ <;> decide

/-- A saturated component admits no unused relationship or participant role. -/
theorem full_saturates_schema :
    ((vertices full).all fun v => (roleNeighbors v.1).all fun c =>
      (neighbors full v).any fun w => w.1 == c) = true := by
  decide

/-- Check both generating paths in the actual valid skeleton. -/
theorem full_generators :
    Path (CoreEdge full) start middle pItems ∧
      Path (CoreEdge full) middle (finish full) (qItems full) := by
  constructor <;> (unfold Path; decide)

theorem core_edge_iff (m : Blocks) (a b : Item) :
    CoreEdge m a b ↔ (a, b) ∈ walkEdges m ∨ (b, a) ∈ walkEdges m := by
  constructor
  · intro h
    unfold CoreEdge neighbors at h
    rw [List.mem_eraseDups, List.mem_filterMap] at h
    obtain ⟨⟨u, v⟩, membership, hv⟩ := h
    change (if a == u then some v else if a == v then some u else none) = some b at hv
    by_cases au : a = u
    · have eq : v = b := by simpa [au] using hv
      exact Or.inl (by simpa [au, ← eq] using membership)
    · by_cases av : a = v
      · have eq : u = b := by simpa only [beq_iff_eq, ite_eq_right au, ite_eq_left av, Option.some.injEq] using hv
        exact Or.inr (by simpa [av, ← eq] using membership)
      · simp [au, av] at hv
  · intro h
    unfold CoreEdge neighbors
    rw [List.mem_eraseDups, List.mem_filterMap]
    rcases h with ab | ba
    · exact ⟨(a, b), ab, by simp⟩
    · exact ⟨(b, a), ba, by by_cases eq : a = b <;> simp [eq]⟩

theorem core_edge_vertices (m : Blocks) {a b : Item} (h : CoreEdge m a b) :
    a ∈ vertices m ∧ b ∈ vertices m := by
  have edgeMembers (u v : Item) (membership : (u, v) ∈ walkEdges m) :
      u ∈ vertices m ∧ v ∈ vertices m := by
    simp only [walkEdges, List.mem_append] at membership
    rcases membership with left | right
    · obtain ⟨hu, hv⟩ := List.of_mem_zip left
      simp [vertices, hu, List.mem_of_mem_tail hv]
    · obtain ⟨hu, hv⟩ := List.of_mem_zip right
      simp [vertices, hu, List.mem_of_mem_tail hv]
  rcases (core_edge_iff m a b).mp h with ab | ba
  · exact edgeMembers _ _ ab
  · exact (edgeMembers _ _ ba).symm

theorem chain_mem_vertices {m : Blocks} {a : Item} {tail : List Item}
    (startIn : a ∈ vertices m) (walk : Chain (CoreEdge m) a tail) :
    ∀ v ∈ a :: tail, v ∈ vertices m := by
  induction tail generalizing a with
  | nil => simpa
  | cons b rest ih =>
    intro v hv
    rcases List.mem_cons.mp hv with eq | hv
    · exact eq ▸ startIn
    · exact ih (core_edge_vertices m walk.1).2 walk.2 v hv

/-- The finite checker covers every simple item path in the core. -/
theorem mem_labels {m : Blocks} {a b : Item} {code : List ItemClass}
    (startIn : a ∈ vertices m) :
    code ∈ labels m a b ↔ ∃ items, Path (CoreEdge m) a b items ∧
      items.map Prod.fst = code := by
  unfold labels
  rw [mem_pathLabels]
  constructor
  · rintro ⟨items, path, _, typed⟩
    exact ⟨items, path, typed⟩
  · rintro ⟨items, path, typed⟩
    obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp path.1
    refine ⟨a :: tail, path, path.2.2.1.length_le_of_subset ?_, typed⟩
    exact chain_mem_vertices startIn path.2.2.2

end RpCD

end
