module
public import OpenCausalScience.Graph.MixedSeparation
public import OpenCausalScience.Papers.PerkovicEtAl2018.MixedBackDoor

/-! # Generalized adjustment with a selected source

Correa, Tian and Bareinboim (2018), Definition 9. The proper
back-door graph deletes precisely the directed first edges of proper
causal paths. Descendants for the forbidden set are computed in the
graph with arrows into treatment removed. The two separation tests
use the available population margin only on its measured variables.
Source: https://causalai.net/r29.pdf#page=5
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2018.Criterion

open PerkovicEtAl2018.MixedBackDoor (DirectedSuffix deleteDirected retained_directed_iff)

@[expose] public section

variable {n : Nat}

/-- Keep the directed subgraph outside the set of interventions.
Marks on other edge types are immaterial to directed reachability. -/
def freeArrows (G : MixedGraph n) (x : Fin n → Bool) : MixedGraph n :=
  deleteDirected G (fun u v => x u || x v)

private theorem free_edge_iff (G : MixedGraph n) (x : Fin n → Bool) (u v : Fin n) :
    (freeArrows G x).edge u false v true = true ↔
    G.edge u false v true = true ∧ x u = false ∧ x v = false := by
  rw [freeArrows, retained_directed_iff]
  cases x u <;> cases x v <;> simp

private theorem suffix_source_free {G : MixedGraph n} {x : Fin n → Bool}
    {a b : Fin n} (suffix : DirectedSuffix G x a b) : x a = false := by
  cases suffix <;> assumption

theorem free_ancestors_iff_suffix (G : MixedGraph n) (x y : Fin n → Bool) (v : Fin n) :
    v ∈ (freeArrows G x).ancestorVertices (fun u => !x u && y u) ↔
      ∃ w, y w = true ∧ DirectedSuffix G x v w := by
  rw [MixedGraph.mem_ancestorVertices_iff]
  constructor
  · intro reaches
    induction reaches with
    | @conditioned w inside =>
      have ⟨noTreatment, outcome⟩ := Bool.and_eq_true_iff.mp inside
      exact ⟨w, outcome, .done (by simpa using noTreatment)⟩
    | parent edge _ ih =>
      obtain ⟨last, outcome, suffix⟩ := ih
      obtain ⟨arrow, outside, _⟩ := (free_edge_iff G x _ _).mp edge
      exact ⟨last, outcome, .step outside arrow suffix⟩
  · rintro ⟨last, outcome, suffix⟩
    induction suffix with
    | done outside => exact .conditioned (by simp [outside, outcome])
    | step outside arrow tail ih =>
      exact .parent ((free_edge_iff G x _ _).mpr ⟨arrow, outside, suffix_source_free tail⟩) (ih outcome)

/-- The first step of a proper directed treatment-to-outcome path. -/
def properFirst (G : MixedGraph n) (x y : Fin n → Bool) (a b : Fin n) : Bool :=
  x a && G.edge a false b true &&
    ((freeArrows G x).ancestorVertices (fun u => !x u && y u)).contains b

theorem proper_first_iff (G : MixedGraph n) (x y : Fin n → Bool) (a b : Fin n) :
    properFirst G x y a b = true ↔
      x a = true ∧ G.edge a false b true = true ∧ ∃ w, y w = true ∧ DirectedSuffix G x b w := by
  simp only [properFirst, Bool.and_eq_true, List.contains_iff_mem,
    free_ancestors_iff_suffix, and_assoc]

def properBackdoor (G : MixedGraph n) (x y : Fin n → Bool) : MixedGraph n :=
  deleteDirected G (properFirst G x y)

theorem proper_backdoor_deletes_iff (G : MixedGraph n) (x y : Fin n → Bool) (a b : Fin n)
    (original : G.edge a false b true = true) :
    (properBackdoor G x y).edge a false b true = false ↔
      x a = true ∧ ∃ w, y w = true ∧ DirectedSuffix G x b w := by
  simp [properBackdoor, deleteDirected,
    PerkovicEtAl2018.MixedBackDoor.keepsMarking, original, proper_first_iff]

/-- It suffices to check descendants of the first children. All later
vertices on a proper causal path are descendants of the first child. -/
def forbidden (G : MixedGraph n) (x y : Fin n → Bool) (v : Fin n) : Bool :=
  (List.finRange n).any fun b =>
    ((List.finRange n).any fun a => properFirst G x y a b) &&
      ((freeArrows G x).ancestorVertices (fun u => !x u && (u == v))).contains b

theorem forbidden_iff (G : MixedGraph n) (x y : Fin n → Bool) (v : Fin n) :
    forbidden G x y v = true ↔
      ∃ a b w, x a = true ∧ G.edge a false b true = true ∧ y w = true ∧
        DirectedSuffix G x b w ∧ DirectedSuffix G x b v := by
  have desc : ∀ b,
      ((freeArrows G x).ancestorVertices (fun u => !x u && (u == v))).contains b = true ↔
        DirectedSuffix G x b v := by
    intro b
    rw [List.contains_iff_mem, free_ancestors_iff_suffix]
    simp
  simp only [forbidden, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    proper_first_iff, desc]
  constructor
  · rintro ⟨b, ⟨a, start, edge, w, endY, path⟩, reaches⟩
    exact ⟨a, b, w, start, edge, endY, path, reaches⟩
  · rintro ⟨a, b, w, start, edge, endY, path, reaches⟩
    exact ⟨b, ⟨a, start, edge, w, endY, path⟩, reaches⟩

private theorem suffix_append {G : MixedGraph n} {x : Fin n → Bool}
    {a b c : Fin n} (first : DirectedSuffix G x a b) (second : DirectedSuffix G x b c) :
    DirectedSuffix G x a c := by
  induction first with
  | done _ => exact second
  | step outside arrow _ ih => exact .step outside arrow (ih second)

/-- Definition 9's descendants of any non-treatment vertex on a proper
causal path. Checking only first children computes the same set. -/
theorem forbidden_iff_through_causal_vertex (G : MixedGraph n) (x y : Fin n → Bool)
    (v : Fin n) :
    forbidden G x y v = true ↔
      ∃ a b w last, x a = true ∧ G.edge a false b true = true ∧ y last = true ∧
        DirectedSuffix G x b w ∧ DirectedSuffix G x w last ∧ DirectedSuffix G x w v := by
  rw [forbidden_iff]
  constructor
  · rintro ⟨a, b, last, starts, arrow, ends, path, desc⟩
    exact ⟨a, b, b, last, starts, arrow, ends, .done (suffix_source_free path), path, desc⟩
  · rintro ⟨a, b, w, last, starts, arrow, ends, earlier, suffix, desc⟩
    exact ⟨a, b, last, starts, arrow, ends, suffix_append earlier suffix, suffix_append earlier desc⟩

/-- Disjoint query roles for one selection vertex. -/
structure Query (n : Nat) where
  x : Fin n → Bool
  y : Fin n → Bool
  s : Fin n
  x_outside_y : ∀ v, x v = true → y v = false
  s_outside_x : x s = false
  s_outside_y : y s = false

def Query.selection (query : Query n) (v : Fin n) : Bool := v == query.s

def Query.adjustmentAllowed (q : Query n) (z zt measured : Fin n → Bool) : Prop :=
  (∀ v, z v = true → q.x v = false ∧ q.y v = false ∧ q.selection v = false) ∧
  ∀ v, zt v = true → z v = true ∧ measured v = true

def coversRoles (q : Query n) (z zt measured : Fin n → Bool) : Bool :=
  ((List.finRange n).all fun v => !z v || (!q.x v && !q.y v && !q.selection v)) &&
    ((List.finRange n).all fun v => !zt v || (z v && measured v))

private theorem covers_roles_iff (q : Query n) (z zt measured : Fin n → Bool) :
    coversRoles q z zt measured = true ↔ q.adjustmentAllowed z zt measured := by
  simp only [coversRoles, Query.adjustmentAllowed, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_const, Bool.or_eq_true_iff, Bool.not_eq_true', and_assoc]
  constructor
  · rintro ⟨roles, outside⟩
    exact ⟨fun v h => (roles v).resolve_left (Bool.noConfusion ∘ (h ▸ ·)),
      fun v h => (outside v).resolve_left (Bool.noConfusion ∘ (h ▸ ·))⟩
  · rintro ⟨roles, outside⟩
    refine ⟨?_, ?_⟩
    · intro v
      cases h : z v
      · exact .inl rfl
      · exact .inr (roles v h)
    · intro v
      cases h : zt v
      · exact .inl rfl
      · exact .inr (outside v h)

def valid (G : MixedGraph n) (q : Query n) (z zt measured : Fin n → Bool) : Bool :=
  let gd := properBackdoor G q.x q.y
  coversRoles q z zt measured &&
    (List.finRange n).all (fun v => !z v || !forbidden G q.x q.y v) &&
    gd.mSeparated q.x q.y (fun v => z v || q.selection v) &&
    gd.mSeparated q.selection q.y zt

/-- The GACT3A path formulation with explicit source availability. -/
def Admissible (G : MixedGraph n) (q : Query n) (z zt measured : Fin n → Bool) : Prop :=
  q.adjustmentAllowed z zt measured ∧
  (∀ v, z v = true →
    ¬ ∃ a b w, q.x a = true ∧ G.edge a false b true = true ∧ q.y w = true ∧
      DirectedSuffix G q.x b w ∧ DirectedSuffix G q.x b v) ∧
  (let gd := properBackdoor G q.x q.y
   ¬ gd.PathConnected q.x q.y (fun v => z v || q.selection v)) ∧
  (let gd := properBackdoor G q.x q.y
   ¬ gd.PathConnected q.selection q.y zt)

theorem valid_iff_admissible (G : MixedGraph n) (q : Query n) (z zt measured : Fin n → Bool) :
    valid G q z zt measured = true ↔ Admissible G q z zt measured := by
  let gd := properBackdoor G q.x q.y
  have candidates : (List.finRange n).all (fun v => !z v || !forbidden G q.x q.y v) = true ↔
      ∀ v, z v = true → ¬ ∃ a b w, q.x a = true ∧ G.edge a false b true = true ∧
        q.y w = true ∧ DirectedSuffix G q.x b w ∧ DirectedSuffix G q.x b v := by
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true_iff,
      Bool.not_eq_true']
    constructor
    · intro checked v used
      have notForbidden : forbidden G q.x q.y v = false :=
        (checked v).resolve_left (by simp [used])
      intro occurs
      have banned := (forbidden_iff G q.x q.y v).mpr occurs
      simp [notForbidden] at banned
    · intro avoids v
      cases used : z v
      · exact .inl rfl
      · right
        cases banned : forbidden G q.x q.y v
        · rfl
        · exact (avoids v used ((forbidden_iff G q.x q.y v).mp banned)).elim
  have first (roles : q.adjustmentAllowed z zt measured) :=
    gd.m_separated_iff_no_path q.x q.y (fun v => z v || q.selection v) (by
      intro v treated
      have noAdjust : z v = false := by
        cases chosen : z v
        · rfl
        · have outside := (roles.1 v chosen).1
          simp [treated] at outside
      have noSelected : q.selection v = false := by
        cases selected : q.selection v
        · rfl
        · have equal : v = q.s := beq_iff_eq.mp selected
          subst v
          simp [q.s_outside_x] at treated
      simp [noAdjust, noSelected]) q.x_outside_y
  have second (roles : q.adjustmentAllowed z zt measured) :=
    gd.m_separated_iff_no_path q.selection q.y zt (by
      intro v selected
      cases used : zt v
      · rfl
      · have noSelection := (roles.1 v (roles.2 v used).1).2.2
        simp [selected] at noSelection) (by
      intro v selected
      obtain rfl := beq_iff_eq.mp selected
      exact q.s_outside_y)
  simp only [valid, Bool.and_eq_true, and_assoc, covers_roles_iff, Admissible]
  refine and_congr_right ?_
  intro roles
  rw [candidates, first roles, second roles]

end

end OpenCausalScience.Papers.CorreaTianBareinboim2018.Criterion
