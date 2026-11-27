module
public import OpenCausalScience.Graph.MixedSeparators
public import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability

/-!
# Ordered local Markov blankets
Richardson, *Markov Properties for Acyclic Directed Mixed Graphs*,
Scandinavian Journal of Statistics 30 (2003), 145–157, and UW TR 353, §3.
The blanket proof uses the induced district and collider augmentation.
-/

namespace OpenCausalScience.MixedGraph

open Papers.TianPearl2003.IdentifyRecurrence (district)
open Papers.TianPearl2003.IdentifyReachability (Reached mem_district_iff)

@[expose] public section

abbrev VertexMask (n : Nat) := Fin n → Bool

variable {n : Nat} {G : MixedGraph n}

/-- A set containing the parents of each of its members. -/
def AncestralSet (G : MixedGraph n) (A : VertexMask n) : Prop :=
  ∀ u v, A v = true → G.edge u false v true = true → A u = true

def NoLines (G : MixedGraph n) : Prop :=
  ∀ u v, G.edge u false v false = false

/-- No directed child of the vertex occurs in the induced set. -/
def ChildlessIn (G : MixedGraph n) (A : VertexMask n) (x : Fin n) : Prop :=
  ∀ v, A v = true → G.edge x false v true = false

def inducedDistrict (G : MixedGraph n) (A : VertexMask n) (x : Fin n) : List (Fin n) :=
  district G ((List.finRange n).filter A) x

theorem mem_inducedDistrict_iff {A : VertexMask n} {x v : Fin n} :
    v ∈ G.inducedDistrict A x ↔
      Reached (fun u w => G.edge u true w true) ((List.finRange n).filter A) (· == x) v :=
  mem_district_iff _ _ _ _

theorem inducedDistrict_inside {A : VertexMask n} {x v : Fin n}
    (member : v ∈ G.inducedDistrict A x) : A v = true :=
  (List.mem_filter.mp (mem_inducedDistrict_iff.mp member).in_current).2

theorem mem_inducedDistrict_self {A : VertexMask n} {x : Fin n}
    (member : A x = true) : x ∈ G.inducedDistrict A x :=
  mem_inducedDistrict_iff.mpr
    (.seed (List.mem_filter.mpr ⟨List.mem_finRange _, member⟩) (by simp))

theorem mem_inducedDistrict_step {A : VertexMask n} {x u v : Fin n}
    (before : u ∈ G.inducedDistrict A x) (member : A v = true)
    (edge : G.edge u true v true = true) : v ∈ G.inducedDistrict A x :=
  mem_inducedDistrict_iff.mpr
    (.step (mem_inducedDistrict_iff.mp before)
      (List.mem_filter.mpr ⟨List.mem_finRange _, member⟩) edge)

/-- The parents of the induced district and the district itself, excluding x. -/
def markovBlanket (G : MixedGraph n) (A : VertexMask n) (x : Fin n) : VertexMask n :=
  let D := G.inducedDistrict A x
  fun v => (v != x) && (D.contains v || D.any (fun w => G.edge v false w true))

theorem markovBlanket_iff {A : VertexMask n} {x v : Fin n} :
    G.markovBlanket A x v = true ↔
      v ≠ x ∧ (v ∈ G.inducedDistrict A x ∨
        ∃ w ∈ G.inducedDistrict A x, G.edge v false w true = true) := by
  simp [markovBlanket, Bool.or_eq_true, List.any_eq_true]

theorem markovBlanket_inside {A : VertexMask n} {x v : Fin n}
    (closed : G.AncestralSet A) (member : G.markovBlanket A x v = true) :
    A v = true := by
  rcases (markovBlanket_iff.mp member).2 with district | ⟨w, district, arrow⟩
  · exact inducedDistrict_inside district
  · exact closed v w (inducedDistrict_inside district) arrow

private theorem collider_from_district {A : VertexMask n} {x u v : Fin n}
    {mark : Bool} (walk : G.ColliderWalk A (u, true) (v, mark))
    (start : u ∈ G.inducedDistrict A x) :
    if mark then v ∈ G.inducedDistrict A x else
      ∃ w ∈ G.inducedDistrict A x, G.edge v false w true = true := by
  have aux (s t : Arrival n) (walk : G.ColliderWalk A s t)
      (head : s.2 = true) (start : s.1 ∈ G.inducedDistrict A x) :
      if t.2 then t.1 ∈ G.inducedDistrict A x else
        ∃ w ∈ G.inducedDistrict A x, G.edge t.1 false w true = true := by
    induction walk with
    | @single a b _ last edge =>
      cases hm : b.2 with
      | false =>
        refine ⟨a.1, start, ?_⟩
        simpa [head, hm] using (G.symmetric _ _ _ _).symm.trans edge
      | true =>
        exact mem_inducedDistrict_step start last (by simpa [head, hm] using edge)
    | join _ _ before after =>
      exact after rfl (before head start)
  exact aux _ _ walk rfl start

private theorem collider_from_root_has_head {A : VertexMask n} {x : Fin n}
    {v : Arrival n} (lineFree : G.NoLines) (sink : G.ChildlessIn A x)
    {mark : Bool} (walk : G.ColliderWalk A (x, mark) v) : mark = true := by
  obtain ⟨y, inside, arrow, _⟩ := walk.first_edge
  cases mark with
  | true => rfl
  | false =>
    cases m : y.2 with
    | false => exact (Bool.noConfusion ((lineFree x y.1).symm.trans (by simpa [m] using arrow)))
    | true => simp [m, sink y.1 inside] at arrow

private theorem district_collider_walk {A : VertexMask n} {x v : Fin n}
    (member : v ∈ G.inducedDistrict A x) :
    v = x ∨ G.ColliderWalk A (x, true) (v, true) := by
  have path := mem_inducedDistrict_iff.mp member
  clear member
  induction path with
  | seed _ root => exact .inl (beq_iff_eq.mp root)
  | @step u v before inSet edge ih =>
    have step : G.ColliderWalk A (u, true) (v, true) := .single
      (List.mem_filter.mp before.in_current).2 (List.mem_filter.mp inSet).2 edge
    rcases ih with rfl | first
    · exact .inr step
    · exact .inr (.join first step)

private theorem blanket_collider_walk {A : VertexMask n} {x v : Fin n}
    (rootInside : A x = true) (inside : A v = true)
    (member : G.markovBlanket A x v = true) :
    ∃ mark, G.ColliderWalk A (x, true) (v, mark) := by
  rcases markovBlanket_iff.mp member with ⟨ne, inDistrict | ⟨w, district, arrow⟩⟩
  · exact ⟨true, (district_collider_walk inDistrict).resolve_left ne⟩
  · have last : G.ColliderWalk A (w, true) (v, false) :=
      .single (inducedDistrict_inside district) inside
        ((G.symmetric _ _ _ _).symm.trans arrow)
    rcases district_collider_walk district with rfl | first
    · exact ⟨false, last⟩
    · exact ⟨false, .join first last⟩

/-- The augmented neighbors of a childless vertex are exactly its blanket. -/
theorem collider_augmented_iff_markovBlanket {A : VertexMask n} {x v : Fin n}
    (lineFree : G.NoLines) (closed : G.AncestralSet A) (rootInside : A x = true)
    (sink : G.ChildlessIn A x) :
    G.colliderAugmented A x v = true ↔ G.markovBlanket A x v = true := by
  constructor
  · intro present
    obtain ⟨distinct, start, last, walk⟩ := (G.collider_augmented_iff _ _ _).mp present
    have head := collider_from_root_has_head lineFree sink walk
    subst start
    apply markovBlanket_iff.mpr
    refine ⟨Ne.symm distinct, ?_⟩
    have reached := collider_from_district walk (mem_inducedDistrict_self rootInside)
    cases last with
    | false => exact .inr reached
    | true => exact .inl reached
  · intro member
    obtain ⟨mark, walk⟩ :=
      blanket_collider_walk rootInside (markovBlanket_inside closed member) member
    exact (G.collider_augmented_iff _ _ _).mpr
      ⟨Ne.symm (markovBlanket_iff.mp member).1, true, mark, walk⟩

/-- A blanket together with its vertex is a clique in the augmentation. -/
theorem markovBlanket_clique {A : VertexMask n} {x u v : Fin n}
    (closed : G.AncestralSet A) (inside : A x = true)
    (left : u = x ∨ G.markovBlanket A x u = true)
    (right : v = x ∨ G.markovBlanket A x v = true) (ne : u ≠ v) :
    G.colliderAugmented A u v = true := by
  rcases left with rfl | left <;> rcases right with rfl | right
  · exact (ne rfl).elim
  · obtain ⟨m, h⟩ := blanket_collider_walk inside (markovBlanket_inside closed right) right
    exact (G.collider_augmented_iff _ _ _).mpr ⟨ne, true, m, h⟩
  · obtain ⟨m, h⟩ := blanket_collider_walk inside (markovBlanket_inside closed left) left
    exact (G.collider_augmented_iff _ _ _).mpr ⟨ne, m, true, h.reverse⟩
  · obtain ⟨a, h⟩ := blanket_collider_walk inside (markovBlanket_inside closed left) left
    obtain ⟨b, k⟩ := blanket_collider_walk inside (markovBlanket_inside closed right) right
    exact (G.collider_augmented_iff _ _ _).mpr ⟨ne, a, b, .join h.reverse k⟩

def outsideBlanket (G : MixedGraph n) (A : VertexMask n) (x : Fin n) : VertexMask n :=
  fun v => A v && (v != x) && !G.markovBlanket A x v

private theorem anterior_inside {A S : VertexMask n} (lineFree : G.NoLines)
    (closed : G.AncestralSet A) (sub : ∀ v, S v = true → A v = true)
    {v : Fin n} (path : G.AnteriorOf S v) : A v = true := by
  apply path.closed sub
  intro u w mark edge child
  cases mark with
  | false => exact (Bool.noConfusion ((lineFree u w).symm.trans edge))
  | true => exact closed u w child edge

private theorem enlarge_collider {A B : VertexMask n} {s t : Arrival n}
    (walk : G.ColliderWalk A s t) (sub : ∀ v, A v = true → B v = true) :
    G.ColliderWalk B s t := by
  induction walk with
  | single a b edge => exact .single (sub _ a) (sub _ b) edge
  | join _ _ ih1 ih2 => exact .join ih1 ih2

/-- The induced Markov blanket m-separates a childless vertex from the
remaining vertices of the ancestral set, even in the full graph. -/
theorem markovBlanket_separates {A : VertexMask n} {x : Fin n}
    (lineFree : G.NoLines) (closed : G.AncestralSet A) (inside : A x = true)
    (sink : G.ChildlessIn A x) :
    G.mSeparated (· == x) (G.outsideBlanket A x) (G.markovBlanket A x) = true := by
  let X : VertexMask n := (· == x)
  let Y := G.outsideBlanket A x
  let Z := G.markovBlanket A x
  let B := G.queryAnterior X Y Z
  have XB : ∀ v, X v = true → Z v = false := by
    intro v hv
    obtain rfl := beq_iff_eq.mp hv
    simp [Z, markovBlanket]
  have sub : ∀ v, B v = true → A v = true := by
    intro v hv
    apply anterior_inside lineFree closed _ ((G.anterior_iff _ _).mp hv)
    intro u hu
    rcases Bool.or_eq_true_iff.mp hu with endpoint | blank
    · rcases Bool.or_eq_true_iff.mp endpoint with root | other
      · obtain rfl := beq_iff_eq.mp root
        exact inside
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp other).1).1
    · exact markovBlanket_inside closed blank
  apply (G.m_separated_iff_no_walk X Y Z).mpr
  intro path
  obtain ⟨v, other, reaches⟩ := augmented_reachable_of_walkConnected XB path
  have reach : v = x ∨ Z v = true := by
    clear other
    induction reaches with
    | seed root => exact .inl (beq_iff_eq.mp root)
    | @step u v _ openU edge ih =>
      rcases ih with rfl | blocked
      · obtain ⟨distinct, h, k, collider⟩ := (G.collider_augmented_iff _ _ _).mp edge
        exact .inr ((collider_augmented_iff_markovBlanket lineFree closed inside sink).mp
          ((G.collider_augmented_iff _ _ _).mpr ⟨distinct, h, k, enlarge_collider collider sub⟩))
      · exact (openU blocked).elim
  rcases reach with rfl | blocked
  · simp [Y, outsideBlanket] at other
  · simp [Y, outsideBlanket, Z, blocked] at other

abbrev Independence (n : Nat) := VertexMask n → VertexMask n → VertexMask n → Prop

def GlobalMarkov (G : MixedGraph n) (J : Independence n) : Prop :=
  ∀ X Y Z : VertexMask n,
    (∀ v, X v = true → Y v = false ∧ Z v = false) →
    (∀ v, Y v = true → Z v = false) →
    G.mSeparated X Y Z = true → J X Y Z

def OrderedLocalMarkov (G : MixedGraph n) (rank : Fin n → Nat) (J : Independence n) :
    Prop :=
  ∀ ⦃x A⦄, G.AncestralSet A → A x = true → (∀ v, A v = true → rank v ≤ rank x) →
    J (· == x) (G.outsideBlanket A x) (G.markovBlanket A x)

/-- The global Markov property entails every statement of the ordered
local property, for a rank strictly increasing along directed edges. -/
theorem orderedLocal_of_globalMarkov {J : Independence n} {rank : Fin n → Nat}
    (lineFree : G.NoLines) (increases : ∀ u v, G.edge u false v true = true → rank u < rank v)
    (global : G.GlobalMarkov J) : G.OrderedLocalMarkov rank J := by
  intro x A closed present earlier
  have sink : G.ChildlessIn A x := by
    intro v member
    cases h : G.edge x false v true
    · rfl
    · exact (Nat.not_lt_of_ge (earlier v member) (increases x v h)).elim
  apply global
  · intro v hv
    obtain rfl := beq_iff_eq.mp hv
    simp [outsideBlanket, markovBlanket]
  · intro v hv
    apply Bool.eq_false_iff.mpr
    intro blocked
    simp [outsideBlanket, blocked] at hv
  · exact markovBlanket_separates lineFree closed present sink

end
end OpenCausalScience.MixedGraph
