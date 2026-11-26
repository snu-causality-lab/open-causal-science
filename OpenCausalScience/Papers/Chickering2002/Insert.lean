module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Papers.Meek1995.Closure

/-! The Insert operator of Chickering (2002), Definition 12, Lemma 41,
and Theorem 15. A selected consistent extension realizes the exact new
skeleton and unshielded colliders. The semidirected blocking condition
ensures that the DAG edit can be made without introducing a cycle. -/

namespace OpenCausalScience.Papers.Chickering2002.Insert

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

abbrev Vertices (n : Nat) := Fin n → Prop

structure Choice (base : DAG n) (fixed : Orientations n) (x y : Fin n)
    (tails : Vertices n) : Prop where
  distinct : x ≠ y
  nonadjacent : ¬ Adjacent base x y
  valid : ∀ v, tails v → Unoriented base fixed v y ∧ ¬ Adjacent base x v

def NeighborsAdjacentToSource (base : DAG n) (fixed : Orientations n)
    (x y z : Fin n) : Prop :=
  Unoriented base fixed z y ∧ Adjacent base x z

def MatchesTails (base G : DAG n) (fixed : Orientations n)
    (x y : Fin n) (tails : Vertices n) : Prop :=
  ∀ z, Unoriented base fixed z y → ¬ Adjacent base x z → (G.edge z y = true ↔ tails z)

def skeleton (base : DAG n) (x y a b : Fin n) : Prop :=
  Adjacent base a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)

def arrow (fixed : Orientations n) (x y : Fin n) (tails : Vertices n) (a b : Fin n) : Prop :=
  fixed a b ∨ (a = x ∧ b = y) ∨ (tails a ∧ b = y)

def Collider (adjacent directed : Orientations n) (a b c : Fin n) : Prop :=
  a ≠ c ∧ ¬ adjacent a c ∧ directed a b ∧ directed c b

structure Realizes (base : DAG n) (fixed : Orientations n) (x y : Fin n)
    (tails : Vertices n) (H : DAG n) : Prop where
  adjacency : ∀ a b, Adjacent H a b ↔ skeleton base x y a b
  directed : ∀ a b, arrow fixed x y tails a b → H.edge a b = true
  signature : ∀ a b c, UnshieldedCollider H a b c ↔
    Collider (skeleton base x y) (arrow fixed x y tails) a b c

variable {base G H : DAG n} {fixed : Orientations n} {x y : Fin n} {tails : Vertices n}

private theorem inserted_adjacency (ext : Extension base fixed G) (inserted : G.IsInsertion H x y)
    (a b : Fin n) : Adjacent H a b ↔ skeleton base x y a b := by
  unfold skeleton Adjacent
  rw [inserted, inserted]
  have same := ext.skeleton a b
  unfold Adjacent at same
  grind

private theorem new_arrow (ext : Extension base fixed G)
    (choice : Choice base fixed x y tails) (tailMatch : MatchesTails base G fixed x y tails)
    (inserted : G.IsInsertion H x y) {a b : Fin n}
    (new : arrow fixed x y tails a b) : H.edge a b = true := by
  apply (inserted a b).mpr
  rcases new with old | added | ⟨tail, eq⟩
  · exact .inl (ext.oriented _ _ old)
  · exact .inr added
  · subst b
    obtain ⟨neighbor, unshielded⟩ := choice.valid a tail
    exact .inl ((tailMatch a neighbor unshielded).mpr tail)

private theorem other_parent (ext : Extension base fixed G)
    (tailMatch : MatchesTails base G fixed x y tails)
    {v : Fin n} (nonadjacent : ¬ Adjacent base x v) (parent : G.edge v y = true) :
    arrow fixed x y tails v y := by
  by_cases known : fixed v y
  · exact .inl known
  · have notOpposite : ¬ fixed y v :=
      fun reverse => G.no_directed_cycle v (.extend (.single parent) (ext.oriented _ _ reverse))
    have adj := (ext.skeleton v y).mpr (.inl parent)
    exact .inr (.inr ⟨(tailMatch v ⟨adj, known, notOpposite⟩ nonadjacent).mp parent, rfl⟩)

/-- The matching-tails direction of Lemma 41. An acyclic single-arrow
insertion into a consistent extension produces exactly the adjacency,
oriented edges, and unshielded colliders of Insert(X,Y,T). -/
theorem realized_of_matching_tails (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed)
    (choice : Choice base fixed x y tails) (tailMatch : MatchesTails base G fixed x y tails)
    (inserted : G.IsInsertion H x y) : Realizes base fixed x y tails H := by
  refine ⟨inserted_adjacency ext inserted, fun _ _ => new_arrow ext choice tailMatch inserted, ?_⟩
  intro a b c
  constructor
  · rintro ⟨different, nonadjacent, left, right⟩
    have nonadj : ¬ skeleton base x y a c :=
      fun adj => nonadjacent ((inserted_adjacency ext inserted a c).mpr adj)
    have baseNonadj : ¬ Adjacent base a c := fun adj => nonadj (.inl adj)
    refine ⟨different, nonadj, ?_⟩
    rcases (inserted a b).mp left with oldLeft | ⟨ax, byy⟩
    · rcases (inserted c b).mp right with oldRight | ⟨cx, byy⟩
      · have oldCollider : UnshieldedCollider G a b c :=
          ⟨different, fun adj => baseNonadj ((ext.skeleton a c).mpr adj), oldLeft, oldRight⟩
        have existed := contains a b c ((ext.colliders a b c).mpr oldCollider)
        exact ⟨.inl existed.1, .inl existed.2⟩
      · subst c
        subst b
        exact ⟨other_parent ext tailMatch (fun adj => baseNonadj (Or.symm adj)) oldLeft,
          .inr (.inl ⟨rfl, rfl⟩)⟩
    · subst a
      subst b
      rcases (inserted c y).mp right with oldRight | ⟨cx, _⟩
      · exact ⟨.inr (.inl ⟨rfl, rfl⟩), other_parent ext tailMatch baseNonadj oldRight⟩
      · exact (different cx.symm).elim
  · rintro ⟨different, nonadjacent, left, right⟩
    exact ⟨different, fun adj => nonadjacent ((inserted_adjacency ext inserted a c).mp adj),
      new_arrow ext choice tailMatch inserted left, new_arrow ext choice tailMatch inserted right⟩

/-- The reverse implication of Lemma 41. The new unshielded collider
at the target detects each reversible, unshielded parent. -/
theorem matching_tails_of_realized (choice : Choice base fixed x y tails)
    (inserted : G.IsInsertion H x y) (realized : Realizes base fixed x y tails H) :
    MatchesTails base G fixed x y tails := by
  intro z neighbor unshielded
  have zx : z ≠ x := fun eq => choice.nonadjacent (eq ▸ neighbor.1)
  have zy : z ≠ y := by
    intro eq
    subst z
    exact base.no_directed_cycle y (.single (neighbor.1.elim id id))
  constructor
  · intro parent
    have unshieldedAfter : ¬ Adjacent H x z := by
      intro adj
      rcases (realized.adjacency x z).mp adj with previous | ⟨_, eq⟩ | ⟨eq, _⟩
      · exact unshielded previous
      · exact zy eq
      · exact choice.distinct eq
    have left := (inserted x y).mpr (.inr ⟨rfl, rfl⟩)
    have right := (inserted z y).mpr (.inl parent)
    have changed := (realized.signature x y z).mp ⟨zx.symm, unshieldedAfter, left, right⟩
    rcases changed.2.2.2 with old | ⟨eq, _⟩ | ⟨chosen, _⟩
    · exact (neighbor.2.1 old).elim
    · exact (zx eq).elim
    · exact chosen
  · intro chosen
    have edge := realized.directed z y (.inr (.inr ⟨chosen, rfl⟩))
    exact ((inserted z y).mp edge).resolve_right (fun eq => zx eq.1)

/-- Reversible neighbors of Y that are adjacent to X must be parents of
Y in any single-edge Insert witness. -/
theorem common_neighbor_is_parent (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed)
    (choice : Choice base fixed x y tails) (inserted : G.IsInsertion H x y)
    {z : Fin n} (neighbor : NeighborsAdjacentToSource base fixed x y z) :
    G.edge z y = true := by
  rcases (ext.skeleton z y).mp neighbor.1.1 with toward | away
  · exact toward
  · rcases (ext.skeleton x z).mp neighbor.2 with xz | zx
    · have added : UnshieldedCollider G x z y :=
        ⟨choice.distinct, fun adj => choice.nonadjacent ((ext.skeleton x y).mpr adj), xz, away⟩
      exact (neighbor.1.2.2 (contains _ _ _ ((ext.colliders _ _ _).mpr added)).2).elim
    · have front := (inserted x y).mpr (.inr ⟨rfl, rfl⟩)
      have yz := (inserted y z).mpr (.inl away)
      have back := (inserted z x).mpr (.inl zx)
      exact (H.no_directed_cycle x (.extend (.extend (.single front) yz) back)).elim

/-- The clique condition of Theorem 15 is necessary for a successful
Insert that comes from a single edit in a consistent extension. -/
theorem clique_of_realization (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed)
    (choice : Choice base fixed x y tails) (inserted : G.IsInsertion H x y)
    (realized : Realizes base fixed x y tails H) {a b : Fin n}
    (aSelected : NeighborsAdjacentToSource base fixed x y a ∨ tails a)
    (bSelected : NeighborsAdjacentToSource base fixed x y b ∨ tails b) (distinct : a ≠ b) :
    Adjacent base a b := by
  have openA := aSelected.elim And.left (fun picked => (choice.valid a picked).1)
  have aParent := aSelected.elim (common_neighbor_is_parent ext contains choice inserted)
    (fun picked => ((matching_tails_of_realized choice inserted realized) a openA
      (choice.valid a picked).2).mpr picked)
  have bParent := bSelected.elim (common_neighbor_is_parent ext contains choice inserted)
    (fun picked => ((matching_tails_of_realized choice inserted realized) b (choice.valid b picked).1
      (choice.valid b picked).2).mpr picked)
  by_cases adjacent : Adjacent base a b
  · exact adjacent
  · have made : UnshieldedCollider G a y b :=
      ⟨distinct, fun edge => adjacent ((ext.skeleton _ _).mpr edge), aParent, bParent⟩
    exact (openA.2.1 (contains _ _ _ ((ext.colliders _ _ _).mpr made)).1).elim

/-- A semidirected walk may follow assigned arrows or an unassigned
edge. Every vertex on an avoiding walk is outside the specified set. -/
inductive AvoidingWalk (base : DAG n) (fixed : Orientations n)
    (blocked : Vertices n) : Fin n → Fin n → Prop
  | single {u v} : ¬ blocked u → ¬ blocked v → Adjacent base u v →
      ¬ fixed v u → AvoidingWalk base fixed blocked u v
  | extend {u v w} : AvoidingWalk base fixed blocked u v → ¬ blocked w →
      Adjacent base v w → ¬ fixed w v → AvoidingWalk base fixed blocked u w

private theorem old_arrow_semidirected (ext : Extension base fixed G) {u v : Fin n}
    (edge : G.edge u v = true) : Adjacent base u v ∧ ¬ fixed v u :=
  ⟨(ext.skeleton _ _).mpr (.inl edge),
    fun reversed => G.no_directed_cycle u (.extend (.single edge) (ext.oriented _ _ reversed))⟩

private theorem directed_path_avoids_parents (ext : Extension base fixed G)
    {blocked : Vertices n} (parents : ∀ v, blocked v → G.edge v y = true)
    {w : Fin n} (path : G.DirectedWalk y w) : AvoidingWalk base fixed blocked y w := by
  induction path with
  | @single dst edge =>
    exact .single
      (fun hy => G.no_directed_cycle y (.single (parents y hy)))
      (fun hd => G.no_directed_cycle y (.extend (.single edge) (parents dst hd)))
      (old_arrow_semidirected ext edge).1 (old_arrow_semidirected ext edge).2
  | @extend mid dst initial edge ih =>
    exact .extend ih
      (fun hd => G.no_directed_cycle y (.extend (.extend initial edge) (parents dst hd)))
      (old_arrow_semidirected ext edge).1 (old_arrow_semidirected ext edge).2

/-- With the parent configuration promised by Chickering's clique
extension lemma, the semidirected blocking test suffices to realize
Insert as a single acyclic edit. -/
theorem exists_realization_of_selected_extension (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed)
    (choice : Choice base fixed x y tails) (tailMatch : MatchesTails base G fixed x y tails)
    (parents : ∀ v, NeighborsAdjacentToSource base fixed x y v ∨ tails v → G.edge v y = true)
    (blocked : ¬ AvoidingWalk base fixed
      (fun v => NeighborsAdjacentToSource base fixed x y v ∨ tails v) y x) :
    ∃ H : DAG n, G.IsInsertion H x y ∧ Realizes base fixed x y tails H := by
  have noBack : ¬ G.DirectedWalk y x := fun p => blocked (directed_path_avoids_parents ext parents p)
  obtain ⟨H, inserted⟩ := (G.exists_insertion_iff choice.distinct).mpr noBack
  exact ⟨H, inserted, realized_of_matching_tails ext contains choice tailMatch inserted⟩

end
end OpenCausalScience.Papers.Chickering2002.Insert
