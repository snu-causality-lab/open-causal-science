module
public import OpenCausalScience.Papers.Chickering2002.Insert

/-! The Delete operator of Chickering (2002), Definition 13, Lemma 42,
and the necessity of the clique condition in Theorem 17. -/

namespace OpenCausalScience.Papers.Chickering2002.Delete

open OpenCausalScience.Papers.Chickering2002.Insert (Collider NeighborsAdjacentToSource Vertices)
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.Orientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

def removedAdjacency (x y a b : Fin n) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

def skeleton (base : DAG n) (x y a b : Fin n) : Prop :=
  Adjacent base a b ∧ ¬ removedAdjacency x y a b

def arrow (fixed : Orientations n) (x y : Fin n) (heads : Vertices n) (a b : Fin n) : Prop :=
  (fixed a b ∧ ¬ removedAdjacency x y a b) ∨ (heads b ∧ (a = x ∨ a = y))

def MatchesHeads (base G : DAG n) (fixed : Orientations n)
    (x y : Fin n) (heads : Vertices n) : Prop :=
  ∀ z, NeighborsAdjacentToSource base fixed x y z → (G.edge y z = true ↔ heads z)

structure Realizes (base : DAG n) (fixed : Orientations n) (x y : Fin n)
    (heads : Vertices n) (H : DAG n) : Prop where
  adjacency : ∀ a b, Adjacent H a b ↔ skeleton base x y a b
  directed : ∀ a b, arrow fixed x y heads a b → H.edge a b = true
  signature : ∀ a b c, UnshieldedCollider H a b c ↔
    Collider (skeleton base x y) (arrow fixed x y heads) a b c

variable {base G : DAG n} {fixed : Orientations n} {x y : Fin n} {heads : Vertices n}

private theorem opposite_absent (forward : G.edge x y = true) : G.edge y x ≠ true :=
  fun back => G.no_directed_cycle x (.extend (.single forward) back)

private theorem deleted_adjacency (ext : Extension base fixed G) (xy : G.edge x y = true)
    (a b : Fin n) : Adjacent (G.deleteArrow x y) a b ↔ skeleton base x y a b := by
  unfold skeleton removedAdjacency Adjacent
  rw [DAG.deleteArrow_edge_iff, DAG.deleteArrow_edge_iff]
  have shape := ext.skeleton a b
  unfold Adjacent at shape
  have back := opposite_absent xy
  grind

private theorem head_is_child_of_source (ext : Extension base fixed G) (xy : G.edge x y = true)
    {z : Fin n} (neighbor : NeighborsAdjacentToSource base fixed x y z) (yz : G.edge y z = true) :
    G.edge x z = true :=
  orient_along_directed_path (.extend (.single xy) yz) ((ext.skeleton x z).mp neighbor.2)

private theorem arrow_realized (ext : Extension base fixed G) (xy : G.edge x y = true)
    (valid : ∀ z, heads z → NeighborsAdjacentToSource base fixed x y z)
    (headMatch : MatchesHeads base G fixed x y heads) {a b : Fin n}
    (post : arrow fixed x y heads a b) : (G.deleteArrow x y).edge a b = true := by
  apply (G.deleteArrow_edge_iff _ _ _ _).mpr
  rcases post with ⟨prior, keep⟩ | ⟨head, eq | eq⟩
  · exact ⟨ext.oriented _ _ prior, fun pair => keep (.inl pair)⟩
  · subst a
    have yz := (headMatch b (valid b head)).mpr head
    exact ⟨head_is_child_of_source ext xy (valid b head) yz,
      fun pair => G.no_directed_cycle y (.single (pair.2 ▸ yz))⟩
  · subst a
    exact ⟨(headMatch b (valid b head)).mpr head,
      fun pair => G.no_directed_cycle x (.single (pair.1 ▸ xy))⟩

/-- The matching-heads direction of Lemma 42, with the compelled-child
triangle implication explicit. In a CPDAG this implication is supplied
by Chickering's reversible-edge and directed-path results. -/
theorem realized_of_matching_heads (ext : Extension base fixed G)
    (contains : ContainsColliders base fixed) (xy : G.edge x y = true)
    (valid : ∀ z, heads z → NeighborsAdjacentToSource base fixed x y z)
    (compelledChild : ∀ z, fixed y z → G.edge x z = true → fixed x z)
    (headMatch : MatchesHeads base G fixed x y heads) :
    Realizes base fixed x y heads (G.deleteArrow x y) := by
  refine ⟨deleted_adjacency ext xy, fun _ _ => arrow_realized ext xy valid headMatch, ?_⟩
  have newCollider {z : Fin n} (xz : G.edge x z = true) (yz : G.edge y z = true) :
      arrow fixed x y heads x z ∧ arrow fixed x y heads y z := by
    have zx : z ≠ x := fun eq => opposite_absent xy (eq ▸ yz)
    have zy : z ≠ y := fun eq => G.no_directed_cycle y (.single (eq ▸ yz))
    by_cases known : fixed y z
    · exact ⟨.inl ⟨compelledChild z known xz, fun cut => cut.elim
          (fun h => zy h.2) (fun h => zx h.2)⟩,
        .inl ⟨known, fun cut => cut.elim (fun h => zy h.2)
          (fun h => zx h.2)⟩⟩
    · have neighbor : NeighborsAdjacentToSource base fixed x y z :=
        ⟨⟨(ext.skeleton _ _).mpr (.inr yz),
          fun fixedBack => G.no_directed_cycle y
            (.extend (.single yz) (ext.oriented _ _ fixedBack)), known⟩,
          (ext.skeleton _ _).mpr (.inl xz)⟩
      have selected := (headMatch z neighbor).mp yz
      exact ⟨.inr ⟨selected, .inl rfl⟩, .inr ⟨selected, .inr rfl⟩⟩
  intro a b c
  constructor
  · rintro ⟨distinct, nonadjacent, left, right⟩
    have ha := (G.deleteArrow_edge_iff _ _ _ _).mp left
    have hc := (G.deleteArrow_edge_iff _ _ _ _).mp right
    have notAfter : ¬ skeleton base x y a c :=
      fun pa => nonadjacent ((deleted_adjacency ext xy a c).mpr pa)
    refine ⟨distinct, notAfter, ?_⟩
    by_cases absent : Adjacent base a c
    · have cut : removedAdjacency x y a c := Classical.byContradiction fun keep =>
        notAfter ⟨absent, keep⟩
      rcases cut with ⟨ax, cy⟩ | ⟨ay, cx⟩
      · subst a; subst c
        exact newCollider ha.1 hc.1
      · subst a; subst c
        exact And.symm (newCollider hc.1 ha.1)
    · have existing := contains a b c ((ext.colliders a b c).mpr
        ⟨distinct, fun adj => absent ((ext.skeleton _ _).mpr adj), ha.1, hc.1⟩)
      have keep {u v : Fin n} (uncut : ¬ (u = x ∧ v = y)) (prior : G.edge u v = true) :
          ¬ removedAdjacency x y u v := fun pair =>
        pair.elim uncut (by
          rintro ⟨rfl, rfl⟩
          exact opposite_absent xy prior)
      exact ⟨.inl ⟨existing.1, keep ha.2 ha.1⟩, .inl ⟨existing.2, keep hc.2 hc.1⟩⟩
  · rintro ⟨distinct, nonadjacent, left, right⟩
    exact ⟨distinct, fun adj => nonadjacent ((deleted_adjacency ext xy a c).mp adj),
      arrow_realized ext xy valid headMatch left, arrow_realized ext xy valid headMatch right⟩

/-- A successful Delete determines the heads by the new colliders
between the previously adjacent source and target. -/
theorem matching_heads_of_realized (ext : Extension base fixed G) (xy : G.edge x y = true)
    (realized : Realizes base fixed x y heads (G.deleteArrow x y)) :
    MatchesHeads base G fixed x y heads := by
  intro z neighbor
  have distinct : x ≠ y := fun eq => G.no_directed_cycle x (.single (eq.symm ▸ xy))
  constructor
  · intro child
    have notAdj : ¬ Adjacent (G.deleteArrow x y) x y := by
      intro adj
      exact ((realized.adjacency x y).mp adj).2 (.inl ⟨rfl, rfl⟩)
    have xz := head_is_child_of_source ext xy neighbor child
    have left := (G.deleteArrow_edge_iff x y x z).mpr
      ⟨xz, fun eq => G.no_directed_cycle y (.single (eq.2 ▸ child))⟩
    have right := (G.deleteArrow_edge_iff x y y z).mpr ⟨child, fun eq => distinct eq.1.symm⟩
    have shape := (realized.signature x z y).mp ⟨distinct, notAdj, left, right⟩
    exact shape.2.2.2.elim (fun old => (neighbor.1.2.2 old.1).elim) And.left
  · intro selected
    exact ((G.deleteArrow_edge_iff _ _ _ _).mp
      (realized.directed y z (.inr ⟨selected, .inr rfl⟩))).1

/-- The clique condition of Theorem 17 is necessary for a successful
Delete that comes from a single edit in a consistent extension. -/
theorem clique_of_realization (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (xy : G.edge x y = true) (realized : Realizes base fixed x y heads (G.deleteArrow x y))
    {a b : Fin n}
    (keptA : NeighborsAdjacentToSource base fixed x y a ∧ ¬ heads a)
    (keptB : NeighborsAdjacentToSource base fixed x y b ∧ ¬ heads b) (different : a ≠ b) :
    Adjacent base a b := by
  have oldParent {z : Fin n} (keep : NeighborsAdjacentToSource base fixed x y z ∧ ¬ heads z) :
      G.edge z y = true :=
    ((ext.skeleton _ _).mp keep.1.1.1).resolve_right fun child =>
      keep.2 ((matching_heads_of_realized ext xy realized z keep.1).mp child)
  by_cases adjacent : Adjacent base a b
  · exact adjacent
  · have made : UnshieldedCollider G a y b :=
      ⟨different, fun edge => adjacent ((ext.skeleton _ _).mpr edge), oldParent keptA, oldParent keptB⟩
    exact (keptA.1.1.2.1 (contains _ _ _ ((ext.colliders _ _ _).mpr made)).1).elim

end
end OpenCausalScience.Papers.Chickering2002.Delete
