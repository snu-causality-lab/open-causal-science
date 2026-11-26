module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Papers.Meek1995.Closure
public import OpenCausalScience.Papers.Meek1995.JoinTreeOrientation

/-! Reorient one undirected chain component while keeping the other
components and all intercomponent arrows. The component order and the
inheritance of fixed parents are explicit structural conditions. -/

namespace OpenCausalScience.Papers.Meek1995.ChainComponents

open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.JoinTreeOrientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n m : Nat}

/-- The numerical component labels are in a topological order. An
adjacency across components has a fixed orientation, and a fixed
parent of one vertex is a fixed parent of its entire component. -/
structure Components (base : DAG n) (fixed : Orientations n) where
  label : Fin n → Nat
  fixed_increases : ∀ u v, fixed u v → label u < label v
  directions_between : ∀ u v, Adjacent base u v → label u ≠ label v → fixed u v ∨ fixed v u
  inherits_parents : ∀ u v w, fixed u v → label v = label w → fixed u w


/-- A component may be presented by its undirected connectivity and
a topological ordering of the intercomponent arrows. -/
inductive OpenWalk (base : DAG n) (fixed : Orientations n) : Fin n → Fin n → Prop
  | stay (v) : OpenWalk base fixed v v
  | step {u v w} : OpenWalk base fixed u v → Unoriented base fixed v w → OpenWalk base fixed u w

/-- Along an undirected component, R1 saturation forces the parent
inheritance used in the chain graph and GES proofs. -/
def components_of_r1 {base : DAG n} {fixed : Orientations n}
    (label : Fin n → Nat)
    (orders : ∀ u v, fixed u v → label u < label v)
    (between : ∀ u v, Adjacent base u v → label u ≠ label v → fixed u v ∨ fixed v u)
    (connected : ∀ u v, label u = label v → OpenWalk base fixed u v)
    (closed : ∀ a b c, fixed a b → Unoriented base fixed b c → a ≠ c →
      ¬ Adjacent base a c → fixed b c) : Components base fixed where
  label := label
  fixed_increases := orders
  directions_between := between
  inherits_parents := by
    intro u v w fixedUV equal
    have follows {a b} (edge : Unoriented base fixed a b) : label a = label b := by
      by_cases same : label a = label b
      · exact same
      · exact ((between a b edge.1 same).elim edge.2.1 edge.2.2).elim
    have transfer {a b} (parent : fixed u a) (openEdge : Unoriented base fixed a b) :
        fixed u b := by
      have before : label u < label b := (follows openEdge) ▸ orders _ _ parent
      have other : u ≠ b := fun same => Nat.ne_of_lt before (congrArg label same)
      have adj : Adjacent base u b := by
        by_cases present : Adjacent base u b
        · exact present
        · exact (openEdge.2.1 (closed u a b parent openEdge other present)).elim
      exact (between u b adj (Nat.ne_of_lt before)).resolve_right fun reverse =>
        Nat.lt_asymm before (orders _ _ reverse)
    have followWalk {z} (path : OpenWalk base fixed v z) : fixed u z := by
      induction path with
      | stay => exact fixedUV
      | step _ openEdge ih => exact transfer ih openEdge
    exact followWalk (connected v w equal)
namespace Components

variable {base G : DAG n} {fixed : Orientations n}

def adjacency (components : Components base fixed) (c : Nat) (u v : Fin n) : Prop :=
  Adjacent base u v ∧ components.label u = c ∧ components.label v = c

theorem label_eq_of_unoriented (components : Components base fixed)
    {u v : Fin n} (edge : Unoriented base fixed u v) : components.label u = components.label v := by
  by_cases equal : components.label u = components.label v
  · exact equal
  · exact ((components.directions_between u v edge.1 equal).elim edge.2.1 edge.2.2).elim

theorem fixed_of_edge_between (components : Components base fixed) (ext : Extension base fixed G)
    {u v : Fin n} (edge : G.edge u v = true) (different : components.label u ≠ components.label v) :
    fixed u v := by
  have adj := (ext.skeleton u v).mpr (.inl edge)
  exact (components.directions_between u v adj different).resolve_right fun opposite =>
    G.no_directed_cycle u (.extend (.single edge) (ext.oriented _ _ opposite))

theorem label_le_of_edge (components : Components base fixed) (ext : Extension base fixed G)
    {u v : Fin n} (edge : G.edge u v = true) : components.label u ≤ components.label v := by
  by_cases equal : components.label u = components.label v
  · exact Nat.le_of_eq equal
  · exact Nat.le_of_lt (components.fixed_increases _ _
      (components.fixed_of_edge_between ext edge equal))

private theorem rank_between {span a b x y : Nat} (earlier : a < b) (bounded : x < span) :
    span * a + x < span * b + y := by
  have h := Nat.mul_le_mul_left span earlier
  rw [Nat.mul_succ] at h
  omega

/-- Any collider-free orientation of the component can be used in a
consistent extension of the full graph. -/
theorem replace_component (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (c : Nat) (H : DAG n)
    (shape : ∀ u v, Adjacent H u v ↔ components.adjacency c u v)
    (noColliders : ∀ u v w, ¬ UnshieldedCollider H u v w) :
    ∃ K : DAG n, Extension base fixed K ∧
      (∀ u v, components.label u = c → components.label v = c → K.edge u v = H.edge u v) := by
  let edge (u v : Fin n) :=
    if components.label u = c ∧ components.label v = c then H.edge u v else G.edge u v
  let localRank (u : Fin n) := if components.label u = c then H.rank u else G.rank u
  let span := G.rankBound + H.rankBound
  have bounded (u) : localRank u < span := by
    have old := G.rank_lt_bound u
    have new := H.rank_lt_bound u
    by_cases hu : components.label u = c <;> simp [localRank, hu, span] <;> omega
  let rank (u : Fin n) := span * components.label u + localRank u
  have increasing (u v) (h : edge u v = true) : rank u < rank v := by
    by_cases together : components.label u = c ∧ components.label v = c
    · have localEdge : H.edge u v = true := by simpa [edge, together] using h
      have localOrder := H.edge_increases _ _ localEdge
      simpa [rank, localRank, together.1, together.2] using localOrder
    · have oldEdge : G.edge u v = true := by simpa [edge, together] using h
      rcases Nat.lt_or_eq_of_le (components.label_le_of_edge ext oldEdge) with earlier | equal
      · exact rank_between earlier (bounded u)
      · have hu : components.label u ≠ c := fun hu => together ⟨hu, equal.symm.trans hu⟩
        have hv : components.label v ≠ c := fun hv => together ⟨equal.trans hv, hv⟩
        have oldOrder := G.edge_increases _ _ oldEdge
        simpa [rank, localRank, hu, hv, equal] using oldOrder
  let K : DAG n := ⟨edge, rank, increasing⟩
  have kept {u v} (outside : ¬ (components.label u = c ∧ components.label v = c)) :
      K.edge u v = G.edge u v := by simp [K, edge, outside]
  have installed {u v} (hu : components.label u = c) (hv : components.label v = c) :
      K.edge u v = H.edge u v := by simp [K, edge, hu, hv]
  have skeleton (u v) : Adjacent base u v ↔ Adjacent K u v := by
    by_cases together : components.label u = c ∧ components.label v = c
    · unfold Adjacent
      rw [installed together.1 together.2, installed together.2 together.1]
      change Adjacent base u v ↔ Adjacent H u v
      exact ⟨fun adj => (shape u v).mpr ⟨adj, together⟩, fun adj => ((shape u v).mp adj).1⟩
    · unfold Adjacent
      rw [kept together, kept (fun h => together h.symm)]
      exact ext.skeleton u v
  have oriented (u v) (h : fixed u v) : K.edge u v = true := by
    have before := components.fixed_increases u v h
    have notBoth : ¬ (components.label u = c ∧ components.label v = c) := by
      rintro ⟨hu, hv⟩
      omega
    rw [kept notBoth]
    exact ext.oriented u v h
  have noMixed {u v w} (hv : components.label v = c) (hu : components.label u ≠ c)
      (hw : components.label w = c) (collider : UnshieldedCollider K u v w) : False := by
    have old : G.edge u v = true := (kept (fun h => hu h.1)).symm ▸ collider.2.2.1
    have direction := components.fixed_of_edge_between ext old (fun equal => hu (equal.trans hv))
    have parent := components.inherits_parents u v w direction (hv.trans hw.symm)
    exact collider.2.1 (.inl (oriented u w parent))
  refine ⟨K, ⟨skeleton, ?_, oriented⟩, fun _ _ => installed⟩
  intro u v w
  constructor
  · intro collider
    have ⟨left, right⟩ := contains u v w collider
    exact ⟨collider.1, fun a => collider.2.1 ((skeleton u w).mpr a),
      oriented u v left, oriented w v right⟩
  · intro collider
    have sameBefore (h₁ : G.edge u v = true) (h₂ : G.edge w v = true) :
        UnshieldedCollider base u v w :=
      (ext.colliders u v w).mpr ⟨collider.1,
        fun a => collider.2.1 ((skeleton u w).mp ((ext.skeleton u w).mpr a)), h₁, h₂⟩
    by_cases hv : components.label v = c
    · by_cases hu : components.label u = c
      · by_cases hw : components.label w = c
        · have hAdj : ¬ Adjacent H u w := fun edge =>
            collider.2.1 ((skeleton u w).mp ((shape u w).mp edge).1)
          exact (noColliders u v w ⟨collider.1, hAdj,
            installed hu hv ▸ collider.2.2.1, installed hw hv ▸ collider.2.2.2⟩).elim
        · exact (noMixed hv hw hu
            ⟨collider.1.symm, fun rev => collider.2.1 (Or.symm rev),
              collider.2.2.2, collider.2.2.1⟩).elim
      · by_cases hw : components.label w = c
        · exact (noMixed hv hu hw collider).elim
        · exact sameBefore (kept (fun h => hu h.1) ▸ collider.2.2.1)
            (kept (fun h => hw h.1) ▸ collider.2.2.2)
    · exact sameBefore (kept (fun h => hv h.2) ▸ collider.2.2.1)
        (kept (fun h => hv h.2) ▸ collider.2.2.2)

/-- Realize a prescribed ordering of a clique in a chain-component
root bag, with all its remaining incident undirected edges pointing
outward. This is the selection used in the GES operator proofs. -/
theorem extend_with_root_clique (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (c : Nat) (tree : RootedJoinTree (components.adjacency c) m)
    (clique : Fin n → Prop) (inRoot : ∀ v, clique v → tree.inBag tree.root v)
    (priority : Fin n → Nat) :
    ∃ K : DAG n, Extension base fixed K ∧
      (∀ u v, clique u → clique v → priority u < priority v →
        components.adjacency c u v → K.edge u v = true) ∧
      (∀ u v, clique u → ¬ clique v → components.adjacency c u v → K.edge u v = true) := by
  obtain ⟨H, shape, noColliders, within, away⟩ := tree.orient_with_root_clique clique inRoot priority
  obtain ⟨K, consistent, installed⟩ := components.replace_component ext contains c H shape noColliders
  refine ⟨K, consistent, ?_, ?_⟩
  · intro u v hu hv precedes edge
    exact (installed u v edge.2.1 edge.2.2).symm ▸ within u v hu hv precedes edge
  · intro u v hu hv edge
    exact (installed u v edge.2.1 edge.2.2).symm ▸ away u v hu hv edge

/-- A root bag containing an undirected edge yields a consistent
extension with either orientation. -/
theorem directions_of_root_edge (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    {u v : Fin n} (openEdge : Unoriented base fixed u v)
    (tree : RootedJoinTree (components.adjacency (components.label v)) m)
    (hu : tree.inBag tree.root u) (hv : tree.inBag tree.root v) :
    (∃ L : DAG n, Extension base fixed L ∧ L.edge u v = true) ∧
    (∃ R : DAG n, Extension base fixed R ∧ R.edge v u = true) := by
  have different : u ≠ v := by
    intro eq
    subst v
    exact base.no_directed_cycle u (.single (openEdge.1.elim id id))
  have reverse : v ≠ u := fun e => different e.symm
  have together := components.label_eq_of_unoriented openEdge
  have inside : components.adjacency (components.label v) u v :=
    ⟨openEdge.1, together, rfl⟩
  let pair := fun w => w = u ∨ w = v
  have inRoot (w) (h : pair w) := h.elim (fun e => e.symm ▸ hu) (fun e => e.symm ▸ hv)
  constructor
  · let priority (w : Fin n) := if w = u then 0 else 1
    obtain ⟨L, keep, arrows, _⟩ := components.extend_with_root_clique ext contains _ tree pair inRoot priority
    exact ⟨L, keep, arrows u v (.inl rfl) (.inr rfl)
      (by simp [priority, reverse]) inside⟩
  · let priority (w : Fin n) := if w = v then 0 else 1
    obtain ⟨R, keep, arrows, _⟩ := components.extend_with_root_clique ext contains _ tree pair inRoot priority
    exact ⟨R, keep, arrows v u (.inr rfl) (.inl rfl)
      (by simp [priority, different]) ⟨Or.symm inside.1, inside.2.2, inside.2.1⟩⟩

/-- Maximal orientation for an extendible chain graph with the stated
parent inheritance and a rooted join tree available at each open edge.
The result compares the exact extension set of this partial orientation. -/
theorem open_iff_both_directions (components : Components base fixed)
    (ext : Extension base fixed G) (contains : ContainsColliders base fixed)
    (root_at_edge : ∀ u v, Unoriented base fixed u v →
      ∃ m, ∃ tree : RootedJoinTree (components.adjacency (components.label v)) m,
        tree.inBag tree.root u ∧ tree.inBag tree.root v)
    (u v : Fin n) :
    Unoriented base fixed u v ↔
      (∃ L : DAG n, Extension base fixed L ∧ L.edge u v = true) ∧
      (∃ R : DAG n, Extension base fixed R ∧ R.edge v u = true) := by
  constructor
  · intro openEdge
    obtain ⟨_, tree, hu, hv⟩ := root_at_edge u v openEdge
    exact components.directions_of_root_edge ext contains openEdge tree hu hv
  · rintro ⟨⟨L, left, forward⟩, ⟨R, right, backward⟩⟩
    exact ⟨(left.skeleton u v).mpr (.inl forward),
      fun f => R.no_directed_cycle v (.extend (.single backward) (right.oriented _ _ f)),
      fun b => L.no_directed_cycle u (.extend (.single forward) (left.oriented _ _ b))⟩

end Components
end
end OpenCausalScience.Papers.Meek1995.ChainComponents
