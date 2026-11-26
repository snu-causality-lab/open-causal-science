module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyReachability

/-! # An ancestor fixed point obstructs fixing

Shpitser (2023), Proposition 1, describes a non-intrinsic c-component
as one whose reachable closure is strictly larger. This module proves
the following graph step. If the target C is contained in a bidirected
connected set T, and every vertex of T is an ancestor of C inside T,
no valid fixing order retaining C can remove any vertex of T.
This implication uses the graphical fixing rule alone.

Source: https://arxiv.org/pdf/2307.03750v1#page=7
-/

namespace OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability

@[expose] public section

variable {n : Nat}

def descendant (graph : MixedGraph n) (current : Vertices n) (root v : Fin n) : Prop :=
  Reached (fun a b => graph.edge a false b true) current (· == root) v

theorem Reached.extend_current {edge : Fin n → Fin n → Bool} {seeds : Fin n → Bool}
    {small large : Vertices n} (within : small ⊆ large) {v : Fin n}
    (path : Reached edge small seeds v) : Reached edge large seeds v := by
  induction path with
  | seed present selected => exact .seed (within present) selected
  | step _ present edge ih => exact .step ih (within present) edge

private theorem prepend_arrow {graph : MixedGraph n} {current : Vertices n} {u v w : Fin n}
    (present : u ∈ current) (edge : graph.edge u false v true = true)
    (suffix : descendant graph current v w) : descendant graph current u w := by
  induction suffix with
  | @seed a inside selected =>
    have same : a = v := beq_iff_eq.mp selected
    subst a
    exact .step (.seed present (beq_iff_eq.mpr rfl)) inside edge
  | step _ inside next ih => exact .step ih inside next

theorem ancestor_reaches_target (graph : MixedGraph n) (current target : Vertices n)
    {v : Fin n} (ancestor : v ∈ ancestors graph current target) :
    ∃ w ∈ target, descendant graph current v w := by
  have path := (mem_ancestors_iff graph current target v).mp ancestor
  clear ancestor
  induction path with
  | seed inside marked =>
    exact ⟨_, List.contains_iff_mem.mp marked, .seed inside (beq_iff_eq.mpr rfl)⟩
  | step _ inside edge ih =>
    obtain ⟨w, member, suffix⟩ := ih
    exact ⟨w, member, prepend_arrow inside edge suffix⟩

/-- In the current random graph, a fixable vertex has no other member of
its district among its directed descendants. -/
def Fixable (graph : MixedGraph n) (current : Vertices n) (v : Fin n) : Prop :=
  v ∈ current ∧ ∀ w, w ≠ v → descendant graph current v w →
    w ∉ district graph current v

def DistrictConnected (graph : MixedGraph n) (vertices : Vertices n) : Prop :=
  ∀ u ∈ vertices, ∀ v ∈ vertices, v ∈ district graph vertices u

theorem cannot_fix_inside_obstruction {graph : MixedGraph n}
    {current fixedPoint target : Vertices n} {v : Fin n}
    (inside : fixedPoint ⊆ current) (includes : target ⊆ fixedPoint)
    (connected : DistrictConnected graph fixedPoint)
    (ancestors_all : ∀ x ∈ fixedPoint, x ∈ ancestors graph fixedPoint target)
    (member : v ∈ fixedPoint) (outside : v ∉ target) : ¬ Fixable graph current v := by
  obtain ⟨w, inTarget, directed⟩ :=
    ancestor_reaches_target graph fixedPoint target (ancestors_all v member)
  have different : w ≠ v := fun same => outside (same ▸ inTarget)
  have districtSmall := (mem_district_iff graph fixedPoint v w).mp
    (connected v member w (includes inTarget))
  have districtLarge := (mem_district_iff graph current v w).mpr
    (Reached.extend_current inside districtSmall)
  intro fixable
  exact fixable.2 w different (Reached.extend_current inside directed) districtLarge

/-- A sequence of fixing operations avoiding the target variables. -/
inductive FixingOrder (graph : MixedGraph n) (target : Vertices n) :
    Vertices n → Vertices n → Prop
  | empty (current) : FixingOrder graph target current current
  | step {current final v} :
      Fixable graph current v → v ∉ target →
      FixingOrder graph target (current.filter (· != v)) final →
      FixingOrder graph target current final

theorem fixed_point_survives_fixing {graph : MixedGraph n}
    {source final fixedPoint target : Vertices n}
    (includes : target ⊆ fixedPoint) (connected : DistrictConnected graph fixedPoint)
    (ancestors_all : ∀ x ∈ fixedPoint, x ∈ ancestors graph fixedPoint target)
    (order : FixingOrder graph target source final) (inside : fixedPoint ⊆ source) :
    fixedPoint ⊆ final := by
  induction order with
  | empty => exact inside
  | @step current final v fixable outside _ ih =>
    have notInside : v ∉ fixedPoint := fun h =>
      cannot_fix_inside_obstruction inside includes connected ancestors_all h outside fixable
    apply ih
    intro w member
    have different : w ≠ v := fun same => notInside (same ▸ member)
    exact List.mem_filter.mpr ⟨inside member, bne_iff_ne.mpr different⟩

theorem proper_fixed_point_blocks_target {graph : MixedGraph n} {source fixedPoint target : Vertices n}
    (inside : fixedPoint ⊆ source) (includes : target ⊆ fixedPoint)
    (connected : DistrictConnected graph fixedPoint)
    (fixed : ancestors graph fixedPoint target = fixedPoint)
    (extra : ∃ v, v ∈ fixedPoint ∧ v ∉ target) :
    ¬ FixingOrder graph target source target := by
  intro order
  obtain ⟨v, inFixed, notTarget⟩ := extra
  exact notTarget (fixed_point_survives_fixing includes connected
    (fun x h => fixed.symm ▸ h) order inside inFixed)

end

end OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction
