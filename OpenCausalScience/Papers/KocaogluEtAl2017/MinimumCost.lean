module
public import OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign

/-! The optimal-cost argument behind Theorem 2 of Kocaoglu, Dimakis
and Vishwanath (2017). The number of experiments is unrestricted.
Nonnegative rational costs let the proof use Lean's standard library.

https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf -/

namespace OpenCausalScience.Papers.KocaogluEtAl2017.MinimumCost

open OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
open OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

def IsVertexCover (base : DAG n) (cover : Target n) : Prop :=
  ∀ u v, Adjacent base u v → cover u = true ∨ cover v = true

def targetUnion (design : List (Target n)) : Target n :=
  fun v => design.any (fun target => target v)

/-- Additive cost, grouped by vertex. Every experiment containing a
vertex pays that vertex's weight again. -/
def designCost (weight : Fin n → Rat) (design : List (Target n)) : Rat :=
  ((List.finRange n).map
    (fun v => weight v * ((design.countP fun target => target v) : Rat))).sum

def coverCost (weight : Fin n → Rat) (cover : Target n) : Rat :=
  ((List.finRange n).map (fun v => if cover v then weight v else 0)).sum

def singletonDesign (cover : Target n) : List (Target n) :=
  ((List.finRange n).filter cover).map (fun vertex v => vertex == v)

theorem union_is_vertex_cover {base : DAG n} {design : List (Target n)}
    (separates : SeparatesSkeleton base design) :
    IsVertexCover base (targetUnion design) := by
  intro u v adj
  obtain ⟨target, member, separated⟩ := separates u v adj
  cases hu : target u
  · right
    apply List.any_eq_true.mpr
    refine ⟨target, member, ?_⟩
    cases hv : target v
    · exact (separated (hu.trans hv.symm)).elim
    · rfl
  · exact .inl (List.any_eq_true.mpr ⟨target, member, hu⟩)

theorem singleton_design_separates {base : DAG n} {cover : Target n}
    (covers : IsVertexCover base cover) :
    SeparatesSkeleton base (singletonDesign cover) := by
  intro u v adj
  have distinct : u ≠ v := by
    intro equal
    subst v
    exact base.no_directed_cycle u (.single (adj.elim id id))
  have select {x : Fin n} (h : cover x = true) :
      (fun y => x == y) ∈ singletonDesign cover := by
    apply List.mem_map.mpr
    exact ⟨x, List.mem_filter.mpr ⟨List.mem_finRange _, h⟩, rfl⟩
  rcases covers u v adj with left | right
  · exact ⟨fun y => u == y, select left, by simpa using distinct⟩
  · exact ⟨fun y => v == y, select right, by simpa using distinct.symm⟩

private theorem sum_le_of_pointwise {α : Type} {f g : α → Rat}
    (bound : ∀ x, f x ≤ g x) (values : List α) :
    (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => exact Rat.le_refl
  | cons first rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Rat.le_trans (Rat.add_le_add_right.mpr (bound first)) (Rat.add_le_add_left.mpr ih)

theorem union_cost_le_design_cost (weight : Fin n → Rat) (nonnegative : ∀ v, 0 ≤ weight v)
    (design : List (Target n)) :
    coverCost weight (targetUnion design) ≤ designCost weight design := by
  unfold coverCost designCost
  apply sum_le_of_pointwise
  intro v
  cases reached : targetUnion design v
  · have nonnegCount : (0 : Rat) ≤ ((design.countP fun target => target v) : Rat) := by
      exact Rat.natCast_le_natCast.mpr (Nat.zero_le _)
    simpa [reached] using Rat.mul_le_mul_of_nonneg_left nonnegCount (nonnegative v)
  · have existsTarget := List.any_eq_true.mp reached
    have countPositive := List.countP_pos_iff.mpr existsTarget
    have atLeastOne : (1 : Rat) ≤ ((design.countP fun target => target v) : Rat) :=
      Rat.natCast_le_natCast.mpr countPositive
    simpa [reached] using Rat.mul_le_mul_of_nonneg_left atLeastOne (nonnegative v)

private theorem singleton_multiplicity (cover : Target n) (v : Fin n) :
    (singletonDesign cover).countP (fun target => target v) = if cover v then 1 else 0 := by
  let coveredVertices := (List.finRange n).filter cover
  have nodup : coveredVertices.Nodup := (List.nodup_finRange n).filter cover
  unfold singletonDesign
  rw [List.countP_map]
  change coveredVertices.count v = _
  rw [nodup.count]
  simp [coveredVertices, List.mem_filter]

theorem singleton_design_cost (weight : Fin n → Rat) (cover : Target n) :
    designCost weight (singletonDesign cover) = coverCost weight cover := by
  unfold designCost coverCost
  congr 1
  apply List.map_congr_left
  intro v _
  rw [singleton_multiplicity]
  cases cover v <;> simp

/-- For a minimum-weight vertex cover, intervening separately on each
selected vertex is optimal over all experiment designs. Grouping the
cover into color classes can reduce the number of experiments at the
same total cost. -/
theorem minimum_cover_gives_optimal_design {base : DAG n}
    (weight : Fin n → Rat) (nonnegative : ∀ v, 0 ≤ weight v)
    {cover : Target n} (covers : IsVertexCover base cover)
    (minimum : ∀ other, IsVertexCover base other → coverCost weight cover ≤ coverCost weight other) :
    IdentifiesEveryOrientation base (singletonDesign cover) ∧
      designCost weight (singletonDesign cover) = coverCost weight cover ∧
      ∀ design, IdentifiesEveryOrientation base design →
        coverCost weight cover ≤ designCost weight design := by
  refine ⟨(identifies_every_orientation_iff_separates_skeleton _ _).mpr
    (singleton_design_separates covers), singleton_design_cost weight cover, ?_⟩
  intro design identifies
  have separates := (identifies_every_orientation_iff_separates_skeleton _ _).mp identifies
  exact Rat.le_trans (minimum _ (union_is_vertex_cover separates))
    (union_cost_le_design_cost weight nonnegative design)

end
end OpenCausalScience.Papers.KocaogluEtAl2017.MinimumCost
