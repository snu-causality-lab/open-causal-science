module
public import OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign

/-! Figure 1 and Proposition 1 of Kocaoglu, Dimakis and Vishwanath (2017).
The source vertices U1 through U5 use Fin indices 0 through 4.

https://proceedings.mlr.press/v70/kocaoglu17a/kocaoglu17a.pdf#page=6 -/

namespace OpenCausalScience.Papers.KocaogluEtAl2017.Figure1

open OpenCausalScience.Papers.HauserBuhlmann2012.InterventionalEquivalence
open OpenCausalScience.Papers.KocaogluEtAl2017.SeparatingDesign
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

def skeletonRepresentative : DAG 5 where
  edge u v := ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3)] :
      List (Fin 5 × Fin 5)).contains (u, v)
  rank u := u.val
  edge_increases := by decide

def graphDesign : List (Target 5) :=
  [fun u => u == 0 || u == 2, fun u => u == 1 || u == 2]

def colorDesign : List (Target 5) :=
  [fun u => u == 0, fun u => u == 1 || u == 3]

theorem both_designs_separate_skeleton :
    SeparatesSkeleton skeletonRepresentative graphDesign ∧
      SeparatesSkeleton skeletonRepresentative colorDesign :=
  ⟨(separatesCheck_iff _ _).mp (by decide), (separatesCheck_iff _ _).mp (by decide)⟩

theorem graph_design_does_not_separate_u4_u5 :
    ∀ target ∈ graphDesign, target 3 = target 4 := by
  intro target member
  simp only [graphDesign, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

private theorem remaining_color_unique :
    ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide

/-- Every proper three-coloring gives U4 and U5 distinct colors. -/
theorem u4_u5_different_colors (color : Fin 5 → Fin 3)
    (proper : ∀ u v, Adjacent skeletonRepresentative u v → color u ≠ color v) :
    color 3 ≠ color 4 := by
  have u4 := remaining_color_unique (color 0) (color 2) (color 3) (color 1)
    (proper 0 2 (.inl rfl)) (proper 0 3 (.inl rfl)).symm (proper 2 3 (.inl rfl)).symm
    (proper 0 1 (.inl rfl)).symm (proper 1 2 (.inl rfl))
  have u5 := remaining_color_unique (color 0) (color 1) (color 4) (color 2)
    (proper 0 1 (.inl rfl)) (proper 0 4 (.inl rfl)).symm (proper 1 4 (.inl rfl)).symm
    (proper 0 2 (.inl rfl)).symm (proper 1 2 (.inl rfl)).symm
  rw [u4, u5]
  exact proper 1 2 (.inl rfl)

/-- The left-hand design in Figure 1(b) is graph separating even though
it fails to separate all distinct color classes of any proper 3-coloring. -/
theorem no_compatible_three_coloring (color : Fin 5 → Fin 3)
    (proper : ∀ u v, Adjacent skeletonRepresentative u v → color u ≠ color v) :
    ¬ (∀ u v, color u ≠ color v → ∃ t ∈ graphDesign, t u ≠ t v) := by
  intro colorSeparated
  obtain ⟨target, member, distinct⟩ := colorSeparated 3 4 (u4_u5_different_colors color proper)
  exact distinct (graph_design_does_not_separate_u4_u5 target member)

end
end OpenCausalScience.Papers.KocaogluEtAl2017.Figure1
