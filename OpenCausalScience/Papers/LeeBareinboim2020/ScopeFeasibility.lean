module
public import Std

/-!
# Lee and Bareinboim (2020), deleting a vertex and retaining scope feasibility

Appendix F, p. A-19 of the 2026-09-20 corrected version gives the graph
`A → Y → Z → X → C` with `X ↔ Y`. The scope in the example replaces the
equation for `A` by a policy with input `C`. This file checks the directed
cycle, the acyclicity of the scope on the induced graph, and the reward
under every binary policy on the example's reduced model.

Sources:
* https://proceedings.neurips.cc/paper/2020/hash/61a10e6abb1149ad9d08f303267f9bc4-Abstract.html
* https://www.sanghacklee.me/ai-corrected/POMPS2020_AI_corrected_2026-09-20.pdf
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020.ScopeFeasibility

@[expose] public section

def a : Fin 5 := 0
def y : Fin 5 := 1
def z : Fin 5 := 2
def x : Fin 5 := 3
def c : Fin 5 := 4

def originalEdge (source target : Fin 5) : Bool :=
  (source == a && target == y) || (source == y && target == z) ||
    (source == z && target == x) || (source == x && target == c)

/-- `C → A` is inserted when the policy for `A` observes `C`.
If `X` is targeted as well, its incoming edge from `Z` is removed. -/
def scopedOriginal (targetX : Bool) (source target : Fin 5) : Bool :=
  (originalEdge source target && !(targetX && target == x)) || (source == c && target == a)

/-- `Z` is excluded from the induced graph by making it isolated. -/
def scopedReduced (source target : Fin 5) : Bool :=
  scopedOriginal false source target && !(source == z || target == z)

inductive Walk (edge : Fin 5 → Fin 5 → Bool) : Fin 5 → Fin 5 → Prop where
  | single {u v} : edge u v = true → Walk edge u v
  | extend {u v w} : Walk edge u v → edge v w = true → Walk edge u w

private theorem walk_increases {edge : Fin 5 → Fin 5 → Bool} (rank : Fin 5 → Nat)
    (edgeIncreases : ∀ u v, edge u v = true → rank u < rank v)
    {u v : Fin 5} (walk : Walk edge u v) : rank u < rank v := by
  induction walk with
  | single step => exact edgeIncreases _ _ step
  | extend _ step lower => exact Nat.lt_trans lower (edgeIncreases _ _ step)

theorem original_scope_has_cycle : Walk (scopedOriginal false) a a := by
  refine .extend (v := c) (.extend (v := x) (.extend (v := z) (.extend (v := y) ?_ ?_) ?_) ?_) ?_
  · exact .single (by decide)
  all_goals decide

private def reducedRank (v : Fin 5) : Nat := if v = x then 0 else if v = c then 1 else v.val + 2

theorem reduced_scope_is_acyclic (v : Fin 5) : ¬ Walk scopedReduced v v := by
  intro walk
  exact Nat.lt_irrefl _ (walk_increases reducedRank (by decide) walk)

theorem targeting_x_breaks_cycle (v : Fin 5) : ¬ Walk (scopedOriginal true) v v := by
  intro walk
  exact Nat.lt_irrefl _ (walk_increases reducedRank (by decide) walk)

/-- A policy for `X` cannot observe `C`, since it inserts the reverse of `X → C`. -/
theorem x_observing_c_has_cycle :
    Walk (fun source target => originalEdge source target || (source == c && target == x)) x x :=
  .extend (v := c) (.single (by decide)) (by decide)

/-- In the reduced SCM, `X = U` unless intervened on, `C = X`, and
`Y = 1{A = U}`. The fair bit `U` has two values, so the expectation is the
number of matches divided by two. A policy for `A` is given by its two outputs. -/
def rewardNumerator (targetX : Option Bool) (actionAtFalse actionAtTrue : Bool) : Nat :=
  let reward (u : Bool) :=
    let context := targetX.getD u
    let action := if context then actionAtTrue else actionAtFalse
    if action = u then 1 else 0
  reward false + reward true

theorem observing_c_attains_one : rewardNumerator none false true = 2 := by decide

theorem constant_a_attains_half (action : Bool) : rewardNumerator none action action = 1 := by
  cases action <;> decide

theorem targeting_x_leaves_half (xValue actionAtFalse actionAtTrue : Bool) :
    rewardNumerator (some xValue) actionAtFalse actionAtTrue = 1 := by
  cases xValue <;> cases actionAtFalse <;> cases actionAtTrue <;> decide

end
end OpenCausalScience.Papers.LeeBareinboim2020.ScopeFeasibility
