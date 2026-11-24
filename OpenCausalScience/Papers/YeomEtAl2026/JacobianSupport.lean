module
public import Std

/-! # Jacobian support of normalizing flows

[Yeom et al., corrected version](https://www.sanghacklee.me/ai-corrected/TSCNF_AI_corrected_2026-10-15.pdf),
Appendix B.3, Corollaries 1–2. The path-sum implication here takes a
chain-rule expansion and the local derivative zero restriction as hypotheses.
Integer local coefficients suffice for the cancellation example from Appendix
B.3. The formalization does not derive the expansion from differentiability.
-/

namespace OpenCausalScience.Papers.YeomEtAl2026.JacobianSupport

@[expose] public section

/-- A composable sequence of potential directed edges. -/
inductive Walk {α : Type} : α → α → List (α × α) → Prop where
  | nil (x : α) : Walk x x []
  | cons {x y z : α} {tail : List (α × α)} : Walk y z tail → Walk x z ((x, y) :: tail)

inductive DirectedWalk {α : Type} (edge : α → α → Prop) : α → α → Prop where
  | nil (x : α) : DirectedWalk edge x x
  | cons {x y z : α} : edge x y → DirectedWalk edge y z → DirectedWalk edge x z

def pathWeight {α : Type} (slope : α → α → Int) : List (α × α) → Int
  | [] => 1
  | (source, target) :: tail => slope source target * pathWeight slope tail

private theorem directed_of_nonzero_weight {α : Type} {edge : α → α → Prop}
    {slope : α → α → Int} (support : ∀ x y, slope x y ≠ 0 → edge x y)
    {x y : α} {path : List (α × α)} (walk : Walk x y path)
    (weight : pathWeight slope path ≠ 0) : DirectedWalk edge x y := by
  induction walk with
  | nil x => exact .nil x
  | @cons x middle y tail _ ih =>
    apply DirectedWalk.cons (y := middle)
    · apply support
      intro h
      exact weight (by simp [pathWeight, h])
    · apply ih
      intro h
      exact weight (by simp [pathWeight, h])

def pathSum {α : Type} (slope : α → α → Int) : List (List (α × α)) → Int
  | [] => 0
  | path :: paths => pathWeight slope path + pathSum slope paths

/-- A nonzero entry expanded as a finite sum of path weights is supported on
an ancestor or the diagonal. The input includes the empty path on the diagonal
if the expansion assigns a diagonal term. -/
theorem ancestor_of_nonzero_path_sum {α : Type} {edge : α → α → Prop}
    {slope : α → α → Int} (support : ∀ x y, slope x y ≠ 0 → edge x y)
    {x y : α} {paths : List (List (α × α))}
    (walks : ∀ path ∈ paths, Walk x y path) (weight : pathSum slope paths ≠ 0) :
    DirectedWalk edge x y := by
  induction paths with
  | nil => exact False.elim (weight rfl)
  | cons path paths ih =>
    by_cases hw : pathWeight slope path = 0
    · apply ih (fun walk hw => walks walk (List.mem_cons_of_mem _ hw))
      simpa [pathSum, hw] using weight
    · exact directed_of_nonzero_weight support (walks path (List.mem_cons_self ..)) hw

/-- The inverse coordinate of a unit-diagonal linear structural system depends
only on its own coordinate and the local parents. -/
theorem inverse_support {α : Type} [DecidableEq α] {edge : α → α → Prop}
    {slope : α → α → Int} (support : ∀ x y, slope x y ≠ 0 → edge x y)
    {source target : α} (nonzero : (if source = target then 1 else -slope source target) ≠ 0) :
    source = target ∨ edge source target := by
  by_cases same : source = target
  · exact Or.inl same
  · refine Or.inr (support _ _ ?_)
    intro zero
    exact nonzero (by simp [same, zero])

def exampleSlope (source target : Nat) : Int :=
  if (source, target) = (1, 2) ∨ (source, target) = (2, 3) then 1
  else if (source, target) = (1, 3) then -1 else 0

/-- In `X₁ = Z₁`, `X₂ = X₁ + Z₂`, `X₃ = X₂ - X₁ + Z₃`, the direct path
and the path via `X₂` have nonzero weights that sum to zero. -/
theorem ancestor_derivative_cancels :
    DirectedWalk (fun x y => exampleSlope x y ≠ 0) 1 3 ∧
    pathWeight exampleSlope [(1, 3)] ≠ 0 ∧
    pathWeight exampleSlope [(1, 2), (2, 3)] ≠ 0 ∧
    pathSum exampleSlope [[(1, 3)], [(1, 2), (2, 3)]] = 0 := by
  exact ⟨.cons (y := 3) (by decide) (.nil 3), by decide, by decide, by decide⟩

end

end OpenCausalScience.Papers.YeomEtAl2026.JacobianSupport
