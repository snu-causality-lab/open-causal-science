module
public import OpenCausalScience.Graph.DSeparation

/-! # DEDUCE-DEP, UAI 2024

Kim, Hwang and Lee, PMLR 244:1999–2017, and the unofficial AI-corrected
version of 2026-09-20. This file checks the logical implication of
Corollary 1, the all-independent uncached call tree of Algorithm 1
(corrected Appendix D), and the order-zero change to Algorithm 3.

<https://proceedings.mlr.press/v244/kim24a.html>
<https://www.sanghacklee.me/ai-corrected/deduce_dep_AI_corrected_2026-09-20.pdf>
-/

namespace OpenCausalScience.Papers.KimEtAl2024.DeduceDep

@[expose] public section

/-- Line 10 uses `true` to mark dependence. -/
def deducesDependence (xy xw yw : Bool) : Bool :=
  xor xy (xw && yw)

theorem xor_criterion_iff (xy xw yw : Bool) :
    deducesDependence xy xw yw = true ↔
      (xy = true ∧ (xw = false ∨ yw = false)) ∨
      (xy = false ∧ xw = true ∧ yw = true) := by
  cases xy <;> cases xw <;> cases yw <;> decide

/-- Here `xy`, `xw`, and `yw` are the three lower-order independence claims,
and `givenW` is the target independence after adding the singleton `w`.
The first two implications are the two symmetric applications of
contraction followed by decomposition in Appendix B. -/
theorem dependence_of_lower_order_ci {xy xw yw givenW : Prop}
    (leftContraction : xw → givenW → xy)
    (rightContraction : yw → givenW → xy)
    (weakTransitivity : xy → givenW → xw ∨ yw)
    (premise : (¬ xy ∧ (xw ∨ yw)) ∨ (xy ∧ ¬ xw ∧ ¬ yw)) : ¬ givenW := by
  intro targetIndependent
  rcases premise with ⟨xyDep, h⟩ | ⟨xyInd, xwDep, ywDep⟩
  · cases h with
    | inl xwInd => exact xyDep (leftContraction xwInd targetIndependent)
    | inr ywInd => exact xyDep (rightContraction ywInd targetIndependent)
  · cases weakTransitivity xyInd targetIndependent with
    | inl xwInd => exact xwDep xwInd
    | inr ywInd => exact ywDep ywInd

/-- The return in Algorithm 1, line 3. `none` continues into the loop. -/
def cutoffResult (cutoff size : Nat) : Option Bool :=
  if size ≤ cutoff then some false else none

theorem marginal_cutoff (cutoff : Nat) : cutoffResult cutoff 0 = some false := by
  simp [cutoffResult]

/-- A pivot whose three lower-order marks are independent gives no deduction. -/
theorem all_independent_pivot : deducesDependence false false false = false := by
  decide

/-- Calls in the all-independent tree, including the current call. A root of
depth `d` has conditioning-set size `cutoff + d`. In this trace Algorithm 1
visits every pivot and makes three calls per pivot at the next lower order.
The count includes repeated recursive calls when only the CI answers are cached. -/
def allIndependentCalls (cutoff : Nat) : Nat → Nat
  | 0 => 1
  | depth + 1 => 1 + 3 * (cutoff + (depth + 1)) * allIndependentCalls cutoff depth

theorem calls_above_cutoff (cutoff size : Nat) (above : cutoff < size) :
    allIndependentCalls cutoff (size - cutoff) =
      1 + 3 * size * allIndependentCalls cutoff (size - 1 - cutoff) := by
  have depth : size - cutoff = (size - 1 - cutoff) + 1 := by omega
  have root : cutoff + ((size - 1 - cutoff) + 1) = size := by omega
  rw [depth, allIndependentCalls, root]

private theorem one_le_calls (cutoff depth : Nat) : 1 ≤ allIndependentCalls cutoff depth := by
  cases depth <;> simp [allIndependentCalls]

private theorem tail_lower_bound (cutoff base steps : Nat) :
    (2 * base) ^ steps ≤ allIndependentCalls cutoff (base + steps) := by
  induction steps with
  | zero => simpa using one_le_calls cutoff base
  | succ steps ih =>
    have factor : 2 * base ≤ 3 * (cutoff + (base + steps + 1)) := by omega
    have mulBound := Nat.mul_le_mul factor ih
    rw [Nat.pow_succ, Nat.mul_comm ((2 * base) ^ steps), Nat.add_succ, allIndependentCalls]
    omega

private theorem lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- Corrected Appendix D. For fixed cutoff the uncached call count is not
bounded by any constant times a fixed base raised to the depth. -/
theorem no_exponential_call_bound (cutoff constant base : Nat) :
    ∃ depth, constant * base ^ depth < allIndependentCalls cutoff depth := by
  by_cases zeroBase : base = 0
  · subst base
    refine ⟨1, ?_⟩
    have lowerBound := one_le_calls cutoff 1
    simp only [Nat.pow_one, Nat.mul_zero]
    omega
  · let steps := constant * base ^ base
    refine ⟨base + steps, ?_⟩
    have positive : 0 < base ^ steps := Nat.pow_pos (Nat.pos_of_ne_zero zeroBase)
    calc
      constant * base ^ (base + steps) = steps * base ^ steps := by
        rw [Nat.pow_add, ← Nat.mul_assoc]
      _ < 2 ^ steps * base ^ steps := Nat.mul_lt_mul_of_pos_right (lt_two_pow steps) positive
      _ = (2 * base) ^ steps := by rw [Nat.mul_pow]
      _ ≤ allIndependentCalls cutoff (base + steps) := tail_lower_bound cutoff base steps

/-- In a two-vertex graph the only potential conditioning set for the edge
is empty. This is the edge-removal branch of Algorithm 3 for this graph. -/
def edgeSurvivesOrder (order : Nat) (marginalIndependent : Bool) : Bool :=
  !(order == 0 && marginalIndependent)

def emptyDAG : DAG 2 where
  edge := fun _ _ => false
  rank := fun _ => 0
  edge_increases := by simp

def marginalIndependent : Bool := emptyDAG.dSeparated 0 1 [] == some true

theorem empty_dag_marginal_independence : marginalIndependent = true := by decide

/-- Starting at order one skips the only separating set. -/
theorem positive_orders_keep_spurious_edge (order : Nat) (positive : 0 < order) :
    edgeSurvivesOrder order marginalIndependent = true := by
  simp [edgeSurvivesOrder, Nat.ne_of_gt positive]

/-- The corrected order-zero pass removes the edge. For any nonnegative
cutoff, `marginal_cutoff` also rules out a deduction-based veto on this pass. -/
theorem zero_order_removes_spurious_edge :
    edgeSurvivesOrder 0 marginalIndependent = false := by decide

end

end OpenCausalScience.Papers.KimEtAl2024.DeduceDep
