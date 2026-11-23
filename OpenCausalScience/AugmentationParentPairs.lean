module
public import Std

namespace OpenCausalScience.AugmentationParentPairs

public section

/-- Number of unordered checks performed by an explicit loop over all distinct
pairs of parents of one component. A check includes a lookup for an edge that
may already have been inserted for a previous component. -/
def pairs (parents : Nat) : Nat := parents * (parents - 1) / 2

/-- One entry per bidirected component, recording its parent count. -/
def checks (parentCounts : List Nat) : Nat := (parentCounts.map pairs).sum

private theorem pairs_le_square (parents bound : Nat) (h : parents ≤ bound) :
    pairs parents ≤ bound * bound := by
  calc
    pairs parents ≤ parents * (parents - 1) := Nat.div_le_self _ _
    _ ≤ bound * bound := Nat.mul_le_mul h (by omega)

/-- The total explicit pair checks are at most the number of components times
the square of the maximum permitted parent count. -/
theorem checks_le (parentCounts : List Nat) (bound : Nat)
    (h : ∀ count ∈ parentCounts, count ≤ bound) :
    checks parentCounts ≤ parentCounts.length * (bound * bound) := by
  induction parentCounts with
  | nil => simp [checks]
  | cons count rest ih =>
    have first := pairs_le_square count bound (h count (by simp))
    have remaining := ih (fun n hn => h n (by simp [hn]))
    simpa [checks, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add first remaining

/-- Witness graphs are two-layer DAGs on `3*n` vertices. The first `2*n`
vertices point to each of the last `n`, and there are no other arrows. -/
def arrow (n : Nat) (parent child : Fin (3 * n)) : Prop :=
  parent.val < 2 * n ∧ 2 * n ≤ child.val

/-- The last `n` vertices are singleton bidirected components with exactly
`2*n` parents each. The other singleton components have zero parents. -/
def witnessCounts (n : Nat) : List Nat := List.replicate n (2 * n)

theorem arrow_increases {n : Nat} {parent child : Fin (3 * n)}
    (h : arrow n parent child) : parent < child := by
  exact Nat.lt_of_lt_of_le h.1 h.2

private theorem sum_replicate (count value : Nat) :
    (List.replicate count value).sum = count * value := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

theorem witness_checks (n : Nat) : checks (witnessCounts n) = n * (n * (2 * n - 1)) := by
  have count : pairs (2 * n) = n * (2 * n - 1) := by
    unfold pairs
    rw [Nat.mul_assoc]
    omega
  simp only [checks, witnessCounts, List.map_replicate, count, sum_replicate]

/-- No constant multiple of the square of the total number of vertices bounds
this explicit per-component pair loop on the witness graphs. -/
theorem exceeds_quadratic (constant : Nat) :
    ∃ n, constant * ((3 * n) * (3 * n)) < checks (witnessCounts n) := by
  let n := 9 * constant + 1
  have pn : 0 < n := by omega
  have hl : 9 * constant < 2 * n - 1 := by omega
  refine ⟨n, ?_⟩
  rw [witness_checks]
  calc
    constant * ((3 * n) * (3 * n)) = (9 * constant) * (n * n) := by
      change constant * ((3 * n) * (3 * n)) = ((3 * 3) * constant) * (n * n)
      ac_rfl
    _ < (2 * n - 1) * (n * n) := Nat.mul_lt_mul_of_pos_right hl (Nat.mul_pos pn pn)
    _ = n * (n * (2 * n - 1)) := by ac_rfl

end

end OpenCausalScience.AugmentationParentPairs
