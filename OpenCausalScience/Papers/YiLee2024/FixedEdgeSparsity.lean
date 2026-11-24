module
public import Std

/-!
# Yi and Lee (2024), fixed-size graph supports

Appendix G of the 2026-09-19 corrected version counts supports with no edge
in either direction between the two vertices and at most one selected edge
in each of the remaining pairs of edges into another vertex. The coefficients
below count a choice of zero or one edge in each pair, then include the
unrestricted edges by convolution. The formula does not condition on the
subsequent eigenvalue restrictions.

Sources:
* https://proceedings.mlr.press/v238/yi24a.html
* https://www.sanghacklee.me/ai-corrected/FRP_AI_corrected_2026-09-19.pdf
-/

namespace OpenCausalScience.Papers.YiLee2024.FixedEdgeSparsity

@[expose] public section

/-- Choose exactly `k` unrestricted edges from `n` labeled edges. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n (k + 1) + choose n k

/-- Each of the `m` disjoint pairs contributes either no edge or one of two. -/
def pairWays : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k + 1 => pairWays m (k + 1) + 2 * pairWays m k

theorem pair_ways_eq (m k : Nat) : pairWays m k = choose m k * 2 ^ k := by
  induction m generalizing k with
  | zero => cases k <;> simp [pairWays, choose]
  | succ m ih =>
    cases k with
    | zero => simp [pairWays, choose]
    | succ k =>
      simp only [pairWays, choose, ih, Nat.add_mul, Nat.pow_succ]
      congr 1
      ac_rfl

/-- Count choices of exactly `k` edges by detaching one pair at a time. -/
def supportCount : Nat → Nat → Nat → Nat
  | 0, free, k => choose free k
  | _ + 1, _, 0 => 1
  | m + 1, free, k + 1 => supportCount m free (k + 1) + 2 * supportCount m free k

/-- The coefficient of degree `k` in the product of two coefficient sequences. -/
def convolve (a b : Nat → Nat) : Nat → Nat
  | 0 => a 0 * b 0
  | k + 1 => a 0 * b (k + 1) + convolve (fun r => a (r + 1)) b k

private def shift (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => a k

private theorem convolve_add (a c b : Nat → Nat) (k : Nat) :
    convolve (fun r => a r + c r) b k = convolve a b k + convolve c b k := by
  induction k generalizing a c with
  | zero => exact Nat.add_mul _ _ _
  | succ k ih =>
    simp only [convolve, Nat.add_mul, ih]
    ac_rfl

private theorem convolve_double (a b : Nat → Nat) (k : Nat) :
    convolve (fun r => 2 * a r) b k = 2 * convolve a b k := by
  induction k generalizing a <;> simp [convolve, Nat.mul_add, Nat.mul_assoc, *]

private theorem convolve_delta (b : Nat → Nat) (k : Nat) : convolve (pairWays 0) b k = b k := by
  have zero_convolve (j : Nat) : convolve (fun _ => 0) b j = 0 := by
    induction j <;> simp [convolve, *]
  cases k with
  | zero => simp [convolve, pairWays]
  | succ k => simp [convolve, pairWays, zero_convolve]

private theorem convolve_pair_ways (pairs free edges : Nat) :
    convolve (pairWays pairs) (choose free) edges = supportCount pairs free edges := by
  induction pairs generalizing edges with
  | zero => exact convolve_delta (choose free) edges
  | succ pairs ih =>
    have step : pairWays (pairs + 1) = fun r => pairWays pairs r + 2 * shift (pairWays pairs) r := by
      funext r
      cases r <;> simp [pairWays, shift]
    rw [step, convolve_add, convolve_double]
    cases edges with
    | zero => simp [convolve, shift, pairWays, choose, supportCount]
    | succ edges =>
      rw [supportCount, ← ih (edges + 1), ← ih edges]
      simp [convolve, shift]

/-- The numerator counts a split of the selected edges between the disjoint
pairs and the free edges. Degree `r` in the first factor counts choosing
`r` pairs and one endpoint in each. -/
theorem support_count_eq (pairs free edges : Nat) :
    supportCount pairs free edges =
      convolve (fun r => choose pairs r * 2 ^ r) (choose free) edges := by
  have eq : pairWays pairs = fun r => choose pairs r * 2 ^ r := funext (pair_ways_eq pairs)
  rw [← eq, convolve_pair_ways]

/-- Expected number of ordered zeros before rejection, under the generic
noncancellation assumption in Appendix G. The term `2` in `p = q + 2`
ensures there are two distinct vertices for a fixed pair. -/
def expectedZeros (q edges : Nat) : Rat :=
  let orderedPairs := (q + 2) * (q + 1)
  let freeEdges := (q + 1) * q
  (orderedPairs * supportCount q freeEdges edges : Nat) / (choose orderedPairs edges : Nat)

theorem expectation_three_vertices_two_edges : expectedZeros 1 2 = 2 := by decide +kernel

end
end OpenCausalScience.Papers.YiLee2024.FixedEdgeSparsity
