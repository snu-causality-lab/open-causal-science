module
public import OpenCausalScience.Papers.RaskuttiUhler2018.Figure1
public import OpenCausalScience.Papers.RaskuttiUhler2018.SparsestPermutation

/-! # An exact positive finite law for the Figure 1 comparison

The two transition probabilities in the chain are 1/4 and 3/4. The final
node has probability 1/4 + X3/2 − X1/8 of being 1. The mass table has
common denominator 256, so CI cross-products use integer numerators.
-/

namespace OpenCausalScience.Papers.RaskuttiUhler2018.Figure1

@[expose] public section

def worlds : List (BitVec 4) := (List.finRange 16).map BitVec.ofFin

def cellNumerator (bits : BitVec 4) : Nat :=
  let x1 := bits.getLsbD 0
  let x2 := bits.getLsbD 1
  let x3 := bits.getLsbD 2
  let x4 := bits.getLsbD 3
  let final : Nat := (if x1 then 1 else 2) + (if x3 then 4 else 0)
  (if x1 == x2 then 3 else 1) * (if x2 == x3 then 3 else 1) *
    (if x4 then final else 8 - final)

def eventNumerator (event : BitVec 4 → Bool) : Nat :=
  (worlds.map fun w => if event w then cellNumerator w else 0).sum

theorem distribution_positive_normalized :
    eventNumerator (fun _ => true) = 256 ∧ ∀ a : Fin 16, 0 < cellNumerator (BitVec.ofFin a) := by
  decide +kernel

def independentInLaw (x y : Fin 4) (mask : BitVec 4) : Bool :=
  worlds.all fun assignment =>
    let condition := fun w : BitVec 4 => (w &&& mask) == (assignment &&& mask)
    let left := fun w : BitVec 4 => w.getLsbD x.val == assignment.getLsbD x.val
    let right := fun w : BitVec 4 => w.getLsbD y.val == assignment.getLsbD y.val
    eventNumerator (fun w => condition w && left w && right w) * eventNumerator condition ==
      eventNumerator (fun w => condition w && left w) * eventNumerator (fun w => condition w && right w)

/-- Each admissible singleton CI query in the example agrees with the
strictly positive mass table, including the additional marginal CI. -/
theorem distribution_realizes_figure_oracle :
    ∀ x y : Fin 4, ∀ assignment : Fin 16, x ≠ y →
      (BitVec.ofFin (w := 4) assignment).getLsbD x.val = false →
      (BitVec.ofFin (w := 4) assignment).getLsbD y.val = false →
      independentInLaw x y (BitVec.ofFin (w := 4) assignment) =
        independent x y (fun z => (BitVec.ofFin (w := 4) assignment).getLsbD z.val) := by
  decide +kernel

/-- All 24 orders participate in the minimization for the Figure 1 oracle. -/
theorem figure_minimum_is_four : optimalCount independent = 4 := by
  decide +kernel

theorem figure_orders_are_minimal :
    ([0, 1, 2, 3] : List (Fin 4)) ∈ sparsestOrders independent ∧
      ([0, 3, 2, 1] : List (Fin 4)) ∈ sparsestOrders independent := by
  decide +kernel

end

end OpenCausalScience.Papers.RaskuttiUhler2018.Figure1
